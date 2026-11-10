--  MDOC_KAT: the known-answer harness of the mDoc layer (Phase D, block
--  5, ADR 0058): the CBOR heads, the legacy tags, the device
--  authentication digest, the public inputs of both circuits, the ends
--  of the hash circuit's witness and the table of specifications,
--  against tests/vectors/mdoc_layer.txt, written by
--  gen_mdoc_layer_vectors.py from an independent Python transcription
--  of upstream's builders and from upstream's witness files. The real
--  cases of the file are the public parts of those files: the layer
--  must rebuild them byte for byte from the parameters of the test
--  case they come from. A few checks need no vector and are built in:
--  the refusals (an attribute that does not fit, a witness without
--  the layout, an unknown specification) and the round trip of the
--  tags through the proof's front.
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads
--  the vector files given as arguments (default: mdoc_layer.txt under
--  tests/vectors/). Built with -gnata, so the library's executable
--  contracts run.
--
--  File format: see gen_mdoc_layer_vectors.py.
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with Mdoc_Status;
with GF2_128;
with P256_Field;
with Sha256;
with Ligero_Geometry;
with Cbor_Encode;
with Mdoc_Mac;
with Mdoc_Proof;
with Device_Auth;
with Mdoc_Inputs;
with Mdoc_Spec;
with Mdoc_Parse;
with Cbor_Parse;
with Prover_Status;
with Circuit_Status;
with Circuit_Reader_GF2_128;
with Circuit_Reader_P256;
with Mdoc_Prover_Lib;

procedure Mdoc_KAT is

   package TIO renames Ada.Text_IO;

   use type GF2_128.Element;
   use type Ligero_Geometry.Config;
   use type Mdoc_Spec.Spec_Index;
   use type Mdoc_Mac.Pads;

   Default_File : constant String := "tests/vectors/mdoc_layer.txt";

   Passed  : Natural := 0;
   Failed  : Natural := 0;
   Line_No : Natural := 0;

   Parse_Error : exception;

   function Hex_Digit (C : Character) return Unsigned_8 is
   begin
      case C is
         when '0' .. '9' =>
            return Unsigned_8 (Character'Pos (C) - Character'Pos ('0'));
         when 'a' .. 'f' =>
            return Unsigned_8 (Character'Pos (C) - Character'Pos ('a') + 10);
         when 'A' .. 'F' =>
            return Unsigned_8 (Character'Pos (C) - Character'Pos ('A') + 10);
         when others =>
            raise Parse_Error with "bad hex digit '" & C & "'";
      end case;
   end Hex_Digit;

   type Byte_Array_Access is access Byte_Array;
   procedure Free is
     new Ada.Unchecked_Deallocation (Byte_Array, Byte_Array_Access);

   --  hex, or "-" for the empty string.
   function To_Bytes (S : String) return Byte_Array_Access is
      R : Byte_Array_Access;
   begin
      if S = "-" then
         return new Byte_Array (0 .. -1);
      end if;
      if S'Length mod 2 /= 0 then
         raise Parse_Error with "odd number of hex digits";
      end if;
      R := new Byte_Array (0 .. S'Length / 2 - 1);
      for I in R'Range loop
         R (I) := Shift_Left (Hex_Digit (S (S'First + 2 * I)), 4)
                  or Hex_Digit (S (S'First + 2 * I + 1));
      end loop;
      return R;
   end To_Bytes;

   function Hex_Of (B : Byte_Array) return String is
      Digits_Of : constant String := "0123456789abcdef";
      R : String (1 .. 2 * B'Length);
   begin
      for I in B'Range loop
         R (2 * (I - B'First) + 1) :=
           Digits_Of (Natural (Shift_Right (B (I), 4)) + 1);
         R (2 * (I - B'First) + 2) := Digits_Of (Natural (B (I) and 15) + 1);
      end loop;
      return R;
   end Hex_Of;

   function Read_File (Path : String) return Byte_Array_Access is
      use Ada.Streams;
      use Ada.Streams.Stream_IO;
      F    : File_Type;
      Size : constant Natural := Natural (Ada.Directories.Size (Path));
      S    : Stream_Element_Array (1 .. Stream_Element_Offset (Size));
      Last : Stream_Element_Offset;
      R    : Byte_Array_Access;
   begin
      Open (F, In_File, Path);
      Read (F, S, Last);
      Close (F);
      if Natural (Last) /= Size then
         raise Parse_Error with "short read of " & Path;
      end if;
      R := new Byte_Array (0 .. Size - 1);
      for I in S'Range loop
         R (Natural (I) - 1) := Unsigned_8 (S (I));
      end loop;
      return R;
   end Read_File;

   --  A GF(2^128) element from its 16 little-endian bytes.
   function GF_Of (S : String) return GF2_128.Element is
      B  : Byte_Array_Access := To_Bytes (S);
      E  : GF2_128.Element;
      Ok : Boolean;
   begin
      if B'Length /= 16 then
         raise Parse_Error with "a GF(2^128) element is 32 hex digits";
      end if;
      GF2_128.From_Bytes (B.all, E, Ok);
      Free (B);
      return E;
   end GF_Of;

   --  A P-256 element from its 32 canonical little-endian bytes.
   function P_Of (S : String) return P256_Field.Element is
      B  : Byte_Array_Access := To_Bytes (S);
      E  : P256_Field.Element;
      Ok : Boolean;
   begin
      if B'Length /= 32 then
         raise Parse_Error with "a P-256 element is 64 hex digits";
      end if;
      P256_Field.From_Bytes (B.all, E, Ok);
      Free (B);
      if not Ok then
         raise Parse_Error with "a P-256 element is below p";
      end if;
      return E;
   end P_Of;

   Max_Fields : constant := 32;
   type Field_Bounds is record
      Lo, Hi : Natural;
   end record;
   type Field_Array is array (1 .. Max_Fields) of Field_Bounds;

   procedure Split
     (Line : String; Fields : out Field_Array; Count : out Natural)
   is
      I : Natural := Line'First;
      J : Natural;
   begin
      Count  := 0;
      Fields := [others => (0, 0)];
      while I <= Line'Last loop
         if Line (I) = ' ' then
            I := I + 1;
         else
            J := I;
            while J < Line'Last and then Line (J + 1) /= ' ' loop
               J := J + 1;
            end loop;
            if Count = Fields'Length then
               raise Parse_Error with "too many fields";
            end if;
            Count := Count + 1;
            Fields (Count) := (I, J);
            I := J + 1;
         end if;
      end loop;
   end Split;

   procedure Report_Failure (Msg : String) is
   begin
      Failed := Failed + 1;
      TIO.Put_Line ("FAIL line" & Line_No'Image & ": " & Msg);
   end Report_Failure;

   procedure Check (Ok : Boolean; Msg : String) is
   begin
      if Ok then
         Passed := Passed + 1;
      else
         Report_Failure (Msg);
      end if;
   end Check;

   --  The SHA-256 of the serialised elements of each array.
   function Digest_Of (Pub : Mdoc_Inputs.SAH.Element_Array) return String is
      Ctx : Sha256.Context := Sha256.Initial;
   begin
      for I in Pub'Range loop
         Sha256.Update (Ctx, GF2_128.To_Bytes (Pub (I)));
      end loop;
      return Hex_Of (Sha256.Digest (Ctx));
   end Digest_Of;

   function Digest_Of (Pub : Mdoc_Inputs.SAP.Element_Array) return String is
      Ctx : Sha256.Context := Sha256.Initial;
   begin
      for I in Pub'Range loop
         Sha256.Update (Ctx, P256_Field.To_Bytes (Pub (I)));
      end loop;
      return Hex_Of (Sha256.Digest (Ctx));
   end Digest_Of;

   --  Six tags from six fields.
   function Tags_Of (Line : String; F : Field_Array; From : Positive)
                     return Mdoc_Mac.Tags
   is
      T : Mdoc_Mac.Tags;
   begin
      for I in Mdoc_Mac.Tag_Index loop
         T (I) := GF_Of (Line (F (From + I).Lo .. F (From + I).Hi));
      end loop;
      return T;
   end Tags_Of;

   function Pads_Of (Line : String; F : Field_Array; From : Positive)
                     return Mdoc_Mac.Pads
   is
      P : Mdoc_Mac.Pads;
   begin
      for I in Mdoc_Mac.Message_Index loop
         for H in Mdoc_Mac.Half_Index loop
            P (I) (H) := GF_Of (Line (F (From + 2 * I + H).Lo
                                      .. F (From + 2 * I + H).Hi));
         end loop;
      end loop;
      return P;
   end Pads_Of;

   function Messages_Of (Line : String; F : Field_Array; From : Positive)
                         return Mdoc_Mac.Messages
   is
      M : Mdoc_Mac.Messages;
   begin
      for I in Mdoc_Mac.Message_Index loop
         declare
            B : Byte_Array_Access :=
              To_Bytes (Line (F (From + I).Lo .. F (From + I).Hi));
         begin
            if B'Length /= 32 then
               raise Parse_Error with "a message is 64 hex digits";
            end if;
            M (I) := B.all;
            Free (B);
         end;
      end loop;
      return M;
   end Messages_Of;

   function Attribute_Of (Id, Value : Byte_Array) return Mdoc_Inputs.Attribute
   is
      A : Mdoc_Inputs.Attribute;
   begin
      if Id'Length > Mdoc_Inputs.Max_Id_Len
        or else Value'Length > Mdoc_Inputs.Max_Value_Len
      then
         raise Parse_Error with "an attribute piece is too long";
      end if;
      A.Id := [others => 0];
      A.Id (0 .. Id'Length - 1) := Id;
      A.Id_Len := Id'Length;
      A.Value := [others => 0];
      A.Value (0 .. Value'Length - 1) := Value;
      A.Value_Len := Value'Length;
      return A;
   end Attribute_Of;

   procedure Process_Line (Line : String) is
      F     : Field_Array;
      Count : Natural;

      function Fld (I : Positive) return String is
        (Line (F (I).Lo .. F (I).Hi));

      function Need (N : Natural) return Boolean is
      begin
         if Count < N then
            Report_Failure ("expected at least" & N'Image & " fields");
            return False;
         end if;
         return True;
      end Need;
   begin
      Split (Line, F, Count);
      if Count = 0 or else Line (F (1).Lo) = '#' then
         return;
      end if;
      declare
         Kind : constant String := Fld (1);
         Name : constant String := (if Count >= 2 then Fld (2) else "");
      begin
         if Kind = "head" then
            if not Need (5) then
               return;
            end if;
            declare
               Major    : constant Unsigned_8 :=
                 Hex_Digit (Fld (3) (Fld (3)'First)) * 16
                 + Hex_Digit (Fld (3) (Fld (3)'First + 1));
               N        : constant Natural := Natural'Value (Fld (4));
               Expected : Byte_Array_Access := To_Bytes (Fld (5));
               Got      : constant Byte_Array := Cbor_Encode.Head (Major, N);
            begin
               Check (Got = Expected.all
                      and then Cbor_Encode.Head_Len (N) = Got'Length,
                      Name & ": head " & Hex_Of (Got) & " expected "
                      & Hex_Of (Expected.all));
               Free (Expected);
            end;
         elsif Kind = "mac" then
            if not Need (2 + 1 + 6 + 3 + 6) then
               return;
            end if;
            declare
               Av  : constant GF2_128.Element := GF_Of (Fld (3));
               Ap  : constant Mdoc_Mac.Pads := Pads_Of (Line, F, 4);
               M   : constant Mdoc_Mac.Messages := Messages_Of (Line, F, 10);
               Exp : constant Mdoc_Mac.Tags := Tags_Of (Line, F, 13);
               Got : constant Mdoc_Mac.Tags :=
                 Mdoc_Mac.Legacy_Tags (Av, Ap, M);
               Ok  : Boolean := True;
            begin
               for I in Mdoc_Mac.Tag_Index loop
                  Ok := Ok and then Got (I) = Exp (I);
               end loop;
               Check (Ok, Name & ": tags differ");
            end;
         elsif Kind = "e2" then
            if not Need (5) then
               return;
            end if;
            declare
               Tr  : Byte_Array_Access := To_Bytes (Fld (3));
               Doc : Byte_Array_Access := To_Bytes (Fld (4));
               Exp : Byte_Array_Access := To_Bytes (Fld (5));
               Got : constant Bytes_32 := Device_Auth.Digest (Tr.all, Doc.all);
            begin
               Check (Got = Exp.all, Name & ": e2 " & Hex_Of (Got)
                      & " expected " & Hex_Of (Exp.all));
               Free (Tr);
               Free (Doc);
               Free (Exp);
            end;
         elsif Kind = "hash_inputs" then
            if not Need (4) then
               return;
            end if;
            declare
               Version : constant Mdoc_Inputs.Version_Number :=
                 Mdoc_Inputs.Version_Number'Value (Fld (3));
               N       : constant Natural := Natural'Value (Fld (4));
               Attrs   : Mdoc_Inputs.Attribute_List (1 .. N);
               Base    : constant Positive := 5 + 2 * N;
            begin
               if not Need (Base + 1 + 6 + 1 + 1 + 1 - 1) then
                  return;
               end if;
               for K in 1 .. N loop
                  declare
                     Id  : Byte_Array_Access :=
                       To_Bytes (Fld (5 + 2 * (K - 1)));
                     Val : Byte_Array_Access :=
                       To_Bytes (Fld (6 + 2 * (K - 1)));
                  begin
                     Attrs (K) := Attribute_Of (Id.all, Val.all);
                     Free (Id);
                     Free (Val);
                  end;
               end loop;
               declare
                  Now   : Byte_Array_Access := To_Bytes (Fld (Base));
                  T     : constant Mdoc_Mac.Tags :=
                    Tags_Of (Line, F, Base + 1);
                  Av    : constant GF2_128.Element := GF_Of (Fld (Base + 7));
                  Cnt   : constant Natural := Natural'Value (Fld (Base + 8));
                  Exp   : constant String := Fld (Base + 9);
                  Count_Ok : constant Boolean :=
                    Mdoc_Inputs.Hash_Count (Version, N) = Cnt;
               begin
                  Check (Count_Ok, Name & ": count"
                         & Mdoc_Inputs.Hash_Count (Version, N)'Image
                         & " expected" & Cnt'Image);
                  if Count_Ok
                    and then Mdoc_Inputs.All_Fit (Version, Attrs)
                    and then Now'Length <= Mdoc_Inputs.Now_Len
                  then
                     declare
                        Pub : Mdoc_Inputs.SAH.Element_Array (0 .. Cnt - 1);
                     begin
                        Mdoc_Inputs.Hash_Inputs
                          (Version, Attrs, Now.all, T, Av, Pub);
                        Check (Digest_Of (Pub) = Exp,
                               Name & ": the hash public inputs differ");
                     end;
                  else
                     Report_Failure
                       (Name & ": the case does not fit the layout");
                  end if;
                  Free (Now);
               end;
            end;
         elsif Kind = "sig_inputs" then
            if not Need (2 + 3 + 6 + 1 + 1) then
               return;
            end if;
            declare
               Pk_X : constant P256_Field.Element := P_Of (Fld (3));
               Pk_Y : constant P256_Field.Element := P_Of (Fld (4));
               E2   : constant P256_Field.Element := P_Of (Fld (5));
               T    : constant Mdoc_Mac.Tags := Tags_Of (Line, F, 6);
               Av   : constant GF2_128.Element := GF_Of (Fld (12));
               Pub  : Mdoc_Inputs.SAP.Element_Array
                 (0 .. Mdoc_Inputs.Sig_Count - 1);
            begin
               Mdoc_Inputs.Sig_Inputs (Pk_X, Pk_Y, E2, T, Av, Pub);
               Check (Digest_Of (Pub) = Fld (13),
                      Name & ": the signature public inputs differ");
            end;
         elsif Kind = "witness" then
            if not Need (2 + 3 + 6 + 3) then
               return;
            end if;
            declare
               File : Byte_Array_Access := Read_File (Fld (3));
               SigF : Byte_Array_Access := Read_File (Fld (4));
               Npub : constant Natural := Natural'Value (Fld (5));
               Exp_Ap : constant Mdoc_Mac.Pads := Pads_Of (Line, F, 6);
               Exp_M  : constant Mdoc_Mac.Messages :=
                 Messages_Of (Line, F, 12);
               Total  : constant Natural := File'Length / 16;
               Priv   : Mdoc_Inputs.SAH.Element_Array (0 .. Total - Npub - 1);
               Ok     : Boolean;
               Ap     : Mdoc_Mac.Pads;
               M      : Mdoc_Mac.Messages;
               Same   : Boolean := True;
            begin
               for I in Priv'Range loop
                  GF2_128.From_Bytes
                    (File (16 * (Npub + I) .. 16 * (Npub + I) + 15),
                     Priv (I), Ok);
               end loop;
               Mdoc_Inputs.Witness_Parts (Priv, Ap, M, Ok);
               for I in Mdoc_Mac.Message_Index loop
                  Same := Same and then M (I) = Exp_M (I);
                  for H in Mdoc_Mac.Half_Index loop
                     Same := Same and then Ap (I) (H) = Exp_Ap (I) (H);
                  end loop;
               end loop;
               Check (Ok and then Same, Name & ": the witness ends differ");
               --  The same pads at the end of the signature witness, read
               --  as P-256 elements from its private part (900 public).
               declare
                  NS   : constant Natural := SigF'Length / 32 - 900;
                  SPrv : Mdoc_Inputs.SAP.Element_Array (0 .. NS - 1);
                  Fresh : Mdoc_Mac.Pads;
                  Ap2  : Mdoc_Mac.Pads;
                  M2   : Mdoc_Mac.Messages;
               begin
                  for I in SPrv'Range loop
                     P256_Field.From_Bytes
                       (SigF (32 * (900 + I) .. 32 * (900 + I) + 31),
                        SPrv (I), Ok);
                  end loop;
                  Check (Mdoc_Inputs.Sig_Pads_Match (SPrv, Exp_Ap),
                         Name & ": the pads at the end of the sig witness");
                  --  Fresh pads placed in both witnesses are read back.
                  for I in Mdoc_Mac.Message_Index loop
                     for H in Mdoc_Mac.Half_Index loop
                        Fresh (I) (H) :=
                          (Limbs => [0 => 16#0123_4567_89AB_CDEF#
                                          xor Unsigned_64 (2 * I + H),
                                     1 => 16#FEDC_BA98_7654_3210#
                                          xor Unsigned_64 (7 * I + 3 * H)]);
                     end loop;
                  end loop;
                  Mdoc_Inputs.Place_Pads (Priv, SPrv, Fresh);
                  Mdoc_Inputs.Witness_Parts (Priv, Ap2, M2, Ok);
                  Check (Ok and then Ap2 = Fresh
                         and then (for all I in Mdoc_Mac.Message_Index =>
                                     M2 (I) = Exp_M (I))
                         and then Mdoc_Inputs.Sig_Pads_Match (SPrv, Fresh)
                         and then not Mdoc_Inputs.Sig_Pads_Match
                                        (SPrv, Exp_Ap),
                         Name & ": fresh pads placed and read back");
               end;
               Free (File);
               Free (SigF);
            end;
         elsif Kind = "spec" then
            if not Need (1 + 2 + 3 + 6) then
               return;
            end if;
            declare
               I        : constant Mdoc_Spec.Spec_Index :=
                 Mdoc_Spec.Spec_Index'Value (Fld (2));
               S        : constant Mdoc_Spec.Specification :=
                 Mdoc_Spec.Spec (I);
               Combined : Byte_Array_Access := To_Bytes (Fld (5));
               Sig_Id   : Byte_Array_Access := To_Bytes (Fld (6));
               Hash_Id  : Byte_Array_Access := To_Bytes (Fld (7));
               Hash_Cfg : constant Ligero_Geometry.Config :=
                 (Rate_Inv    => Natural'Value (Fld (8)),
                  Num_Queries => Natural'Value (Fld (9)),
                  Encoded_Len => Natural'Value (Fld (10)));
               Sig_Cfg  : constant Ligero_Geometry.Config :=
                 (Rate_Inv    => Natural'Value (Fld (11)),
                  Num_Queries => Natural'Value (Fld (12)),
                  Encoded_Len => Natural'Value (Fld (13)));
               Found : Boolean;
               J     : Mdoc_Spec.Spec_Index;
            begin
               Check (Natural (S.Version) = Natural'Value (Fld (3))
                      and then S.Num_Attributes = Natural'Value (Fld (4))
                      and then S.Combined = Combined.all
                      and then S.Sig_Id = Sig_Id.all
                      and then S.Hash_Id = Hash_Id.all
                      and then S.Hash_Cfg = Hash_Cfg
                      and then S.Sig_Cfg = Sig_Cfg,
                      "spec" & I'Image & ": the row differs from upstream's");
               Mdoc_Spec.Lookup (Combined.all, Found, J);
               Check (Found and then J = I,
                      "spec" & I'Image & ": not found by its combined id");
               Check (Mdoc_Spec.Combined_Of (Sig_Id.all, Hash_Id.all)
                      = Combined.all,
                      "spec" & I'Image & ": the combined identifier is not"
                      & " SHA-256 (sig || hash)");
               Free (Combined);
               Free (Sig_Id);
               Free (Hash_Id);
            end;
         else
            Report_Failure ("unknown case kind " & Kind);
         end if;
      end;
   exception
      when E : Parse_Error =>
         Report_Failure
           ("parse error: " & Ada.Exceptions.Exception_Message (E));
   end Process_Line;

   procedure Process_File (Path : String) is
      File : TIO.File_Type;
   begin
      TIO.Open (File, TIO.In_File, Path);
      Line_No := 0;
      while not TIO.End_Of_File (File) loop
         declare
            Line : constant String := TIO.Get_Line (File);
         begin
            Line_No := Line_No + 1;
            Process_Line (Line);
         end;
      end loop;
      TIO.Close (File);
   end Process_File;

   --  The checks that need no vector.
   procedure Built_In is
      Z : constant Byte_Array (0 .. 95) := [others => 16#61#];
   begin
      Line_No := 0;
      --  The layouts' limits.
      Check (Mdoc_Inputs.Fits (7, Attribute_Of (Z (0 .. 29), Z (0 .. 63)))
             and then not Mdoc_Inputs.Fits
                              (7, Attribute_Of (Z (0 .. 30), Z (0 .. 63)))
             and then not Mdoc_Inputs.Fits
                              (7, Attribute_Of (Z (0 .. 29), Z (0 .. 64))),
             "built-in: the limits of the version 7 layout");
      Check (Mdoc_Inputs.Fits (6, Attribute_Of (Z (0 .. 10), Z (0 .. 70)))
             and then not Mdoc_Inputs.Fits
                              (6, Attribute_Of (Z (0 .. 10), Z (0 .. 71))),
             "built-in: the limits of the version 6 layout");
      Check (Mdoc_Inputs.Hash_Count (7, 1) = 952
             and then Mdoc_Inputs.Hash_Count (6, 1) = 944,
             "built-in: the counts of the archives held");
      Check (Cbor_Encode.Head_Len (23) = 1
             and then Cbor_Encode.Head_Len (24) = 2
             and then Cbor_Encode.Head_Len (255) = 2
             and then Cbor_Encode.Head_Len (256) = 3
             and then Cbor_Encode.Head_Len (65535) = 3
             and then Cbor_Encode.Head_Len (65536) = 5,
             "built-in: the lengths of the CBOR heads");
      --  A witness without the layout.
      declare
         Short : constant Mdoc_Inputs.SAH.Element_Array (0 .. 9) :=
           [others => GF2_128.Zero];
         Bits  : Mdoc_Inputs.SAH.Element_Array (0 .. 773) :=
           [others => GF2_128.One];
         Ap    : Mdoc_Mac.Pads;
         M     : Mdoc_Mac.Messages;
         Ok    : Boolean;
      begin
         Mdoc_Inputs.Witness_Parts (Short, Ap, M, Ok);
         Check (not Ok, "built-in: a short witness is refused");
         Bits (Bits'Last) := (Limbs => [0 => 5, 1 => 7]);
         Mdoc_Inputs.Witness_Parts (Bits, Ap, M, Ok);
         Check (Ok and then Ap (2) (1) = Bits (Bits'Last)
                and then (for all I in Mdoc_Mac.Message_Index =>
                            (for all J in 0 .. 31 => M (I) (J) = 16#FF#)),
                "built-in: the ends of a witness of ones");
         Bits (0) := (Limbs => [0 => 2, 1 => 0]);
         Mdoc_Inputs.Witness_Parts (Bits, Ap, M, Ok);
         Check (not Ok,
                "built-in: a message element that is no bit is refused");
      end;
      --  The tags through the front of the proof.
      declare
         T   : Mdoc_Mac.Tags;
         B   : Byte_Array (0 .. Mdoc_Proof.Tags_Len - 1);
         Got : Mdoc_Mac.Tags;
         Ok  : Boolean := True;
      begin
         for I in Mdoc_Mac.Tag_Index loop
            T (I) :=
              (Limbs => [0 => Unsigned_64 (I) * 16#0101_0101_0101_0101#,
                         1 => 16#8000_0000_0000_0000# + Unsigned_64 (I)]);
         end loop;
         Mdoc_Proof.Write_Tags (T, B);
         Got := Mdoc_Proof.Read_Tags (B);
         for I in Mdoc_Mac.Tag_Index loop
            Ok := Ok and then Got (I) = T (I);
         end loop;
         Check (Ok and then B (0) = 0 and then B (16) = 1
                and then B (31) = 16#80#,
                "built-in: the tags written and read back");
      end;
      --  An unknown specification.
      declare
         Found : Boolean;
         I     : Mdoc_Spec.Spec_Index;
      begin
         Mdoc_Spec.Lookup ([others => 16#AB#], Found, I);
         Check (not Found, "built-in: an unknown combined identifier");
      end;
      --  The supported profile (ADR 0089): each row accepted with its
      --  own circuits and one attribute; refused under an unknown name,
      --  with the other row's hash circuit, with the signature
      --  circuit's identifier altered, and with zero and two to four
      --  attributes.
      declare
         use type Mdoc_Status.Status;
         I   : Mdoc_Spec.Spec_Index;
         St  : Mdoc_Status.Status;
         Bad : Bytes_32;
      begin
         for R in Mdoc_Spec.Spec_Index loop
            declare
               S     : constant Mdoc_Spec.Specification := Mdoc_Spec.Spec (R);
               Other : constant Mdoc_Spec.Specification :=
                 Mdoc_Spec.Spec (if R = 1 then 2 else 1);
            begin
               Mdoc_Spec.Select_Profile (S.Combined, S.Hash_Id, S.Sig_Id, 1, I, St);
               Check (St = Mdoc_Status.Ok and then I = R,
                      "profile: row" & R'Image & " refused: " & St'Image);
               Mdoc_Spec.Select_Profile ([others => 16#AB#], S.Hash_Id, S.Sig_Id, 1, I, St);
               Check (St = Mdoc_Status.Profile_Unknown,
                      "profile: an unknown name gives " & St'Image);
               Mdoc_Spec.Select_Profile (S.Combined, Other.Hash_Id, S.Sig_Id, 1, I, St);
               Check (St = Mdoc_Status.Profile_Mismatch,
                      "profile: the other row's hash circuit gives " & St'Image);
               Bad := S.Sig_Id;
               Bad (0) := Bad (0) xor 1;
               Mdoc_Spec.Select_Profile (S.Combined, S.Hash_Id, Bad, 1, I, St);
               Check (St = Mdoc_Status.Profile_Mismatch,
                      "profile: an altered signature circuit gives " & St'Image);
               for N in 0 .. 4 loop
                  if N /= 1 then
                     Mdoc_Spec.Select_Profile (S.Combined, S.Hash_Id, S.Sig_Id, N, I, St);
                     Check (St = Mdoc_Status.Attribute_Count,
                            "profile:" & N'Image & " attributes give " & St'Image);
                  end if;
               end loop;
            end;
         end loop;
      end;
   end Built_In;

   --  The prover's entry point refuses buffers that are not the row's
   --  (ADR 0089): on the version 7 circuits, each of the three buffers
   --  one element short, and the proof buffer not starting at zero;
   --  each refusal is Profile_Mismatch with Len zero, the details Ok and
   --  every buffer zero. The circuits are read pinned to the row's
   --  identifiers, as the command line reads them.
   procedure Profile_Buffers is
      use type Mdoc_Status.Status;
      use type Prover_Status.Status;
      use type Mdoc_Parse.Status;
      use type GF2_128.Element;
      use type Circuit_Status.Status;
      package MP renames Mdoc_Prover_Lib;
      S   : constant Mdoc_Spec.Specification := Mdoc_Spec.Spec (1);
      Dir : constant String := "tests/vectors/upstream/mdoc/";
      Hex : constant String := "8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121";
      HB  : Byte_Array_Access := Read_File (Dir & Hex & "_hash.lfc2");
      SB  : Byte_Array_Access := Read_File (Dir & Hex & "_sig.lfc2");
      Doc : Byte_Array_Access :=
        Read_File (Dir & "testcases/FAMILYNAME_MUSTERMANN_MDOC_3/mdoc.bin");
      HC  : Circuit_Reader_GF2_128.Packed_Access;
      HH  : Circuit_Reader_GF2_128.Header;
      HS  : Circuit_Status.Status;
      SC  : Circuit_Reader_P256.Packed_Access;
      SH  : Circuit_Reader_P256.Header;
      SS  : Circuit_Status.Status;
      A   : Mdoc_Inputs.Attribute_List (1 .. 1);
      Ap  : constant Mdoc_Mac.Pads := [others => [others => GF2_128.Zero]];
      Now : constant Byte_Array := [for C of String'("2024-10-01T09:00:00Z") => Character'Pos (C)];
      DT  : constant Byte_Array := [for C of String'("org.iso.18013.5.1.mDL") => Character'Pos (C)];
      Fn  : constant Byte_Array := [for C of String'("family_name") => Character'Pos (C)];
      Val : constant Byte_Array := [16#6a#, 16#4d#, 16#75#, 16#73#, 16#74#, 16#65#, 16#72#, 16#6d#, 16#61#, 16#6e#, 16#6e#];
      Tr  : constant Byte_Array (0 .. -1) := [];
   begin
      Circuit_Reader_GF2_128.Read_Packed (HB.all, True, S.Hash_Id, HC, HH, HS);
      Circuit_Reader_P256.Read_Packed (SB.all, True, S.Sig_Id, SC, SH, SS);
      if HS /= Circuit_Status.Ok or else SS /= Circuit_Status.Ok then
         Report_Failure ("profile buffers: the version 7 circuits did not load");
         return;
      end if;
      A (1).Id (0 .. Fn'Length - 1) := Fn;
      A (1).Id_Len := Fn'Length;
      A (1).Value (0 .. Val'Length - 1) := Val;
      A (1).Value_Len := Val'Length;
      declare
         HI  : constant MP.Circuit_Info :=
           (Id => HH.Id, Sfb => HH.Subfield_Boundary, Cfg => S.Hash_Cfg);
         SI  : constant MP.Circuit_Info :=
           (Id => SH.Id, Sfb => SH.Subfield_Boundary, Cfg => S.Sig_Cfg);
         Max : constant Positive := MP.Max_Len (HC.all, HI, SC.all, SI);
         NH  : constant Positive := 84_166;
         NS  : constant Positive := 2_839;

         procedure Try (Name : String; Lh, Ls, Fb, Lb : Natural) is
            type HA is access MP.Hash_Elements;
            type SA is access MP.Sig_Elements;
            type BA is access Byte_Array;
            WH  : constant HA := new MP.Hash_Elements (0 .. Lh - 1);
            WS  : constant SA := new MP.Sig_Elements (0 .. Ls - 1);
            B   : constant BA := new Byte_Array (Fb .. Fb + Lb - 1);
            Len : Natural;
            St  : Mdoc_Status.Status;
            D   : Prover_Status.Status;
            PS  : Mdoc_Parse.Status;
            CS  : Cbor_Parse.Status;
         begin
            MP.Prove_Profile (S.Combined, HC.all, HH.Id, HH.Subfield_Boundary,
                              SC.all, SH.Id, SH.Subfield_Boundary, Doc.all, Ap,
                              P256_Field.Zero, P256_Field.Zero, Tr, A, Now, DT,
                              WH.all, WS.all, B.all, Len, St, D, PS, CS);
            Check (St = Mdoc_Status.Profile_Mismatch and then Len = 0
                   and then D = Prover_Status.Ok and then PS = Mdoc_Parse.Ok
                   and then (for all E of WH.all => E = GF2_128.Zero)
                   and then (for all E of WS.all =>
                               P256_Field.To_Bytes (E) = Bytes_32'[others => 0])
                   and then (for all X of B.all => X = 0),
                   "profile buffers, " & Name & ": " & St'Image);
         end Try;
      begin
         Try ("hash witness one short", NH - 1, NS, 0, Max);
         Try ("signature witness one short", NH, NS - 1, 0, Max);
         Try ("proof buffer one short", NH, NS, 0, Max - 1);
         Try ("proof buffer from 1", NH, NS, 1, Max);
      end;
      Circuit_Reader_GF2_128.Free_Packed (HC);
      Circuit_Reader_P256.Free_Packed (SC);
      Free (HB); Free (SB); Free (Doc);
   end Profile_Buffers;

begin
   if Ada.Command_Line.Argument_Count = 0 then
      Process_File (Default_File);
   else
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         Process_File (Ada.Command_Line.Argument (I));
      end loop;
   end if;
   Built_In;
   Profile_Buffers;
   TIO.Put_Line ("mdoc_kat:" & Passed'Image & " passed," & Failed'Image
                 & " failed");
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (1);
   end if;
end Mdoc_KAT;
