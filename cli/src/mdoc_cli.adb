pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Directories;
with Ada.IO_Exceptions;
with Ada.Characters.Handling;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Circuit_Status;
with Device_Auth;
with Sumcheck_Algebra_GF2_128;
with Sumcheck_Algebra_P256;
with Packed_Circuits_GF2_128;
with Packed_Circuits_P256;
with Pinned_Circuits;

package body Mdoc_Cli is

   package TIO renames Ada.Text_IO;
   package CL renames Ada.Command_Line;

   use type Ada.Directories.File_Size;

   Default_Dir : constant String := "tests/vectors/upstream/mdoc";

   Prove_Usage : constant String :=
     "usage: longfellow_prove_mdoc --spec HEX"
     & " (--mdoc FILE | --hash-witness FILE --sig-witness FILE)"
     & " --pkx HEX --pky HEX"
     & " (--transcript HEX | --transcript-file FILE) --now STRING"
     & " --doc-type STRING --attr ID:CBORHEX [--attr ...] --out FILE"
     & " [--circuits DIR] [--seed N] [--check-circuit-id]";

   Verify_Usage : constant String :=
     "usage: longfellow_verify_mdoc --spec HEX --proof FILE --pkx HEX"
     & " --pky HEX (--transcript HEX | --transcript-file FILE) --now STRING"
     & " --doc-type STRING --attr ID:CBORHEX [--attr ...]"
     & " [--circuits DIR] [--check-circuit-id]";

   procedure Free_Bytes is
     new Ada.Unchecked_Deallocation (Byte_Array, Byte_Array_Access);

   procedure Free (B : in out Byte_Array_Access) is
   begin
      Free_Bytes (B);
   end Free;

   function Read_File (Path : String) return Byte_Array_Access is
      use Ada.Streams;
      use Ada.Streams.Stream_IO;
      use type Ada.Directories.File_Kind;
      F     : File_Type;
      Bytes : Ada.Directories.File_Size;
      Size  : Natural;
      R     : Byte_Array_Access;
   begin
      if not Ada.Directories.Exists (Path)
        or else Ada.Directories.Kind (Path) /= Ada.Directories.Ordinary_File
      then
         raise Usage_Error with "no such file: " & Path;
      end if;
      --  The size is read once, in the file system's own type, checked
      --  against the bound, and that same value sizes the allocation.
      Bytes := Ada.Directories.Size (Path);
      if Bytes > Max_File_Bytes then
         raise Usage_Error with "file larger than" & Max_File_Bytes'Image
           & " bytes: " & Path;
      end if;
      Size := Natural (Bytes);
      --  The file goes to the heap through a chunk buffer of 64 kB: no
      --  array of the file's size on the stack.
      R := new Byte_Array (0 .. Size - 1);
      declare
         Chunk : Stream_Element_Array (1 .. 65_536);
         Last  : Stream_Element_Offset;
         Pos   : Natural := 0;
      begin
         Open (F, In_File, Path);
         while Pos < Size loop
            Read (F, Chunk, Last);
            exit when Last < Chunk'First;
            if Pos + Natural (Last) > Size then
               Close (F);
               Free (R);
               raise Usage_Error with "file grew while read: " & Path;
            end if;
            for I in Chunk'First .. Last loop
               R (Pos + Natural (I - Chunk'First)) := Unsigned_8 (Chunk (I));
            end loop;
            Pos := Pos + Natural (Last);
         end loop;
         Close (F);
         if Pos /= Size then
            Free (R);
            raise Usage_Error with "short read of " & Path;
         end if;
      exception
         when Ada.IO_Exceptions.Name_Error | Ada.IO_Exceptions.Use_Error
            | Ada.IO_Exceptions.Device_Error | Ada.IO_Exceptions.Status_Error
            | Ada.IO_Exceptions.End_Error =>
            if Is_Open (F) then
               Close (F);
            end if;
            Free (R);
            raise Usage_Error with "cannot read " & Path;
      end;
      return R;
   exception
      when Ada.IO_Exceptions.Name_Error | Ada.IO_Exceptions.Use_Error =>
         raise Usage_Error with "cannot read " & Path;
   end Read_File;

   procedure Write_File (Path : String; B : Byte_Array) is
      use Ada.Streams;
      use Ada.Streams.Stream_IO;
      F : File_Type;
      S : Stream_Element_Array (1 .. Stream_Element_Offset (B'Length));
   begin
      for I in B'Range loop
         S (Stream_Element_Offset (I - B'First + 1)) := Stream_Element (B (I));
      end loop;
      Create (F, Out_File, Path);
      Write (F, S);
      Close (F);
   exception
      when others =>
         raise Usage_Error with "cannot write " & Path;
   end Write_File;

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
            raise Usage_Error with "bad hex digit '" & C & "'";
      end case;
   end Hex_Digit;

   function Hex_Bytes (S : String) return Byte_Array is
      R : Byte_Array (0 .. S'Length / 2 - 1);
   begin
      if S'Length mod 2 /= 0 then
         raise Usage_Error with "odd number of hex digits: " & S;
      end if;
      for I in R'Range loop
         R (I) := Shift_Left (Hex_Digit (S (S'First + 2 * I)), 4)
                  or Hex_Digit (S (S'First + 2 * I + 1));
      end loop;
      return R;
   end Hex_Bytes;

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

   function To_Bytes (S : String) return Byte_Array is
      R : Byte_Array (0 .. S'Length - 1);
   begin
      for I in R'Range loop
         R (I) := Character'Pos (S (S'First + I));
      end loop;
      return R;
   end To_Bytes;

   function Lower (S : String) return String
     renames Ada.Characters.Handling.To_Lower;

   function Coordinate (S : String) return P256_Field.Element is
      Start : Natural := S'First;
      R     : P256_Field.Limb_Array := [others => 0];
      L     : P256_Field.Limb_Index;
      N     : Natural;
   begin
      if S'Length >= 2 and then S (S'First) = '0'
        and then (S (S'First + 1) = 'x' or else S (S'First + 1) = 'X')
      then
         Start := S'First + 2;
      end if;
      N := S'Last - Start + 1;
      if N = 0 or else N > 64 then
         raise Usage_Error with "a coordinate is 1 to 64 hex digits: " & S;
      end if;
      --  Digit K from the end fills nibble K of the integer: the limb
      --  K / 16, shifted by 4 (K mod 16).
      for K in 0 .. N - 1 loop
         L := P256_Field.Limb_Index (K / 16);
         R (L) := R (L) or Shift_Left
           (Unsigned_64 (Hex_Digit (S (S'Last - K))), 4 * (K mod 16));
      end loop;
      if not P256_Field.Is_Canonical (R) then
         raise Usage_Error with "a coordinate is below p: " & S;
      end if;
      return P256_Field.From_Canonical (R);
   end Coordinate;

   --  ID:CBORHEX.
   function Attribute_Of (S : String) return Mdoc_Inputs.Attribute is
      Colon : Natural := 0;
      A     : Mdoc_Inputs.Attribute;
   begin
      for I in S'Range loop
         if S (I) = ':' then
            Colon := I;
            exit;
         end if;
      end loop;
      if Colon = 0 then
         raise Usage_Error with "an attribute is ID:CBORHEX: " & S;
      end if;
      declare
         Id    : constant Byte_Array := To_Bytes (S (S'First .. Colon - 1));
         Value : constant Byte_Array := Hex_Bytes (S (Colon + 1 .. S'Last));
      begin
         if Id'Length = 0 or else Id'Length > Mdoc_Inputs.Max_Id_Len then
            raise Usage_Error with "an attribute identifier is 1 to"
              & Mdoc_Inputs.Max_Id_Len'Image & " bytes: " & S;
         end if;
         if Value'Length = 0 or else Value'Length > Mdoc_Inputs.Max_Value_Len
         then
            raise Usage_Error with "an attribute value is 1 to"
              & Mdoc_Inputs.Max_Value_Len'Image & " bytes: " & S;
         end if;
         A.Id := [others => 0];
         A.Id (0 .. Id'Length - 1) := Id;
         A.Id_Len := Id'Length;
         A.Value := [others => 0];
         A.Value (0 .. Value'Length - 1) := Value;
         A.Value_Len := Value'Length;
      end;
      return A;
   end Attribute_Of;

   procedure Parse_Arguments (R : out Request; Prover : Boolean) is
      I         : Positive := 1;
      Spec_Arg  : String_Access;
      Pkx_Arg   : String_Access;
      Pky_Arg   : String_Access;
      Usage     : constant String :=
        (if Prover then Prove_Usage else Verify_Usage);

      function Value return String is
      begin
         if I + 1 > CL.Argument_Count then
            raise Usage_Error with CL.Argument (I) & " needs a value";
         end if;
         I := I + 2;
         return CL.Argument (I - 1);
      end Value;
   begin
      R := (others => <>);
      R.Dir := new String'(Default_Dir);
      while I <= CL.Argument_Count loop
         declare
            Opt : constant String := CL.Argument (I);
         begin
            if Opt = "--spec" then
               Spec_Arg := new String'(Value);
            elsif Opt = "--circuits" then
               R.Dir := new String'(Value);
            elsif Opt = "--pkx" then
               Pkx_Arg := new String'(Value);
            elsif Opt = "--pky" then
               Pky_Arg := new String'(Value);
            elsif Opt = "--transcript" then
               R.Session := new Byte_Array'(Hex_Bytes (Value));
            elsif Opt = "--transcript-file" then
               R.Session := Read_File (Value);
            elsif Opt = "--now" then
               R.Now := new Byte_Array'(To_Bytes (Value));
            elsif Opt = "--doc-type" then
               R.Doc_Type := new Byte_Array'(To_Bytes (Value));
            elsif Opt = "--attr" then
               if R.Nattrs = Mdoc_Inputs.Max_Attributes then
                  raise Usage_Error with "at most"
                    & Mdoc_Inputs.Max_Attributes'Image & " attributes";
               end if;
               R.Nattrs := R.Nattrs + 1;
               R.Attrs (R.Nattrs) := Attribute_Of (Value);
            elsif Opt = "--check-circuit-id" then
               R.Full_Id := True;
               I := I + 1;
            elsif Prover and then Opt = "--mdoc" then
               R.Mdoc_Path := new String'(Value);
            elsif Prover and then Opt = "--hash-witness" then
               R.Hash_Witness := new String'(Value);
            elsif Prover and then Opt = "--sig-witness" then
               R.Sig_Witness := new String'(Value);
            elsif Prover and then Opt = "--out" then
               R.Out_Path := new String'(Value);
            elsif Prover and then Opt = "--seed" then
               declare
                  S : constant String := Value;
               begin
                  R.Seed   := Unsigned_64'Value (S);
                  R.Seeded := True;
               exception
                  when others =>
                     raise Usage_Error with "not a seed: " & S;
               end;
            elsif not Prover and then Opt = "--proof" then
               R.Proof_Path := new String'(Value);
            elsif Opt = "--help" or else Opt = "-h" then
               TIO.Put_Line (Usage);
               CL.Set_Exit_Status (0);
               raise Usage_Error with "";
            else
               raise Usage_Error with "unknown option " & Opt;
            end if;
         end;
      end loop;
      if Spec_Arg = null or else Pkx_Arg = null or else Pky_Arg = null
        or else R.Session = null or else R.Now = null or else R.Doc_Type = null
        or else R.Nattrs = 0
        or else (Prover and then R.Out_Path = null)
        or else (Prover and then R.Mdoc_Path = null
                 and then (R.Hash_Witness = null or else R.Sig_Witness = null))
        or else (not Prover and then R.Proof_Path = null)
      then
         raise Usage_Error with "missing argument";
      end if;
      if Prover and then R.Mdoc_Path /= null
        and then (R.Hash_Witness /= null or else R.Sig_Witness /= null)
      then
         raise Usage_Error with "--mdoc excludes the witness files";
      end if;
      declare
         Combined : constant Byte_Array := Hex_Bytes (Spec_Arg.all);
         Found    : Boolean;
      begin
         if Combined'Length /= 32 then
            raise Usage_Error with "a specification is 64 hex digits";
         end if;
         Mdoc_Spec.Lookup (Combined, Found, R.Spec);
         if not Found then
            raise Refused with "spec_unknown";
         end if;
      end;
      R.Pk_X := Coordinate (Pkx_Arg.all);
      R.Pk_Y := Coordinate (Pky_Arg.all);
      --  The preconditions of the library on the request, checked here:
      --  the library units run without run-time checks (ADR 0068).
      if R.Now'Length > Mdoc_Inputs.Now_Len then
         raise Usage_Error with "the date is at most"
           & Mdoc_Inputs.Now_Len'Image & " bytes";
      end if;
      if R.Doc_Type'Length > Device_Auth.Max_Doc_Type then
         raise Usage_Error with "the document type is at most"
           & Device_Auth.Max_Doc_Type'Image & " bytes";
      end if;
      if R.Session'Length > Device_Auth.Max_Session_Transcript then
         raise Refused with "transcript_too_long";
      end if;
   end Parse_Arguments;

   procedure Load_Circuits
     (R      : Request;
      Hash_C : out Circuit_Reader_GF2_128.Packed_Access;
      Hash_H : out Circuit_Reader_GF2_128.Header;
      Sig_C  : out Circuit_Reader_P256.Packed_Access;
      Sig_H  : out Circuit_Reader_P256.Header)
   is
      use type Circuit_Status.Status;
      package CRH renames Circuit_Reader_GF2_128;
      package CRS renames Circuit_Reader_P256;
      package PCH renames Packed_Circuits_GF2_128;
      package PCS renames Packed_Circuits_P256;
      procedure Read_Hash is new Pinned_Circuits.Read_Packed (CRH);
      procedure Read_Sig is new Pinned_Circuits.Read_Packed (CRS);
      S    : constant Mdoc_Spec.Specification := Mdoc_Spec.Spec (R.Spec);
      Base : constant String := R.Dir.all & "/" & Hex_Of (S.Combined);
      St   : Circuit_Status.Status;
   begin
      declare
         B : Byte_Array_Access := Read_File (Base & "_hash.lfc2");
      begin
         Read_Hash (B.all, R.Full_Id, Hash_C, Hash_H, St);
         Free (B);
      end;
      if St /= Circuit_Status.Ok then
         raise Refused with "hash circuit " & Lower (St'Image);
      end if;
      --  The executable part of what the library asks of a circuit,
      --  checked once where it enters the program (ADR 0072).
      if not (PCH.Indices_Ok (Hash_C.all)
              and then PCH.Layers_Ok (Hash_C.all)
              and then Sumcheck_Algebra_GF2_128.Shape_Ok
                         (PCH.Shape_Of (Hash_C.all)))
      then
         CRH.Free_Packed (Hash_C);
         raise Refused with "hash circuit not_well_formed";
      end if;
      declare
         B : Byte_Array_Access := Read_File (Base & "_sig.lfc2");
      begin
         Read_Sig (B.all, R.Full_Id, Sig_C, Sig_H, St);
         Free (B);
      end;
      if St /= Circuit_Status.Ok then
         CRH.Free_Packed (Hash_C);
         raise Refused with "sig circuit " & Lower (St'Image);
      end if;
      if not (PCS.Indices_Ok (Sig_C.all)
              and then PCS.Layers_Ok (Sig_C.all)
              and then Sumcheck_Algebra_P256.Shape_Ok
                         (PCS.Shape_Of (Sig_C.all)))
      then
         CRH.Free_Packed (Hash_C);
         CRS.Free_Packed (Sig_C);
         raise Refused with "sig circuit not_well_formed";
      end if;
      --  The identifiers are the row's and combine to the archive's.
      if Hash_H.Id /= S.Hash_Id or else Sig_H.Id /= S.Sig_Id
        or else Mdoc_Spec.Combined_Of (Sig_H.Id, Hash_H.Id) /= S.Combined
      then
         CRH.Free_Packed (Hash_C);
         CRS.Free_Packed (Sig_C);
         raise Refused with "combined_hash";
      end if;
   end Load_Circuits;

end Mdoc_Cli;
