--  MDOC_PARSE_KAT: known-answer test harness for Cbor_Parse, Mdoc_Parse
--  and Sha256.Trace (block 6 of Phase D, ADR 0086).
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads the
--  vector file given as argument (default tests/vectors/mdoc_parse.txt)
--  and checks every case against the library; the parse cases read
--  upstream's test documents under tests/vectors/upstream/mdoc/testcases/,
--  the witness_front cases the hash witness files under
--  tests/vectors/upstream/mdoc/. Built with -gnata, so the library's
--  executable contracts run. Not the constant-time build.
--
--  File format: see gen_mdoc_parse_vectors.py. Unknown operations are
--  failures, so a vector file never passes silently.
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Ada.Characters.Handling;
with Ada.Unchecked_Deallocation;
with Interfaces;   use Interfaces;
with Bytes;        use Bytes;
with Cbor_Parse;
with Mdoc_Parse;
with Sha256;
with Sha256.Trace;

procedure MDOC_PARSE_KAT is

   package TIO renames Ada.Text_IO;
   use type Cbor_Parse.Status;
   use type Mdoc_Parse.Status;

   Default_Path : constant String := "tests/vectors/mdoc_parse.txt";
   Mdoc_Dir     : constant String := "tests/vectors/upstream/mdoc/";
   Cases_Dir    : constant String := Mdoc_Dir & "testcases/";

   Passed  : Natural := 0;
   Failed  : Natural := 0;
   Line_No : Natural := 0;

   Parse_Error : exception;

   type Byte_Array_Access is access Byte_Array;
   procedure Free is new Ada.Unchecked_Deallocation (Byte_Array, Byte_Array_Access);

   function Hex_Digit (C : Character) return Unsigned_8 is
   begin
      case C is
         when '0' .. '9' => return Unsigned_8 (Character'Pos (C) - Character'Pos ('0'));
         when 'a' .. 'f' => return Unsigned_8 (Character'Pos (C) - Character'Pos ('a') + 10);
         when 'A' .. 'F' => return Unsigned_8 (Character'Pos (C) - Character'Pos ('A') + 10);
         when others => raise Parse_Error with "bad hex digit '" & C & "'";
      end case;
   end Hex_Digit;

   --  The bytes of a hex string; "-" is the empty array.
   function To_Bytes (S : String) return Byte_Array_Access is
   begin
      if S = "-" then
         return new Byte_Array (0 .. -1);
      end if;
      if S'Length mod 2 /= 0 then
         raise Parse_Error with "odd hex length";
      end if;
      declare
         R : constant Byte_Array_Access := new Byte_Array (0 .. S'Length / 2 - 1);
      begin
         for I in R'Range loop
            R (I) := Hex_Digit (S (S'First + 2 * I)) * 16
                     + Hex_Digit (S (S'First + 2 * I + 1));
         end loop;
         return R;
      end;
   end To_Bytes;

   function Hex_Of (B : Byte_Array) return String is
      Hex : constant String := "0123456789abcdef";
      S   : String (1 .. 2 * B'Length);
   begin
      for I in B'Range loop
         S (2 * (I - B'First) + 1) := Hex (Integer (B (I) / 16) + 1);
         S (2 * (I - B'First) + 2) := Hex (Integer (B (I) mod 16) + 1);
      end loop;
      return S;
   end Hex_Of;

   function Read_File (Path : String) return Byte_Array_Access is
      use Ada.Streams;
      use Ada.Streams.Stream_IO;
      F    : File_Type;
      Size : constant Natural := Natural (Ada.Directories.Size (Path));
      S    : Stream_Element_Array (1 .. Stream_Element_Offset (Size));
      Last : Stream_Element_Offset;
      R    : constant Byte_Array_Access := new Byte_Array (0 .. Size - 1);
   begin
      Open (F, In_File, Path);
      Read (F, S, Last);
      Close (F);
      for I in S'Range loop
         R (Natural (I - 1)) := Unsigned_8 (S (I));
      end loop;
      return R;
   end Read_File;

   --  The SHA-256 of a string, as hex.
   function Digest_Hex (Ctx : Sha256.Context) return String is
      D : constant Bytes_32 := Sha256.Digest (Ctx);
   begin
      return Hex_Of (D);
   end Digest_Hex;

   procedure Absorb (Ctx : in out Sha256.Context; S : String) is
      B : Byte_Array (0 .. S'Length - 1);
   begin
      for I in S'Range loop
         B (I - S'First) := Unsigned_8 (Character'Pos (S (I)));
      end loop;
      Sha256.Update (Ctx, B);
   end Absorb;

   --  A natural in decimal without the leading blank of 'Image.
   function Dec64 (N : Unsigned_64) return String is
      S : constant String := N'Image;
   begin
      return S (S'First + 1 .. S'Last);
   end Dec64;

   function Dec (N : Natural) return String is (Dec64 (Unsigned_64 (N)));

   function Lower (S : String) return String is
     (Ada.Characters.Handling.To_Lower (S));

   --  The rows of a table as the generator digests them.
   function Table_Digest (Doc : Cbor_Parse.Document) return String is
      Ctx : Sha256.Context := Sha256.Initial;
   begin
      for I in 1 .. Doc.Count loop
         declare
            E : Cbor_Parse.Element renames Doc.Elements (I);
         begin
            Absorb (Ctx, Lower (E.Kind'Image) & " " & Dec (E.Start) & " "
                    & Dec (E.Content) & " " & Dec (E.Stop) & " " & Dec64 (E.Value)
                    & " " & Dec (E.Count) & " " & Dec (E.Parent) & " "
                    & Dec (E.Child) & " " & Dec (E.Next) & ASCII.LF);
         end;
      end loop;
      return Digest_Hex (Ctx);
   end Table_Digest;

   function Item_Row (It : Mdoc_Parse.Item) return String is
     (Dec (It.Name_Start) & " " & Dec (It.Name_Len) & " "
      & Dec (It.Value_Start) & " " & Dec (It.Value_Len) & " "
      & Dec (It.Item_Start) & " " & Dec (It.Item_Len) & " "
      & Dec (It.Slot (0)) & " " & Dec (It.Slot (1)) & " "
      & Dec (It.Slot (2)) & " " & Dec (It.Slot (3)) & " "
      & Dec (It.Length (0)) & " " & Dec (It.Length (1)) & " "
      & Dec (It.Length (2)) & " " & Dec (It.Length (3)) & " "
      & Dec (It.Permutation) & " " & Dec (It.Digest_Offset) & " "
      & Dec64 (It.Digest_Id));

   function Items_Digest (P : Mdoc_Parse.Parsed_Mdoc) return String is
      Ctx : Sha256.Context := Sha256.Initial;
   begin
      for I in 1 .. P.Count loop
         Absorb (Ctx, Item_Row (P.Items (I)) & ASCII.LF);
      end loop;
      return Digest_Hex (Ctx);
   end Items_Digest;

   --  The parse fields as the generator writes them.
   function Parse_Fields (P : Mdoc_Parse.Parsed_Mdoc) return String is
     (Hex_Of (P.Issuer_Sig_Digest) & " " & Hex_Of (P.Device_Pk_X) & " "
      & Hex_Of (P.Device_Pk_Y) & " " & Hex_Of (P.Issuer_Sig_R) & " "
      & Hex_Of (P.Issuer_Sig_S) & " " & Hex_Of (P.Device_Sig_Digest) & " "
      & Hex_Of (P.Device_Sig_R) & " " & Hex_Of (P.Device_Sig_S) & " "
      & Dec (P.Mso_Start) & " " & Dec (P.Mso_Len) & " "
      & Dec (P.Doc_Type_Offset) & " " & Dec (P.Valid_From_Offset) & " "
      & Dec (P.Valid_Until_Offset) & " " & Dec (P.Device_Key_Info_Offset) & " "
      & Dec (P.Value_Digests_Offset) & " " & Dec (P.Count) & " "
      & Items_Digest (P));

   --  Fields of a line, split on blanks.
   type Field_Array is array (Positive range <>) of Natural;

   procedure Split (Line : String; Starts, Stops : out Field_Array; N : out Natural) is
      I : Natural := Line'First;
   begin
      N := 0;
      while I <= Line'Last loop
         while I <= Line'Last and then Line (I) = ' ' loop
            I := I + 1;
         end loop;
         exit when I > Line'Last;
         N := N + 1;
         Starts (N) := I;
         while I <= Line'Last and then Line (I) /= ' ' loop
            I := I + 1;
         end loop;
         Stops (N) := I - 1;
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

   --  The request of a test case: the document type.
   function Doc_Type_Of (Case_Name : String) return Byte_Array_Access is
      F    : TIO.File_Type;
      Text : String (1 .. 1024);
      Last : Natural;
   begin
      TIO.Open (F, TIO.In_File, Cases_Dir & Case_Name & "/request.txt");
      while not TIO.End_Of_File (F) loop
         TIO.Get_Line (F, Text, Last);
         if Last >= 9 and then Text (1 .. 9) = "doc_type " then
            declare
               S : constant String := Text (10 .. Last);
               R : constant Byte_Array_Access := new Byte_Array (0 .. S'Length - 1);
            begin
               for I in S'Range loop
                  R (I - S'First) := Unsigned_8 (Character'Pos (S (I)));
               end loop;
               TIO.Close (F);
               return R;
            end;
         end if;
      end loop;
      TIO.Close (F);
      raise Parse_Error with "no doc_type in " & Case_Name;
   end Doc_Type_Of;

   --  The SHA-256 of Signed_Message equals the digest the parse computed
   --  by streaming, and its length is Message_Length.
   function Message_Agrees (Mdoc : Byte_Array; P : Mdoc_Parse.Parsed_Mdoc)
     return Boolean
   is
      Msg : Byte_Array (0 .. Mdoc_Parse.Max_Message - 1);
      Len : Natural;
      Ctx : Sha256.Context := Sha256.Initial;
   begin
      Mdoc_Parse.Signed_Message (Mdoc, P, Msg, Len);
      Sha256.Update (Ctx, Msg (0 .. Len - 1));
      return Len = Mdoc_Parse.Message_Length (P)
        and then Sha256.Digest (Ctx) = P.Issuer_Sig_Digest;
   end Message_Agrees;

   --  Parse a case at a version; the status and the result.
   procedure Parse_Case
     (Case_Name : String; Version : Positive;
      P : out Mdoc_Parse.Parsed_Mdoc; R : out Mdoc_Parse.Status;
      D : out Cbor_Parse.Status)
   is
      Mdoc : Byte_Array_Access := Read_File (Cases_Dir & Case_Name & "/mdoc.bin");
      Tr   : Byte_Array_Access := Read_File (Cases_Dir & Case_Name & "/transcript.bin");
      DT   : Byte_Array_Access := Doc_Type_Of (Case_Name);
   begin
      Mdoc_Parse.Parse (Mdoc.all, Tr.all, DT.all, Version, P, R, D);
      if R = Mdoc_Parse.Ok then
         Check (Message_Agrees (Mdoc.all, P),
                "parse " & Case_Name & ": Signed_Message disagrees with the digest");
      end if;
      Free (Mdoc); Free (Tr); Free (DT);
   end Parse_Case;

   procedure Process_Line (Line : String) is
      Starts, Stops : Field_Array (1 .. 64);
      N : Natural;
      function Fld (I : Positive) return String is (Line (Starts (I) .. Stops (I)));
      function Rest (From : Positive) return String is (Line (Starts (From) .. Line'Last));
   begin
      Split (Line, Starts, Stops, N);
      if N = 0 or else Line (Starts (1)) = '#' then
         return;
      end if;
      declare
         Op : constant String := Fld (1);
      begin
         if Op = "cbor" then
            declare
               Data : Byte_Array_Access := To_Bytes (Fld (3));
               Doc  : Cbor_Parse.Document;
               R    : Cbor_Parse.Status;
            begin
               Cbor_Parse.Parse_Exact (Data.all, Doc, R);
               Check (R = Cbor_Parse.Ok and then Doc.Count = Natural'Value (Fld (4))
                      and then Table_Digest (Doc) = Fld (5),
                      "cbor " & Fld (2) & ": status " & Lower (R'Image) & ", "
                      & Dec (Doc.Count) & " elements, digest " & Table_Digest (Doc));
               Free (Data);
            end;
         elsif Op = "cbor_reject" then
            declare
               Data : Byte_Array_Access := To_Bytes (Fld (3));
               Doc  : Cbor_Parse.Document;
               R    : Cbor_Parse.Status;
            begin
               Cbor_Parse.Parse_Exact (Data.all, Doc, R);
               Check (Lower (R'Image) = Fld (4),
                      "cbor_reject " & Fld (2) & ": got " & Lower (R'Image)
                      & ", expected " & Fld (4));
               Free (Data);
            end;
         elsif Op = "trace" then
            declare
               Msg    : Byte_Array_Access := To_Bytes (Fld (2));
               Blocks : constant Sha256.Trace.Block_Count := Positive'Value (Fld (3));
               Padded : Byte_Array (0 .. 64 * Blocks - 1);
               NB     : Sha256.Trace.Block_Count;
               H      : Sha256.State := Sha256.Initial_State;
               T      : Sha256.Trace.Block_Trace;
               Ctx    : Sha256.Context := Sha256.Initial;
               Words  : Byte_Array (0 .. 3);
               Plain  : Sha256.Context := Sha256.Initial;
               Last_H : Sha256.State := Sha256.Initial_State;
            begin
               Sha256.Trace.Pad_Message (Msg.all, Blocks, Padded, NB);
               Sha256.Update (Ctx, Padded);
               for B in 0 .. Blocks - 1 loop
                  Sha256.Trace.Compress_Traced (H, Padded, 64 * B, T);
                  for W of T.W loop
                     Words := [Unsigned_8 (Shift_Right (W, 24) and 255), Unsigned_8 (Shift_Right (W, 16) and 255),
                               Unsigned_8 (Shift_Right (W, 8) and 255), Unsigned_8 (W and 255)];
                     Sha256.Update (Ctx, Words);
                  end loop;
                  for W of T.E loop
                     Words := [Unsigned_8 (Shift_Right (W, 24) and 255), Unsigned_8 (Shift_Right (W, 16) and 255),
                               Unsigned_8 (Shift_Right (W, 8) and 255), Unsigned_8 (W and 255)];
                     Sha256.Update (Ctx, Words);
                  end loop;
                  for W of T.A loop
                     Words := [Unsigned_8 (Shift_Right (W, 24) and 255), Unsigned_8 (Shift_Right (W, 16) and 255),
                               Unsigned_8 (Shift_Right (W, 8) and 255), Unsigned_8 (W and 255)];
                     Sha256.Update (Ctx, Words);
                  end loop;
                  for W of H loop
                     Words := [Unsigned_8 (Shift_Right (W, 24) and 255), Unsigned_8 (Shift_Right (W, 16) and 255),
                               Unsigned_8 (Shift_Right (W, 8) and 255), Unsigned_8 (W and 255)];
                     Sha256.Update (Ctx, Words);
                  end loop;
                  if B + 1 = NB then
                     Last_H := H;
                  end if;
               end loop;
               Check (NB = Positive'Value (Fld (4)) and then Digest_Hex (Ctx) = Fld (5),
                      "trace of " & Dec (Msg'Length) & " bytes over " & Fld (3)
                      & " blocks: n_blocks " & Dec (NB) & ", digest " & Digest_Hex (Ctx));
               --  The state after the last used block is the parent's digest.
               Sha256.Update (Plain, Msg.all);
               declare
                  D   : constant Bytes_32 := Sha256.Digest (Plain);
                  Out_B : Bytes_32;
               begin
                  for I in Sha256.Word_Index loop
                     Out_B (4 * Natural (I)) := Unsigned_8 (Shift_Right (Last_H (I), 24) and 255);
                     Out_B (4 * Natural (I) + 1) := Unsigned_8 (Shift_Right (Last_H (I), 16) and 255);
                     Out_B (4 * Natural (I) + 2) := Unsigned_8 (Shift_Right (Last_H (I), 8) and 255);
                     Out_B (4 * Natural (I) + 3) := Unsigned_8 (Last_H (I) and 255);
                  end loop;
                  Check (Out_B = D, "trace: the state after block " & Dec (NB)
                         & " is not Sha256.Digest of the message");
               end;
               Free (Msg);
            end;
         elsif Op = "parse" then
            declare
               P : Mdoc_Parse.Parsed_Mdoc;
               R : Mdoc_Parse.Status;
               D : Cbor_Parse.Status;
            begin
               Parse_Case (Fld (2), Positive'Value (Fld (3)), P, R, D);
               if Fld (4) = "ok" then
                  if R /= Mdoc_Parse.Ok then
                     Report_Failure ("parse " & Fld (2) & " v" & Fld (3) & ": "
                                     & Lower (R'Image) & " " & Lower (D'Image));
                  else
                     Check (Parse_Fields (P) = Rest (5),
                            "parse " & Fld (2) & " v" & Fld (3) & ": fields differ:"
                            & ASCII.LF & "  got  " & Parse_Fields (P)
                            & ASCII.LF & "  want " & Rest (5));
                  end if;
               else
                  Check (Lower (R'Image) = Fld (4),
                         "parse " & Fld (2) & ": got " & Lower (R'Image)
                         & ", expected " & Fld (4));
               end if;
            end;
         elsif Op = "item" then
            declare
               P  : Mdoc_Parse.Parsed_Mdoc;
               R  : Mdoc_Parse.Status;
               D  : Cbor_Parse.Status;
               I  : constant Positive := Positive'Value (Fld (4));
               Id : Byte_Array_Access := To_Bytes (Fld (5));
               Mdoc : Byte_Array_Access := Read_File (Cases_Dir & Fld (2) & "/mdoc.bin");
            begin
               Parse_Case (Fld (2), Positive'Value (Fld (3)), P, R, D);
               Check (R = Mdoc_Parse.Ok and then I <= P.Count
                      and then Item_Row (P.Items (I)) = Rest (6),
                      "item " & Fld (4) & " of " & Fld (2) & ":" & ASCII.LF
                      & "  got  " & (if R = Mdoc_Parse.Ok and then I <= P.Count
                                     then Item_Row (P.Items (I)) else Lower (R'Image))
                      & ASCII.LF & "  want " & Rest (6));
               Check (R = Mdoc_Parse.Ok
                      and then Mdoc_Parse.Find_Item (Mdoc.all, P, Id.all) = I,
                      "item " & Fld (4) & " of " & Fld (2) & ": Find_Item does not return it");
               Free (Id); Free (Mdoc);
            end;
         elsif Op = "find_hex" then
            declare
               Mdoc : Byte_Array_Access := To_Bytes (Fld (3));
               Id   : Byte_Array_Access := To_Bytes (Fld (4));
               Tr   : constant Byte_Array (0 .. -1) := [];
               DT   : constant Byte_Array (0 .. 0) := [Character'Pos ('x')];
               P    : Mdoc_Parse.Parsed_Mdoc;
               R    : Mdoc_Parse.Status;
               D    : Cbor_Parse.Status;
            begin
               Mdoc_Parse.Parse (Mdoc.all, Tr, DT, 7, P, R, D);
               Check (R = Mdoc_Parse.Ok
                      and then Mdoc_Parse.Find_Item (Mdoc.all, P, Id.all)
                               = Natural'Value (Fld (5)),
                      "find_hex " & Fld (2) & ": " & Lower (R'Image) & ", got "
                      & (if R = Mdoc_Parse.Ok
                         then Dec (Mdoc_Parse.Find_Item (Mdoc.all, P, Id.all)) else "-")
                      & ", expected " & Fld (5));
               Free (Mdoc); Free (Id);
            end;
         elsif Op = "parse_hex" or else Op = "parse_reject" then
            declare
               Mdoc : Byte_Array_Access := To_Bytes (Fld (3));
               Tr   : constant Byte_Array (0 .. -1) := [];
               DT   : constant Byte_Array (0 .. 0) := [Character'Pos ('x')];
               P    : Mdoc_Parse.Parsed_Mdoc;
               R    : Mdoc_Parse.Status;
               D    : Cbor_Parse.Status;
            begin
               Mdoc_Parse.Parse (Mdoc.all, Tr, DT, Positive'Value (Fld (4)), P, R, D);
               if Op = "parse_hex" then
                  Check (R = Mdoc_Parse.Ok and then Parse_Fields (P) = Rest (5),
                         "parse_hex " & Fld (2) & ": " & Lower (R'Image) & ASCII.LF
                         & "  got  " & Parse_Fields (P) & ASCII.LF & "  want " & Rest (5));
                  if R = Mdoc_Parse.Ok then
                     Check (Message_Agrees (Mdoc.all, P),
                            "parse_hex " & Fld (2) & ": Signed_Message disagrees with the digest");
                  end if;
               else
                  Check (Lower (R'Image) = Fld (5)
                         and then (N < 6 or else Lower (D'Image) = Fld (6)),
                         "parse_reject " & Fld (2) & ": got " & Lower (R'Image) & " "
                         & Lower (D'Image) & ", expected " & Rest (5));
               end if;
               Free (Mdoc);
            end;
         elsif Op = "witness_front" then
            declare
               P    : Mdoc_Parse.Parsed_Mdoc;
               R    : Mdoc_Parse.Status;
               D    : Cbor_Parse.Status;
               File : Byte_Array_Access := Read_File (Mdoc_Dir & Fld (3) & "_hash_witness.bin");
               Version : constant Positive := Positive'Value (Fld (4));
               Npub : constant Natural := Natural'Value (Fld (5));
               MB   : constant Natural := Mdoc_Parse.Max_Blocks (Version);
               Ok   : Boolean := True;
               First_Bad : Integer := -1;
               --  Element K of the file, a little-endian 16-byte integer: 0 or 1.
               function Bit_Element (K : Natural) return Integer is
                  V : Integer := 0;
               begin
                  for J in 0 .. 15 loop
                     if File (16 * K + J) /= 0 then
                        if J = 0 and then File (16 * K) = 1 then
                           V := 1;
                        else
                           return -1;
                        end if;
                     end if;
                  end loop;
                  return V;
               end Bit_Element;
               procedure Expect (K : Natural; B : Integer) is
               begin
                  if Ok and then Bit_Element (K) /= B then
                     Ok := False;
                     First_Bad := K;
                  end if;
               end Expect;
               procedure Expect_Value (From : Natural; V : Bytes_32) is
               begin
                  --  Bit k of the big-endian value: byte 31 - k / 8, bit k mod 8.
                  for K in 0 .. 255 loop
                     Expect (From + K,
                             Integer (Shift_Right (V (31 - K / 8), K mod 8) and 1));
                  end loop;
               end Expect_Value;
               Pos : Natural;
               NB  : Natural;
            begin
               Parse_Case (Fld (2), Version, P, R, D);
               if R /= Mdoc_Parse.Ok then
                  Report_Failure ("witness_front: parse " & Lower (R'Image));
               else
                  Pos := Npub;
                  Expect_Value (Pos, P.Issuer_Sig_Digest);
                  Expect_Value (Pos + 256, P.Device_Pk_X);
                  Expect_Value (Pos + 512, P.Device_Pk_Y);
                  Pos := Pos + 768;
                  NB := (Mdoc_Parse.Message_Length (P) + 9 + 63) / 64;
                  for K in 0 .. 7 loop
                     Expect (Pos + K, (NB / 2 ** K) mod 2);
                  end loop;
                  Pos := Npub + 768 + 8 + (MB * 64 - 18) * 8 + MB * 1472;
                  declare
                     Offs : constant array (0 .. 3) of Natural :=
                       [P.Valid_From_Offset, P.Valid_Until_Offset,
                        P.Device_Key_Info_Offset, P.Value_Digests_Offset];
                  begin
                     for I in 0 .. 3 loop
                        for K in 0 .. 11 loop
                           Expect (Pos + 12 * I + K, (Offs (I) / 2 ** K) mod 2);
                        end loop;
                     end loop;
                  end;
                  declare
                     A : constant String := Fld (3);
                  begin
                     Check (Ok, "witness_front " & A (A'First .. A'First + 7)
                            & ": first differing element " & Integer'Image (First_Bad));
                  end;
               end if;
               Free (File);
            end;
         else
            Report_Failure ("unknown operation " & Op);
         end if;
      end;
   exception
      when E : others =>
         Report_Failure ("line " & Line_No'Image & ": "
                         & Ada.Exceptions.Exception_Information (E));
   end Process_Line;

   procedure Process_File (Path : String) is
      F : TIO.File_Type;
   begin
      TIO.Open (F, TIO.In_File, Path);
      while not TIO.End_Of_File (F) loop
         declare
            Line : constant String := TIO.Get_Line (F);
         begin
            Line_No := Line_No + 1;
            Process_Line (Line);
         end;
      end loop;
      TIO.Close (F);
   end Process_File;

   --  Without a vector: a document above Cbor_Parse.Max_Bytes is refused
   --  with Document_Too_Long whatever its bytes, and one at the bound is
   --  parsed (and refused on its content, not its size).
   procedure Built_In is
      Big  : Byte_Array_Access := new Byte_Array (0 .. Cbor_Parse.Max_Bytes);
      Edge : Byte_Array_Access := new Byte_Array (0 .. Cbor_Parse.Max_Bytes - 1);
      Tr   : constant Byte_Array (0 .. -1) := [];
      DT   : constant Byte_Array (0 .. 0) := [Character'Pos ('x')];
      P    : Mdoc_Parse.Parsed_Mdoc;
      R    : Mdoc_Parse.Status;
      D    : Cbor_Parse.Status;
   begin
      Big.all := [others => 0];
      Edge.all := [others => 0];
      Mdoc_Parse.Parse (Big.all, Tr, DT, 7, P, R, D);
      Check (R = Mdoc_Parse.Document_Too_Long,
             "a document of Max_Bytes + 1 bytes: " & Lower (R'Image));
      Mdoc_Parse.Parse (Edge.all, Tr, DT, 7, P, R, D);
      Check (R = Mdoc_Parse.Cbor_Root and then D = Cbor_Parse.Trailing_Bytes,
             "a document of Max_Bytes zero bytes: " & Lower (R'Image) & " " & Lower (D'Image));
      Free (Big); Free (Edge);
   end Built_In;

begin
   Built_In;
   if Ada.Command_Line.Argument_Count = 0 then
      TIO.Put_Line ("Cbor_Parse, Mdoc_Parse and Sha256.Trace known-answer tests: " & Default_Path);
      Process_File (Default_Path);
   else
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         TIO.Put_Line ("Cbor_Parse, Mdoc_Parse and Sha256.Trace known-answer tests: "
                       & Ada.Command_Line.Argument (I));
         Process_File (Ada.Command_Line.Argument (I));
      end loop;
   end if;
   TIO.Put_Line ("passed" & Passed'Image & ", failed" & Failed'Image);
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end MDOC_PARSE_KAT;
