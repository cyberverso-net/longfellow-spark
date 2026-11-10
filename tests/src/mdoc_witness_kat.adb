--  MDOC_WITNESS_KAT: known-answer test harness for Mdoc_Witness (block 6
--  of Phase D, ADR 0086): the two witnesses of the mDoc proof built from
--  the parsed credential.
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads the
--  vector file given as argument (default tests/vectors/mdoc_witness.txt)
--  and checks every case against the library. The witness_file cases
--  compare both witnesses, element by element, with the private parts
--  of upstream's witness files under tests/vectors/upstream/mdoc/, built
--  from the test document and the pads mac_ap the files hold; the
--  witness cases digest both witnesses of a test document under fixed
--  pads and compare the digests with the Python transcription's; the
--  reject cases check the statuses and that a refused witness is zero.
--  Built with -gnata, so the library's
--  executable contracts run. Not the constant-time build.
--
--  File format: see gen_mdoc_witness_vectors.py. Unknown operations are
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
with GF2_128;
with P256_Field;
with Sha256;
with Cbor_Parse;
with Mdoc_Parse;
with Mdoc_Mac;
with Mdoc_Inputs;
with Mdoc_Witness;
with Sumcheck_Algebra_GF2_128;
with Sumcheck_Algebra_P256;

procedure MDOC_WITNESS_KAT is

   package TIO renames Ada.Text_IO;
   package SAH renames Sumcheck_Algebra_GF2_128;
   package SAP renames Sumcheck_Algebra_P256;
   use type Mdoc_Parse.Status;
   use type Mdoc_Witness.Status;
   use type GF2_128.Element;
   use type Mdoc_Mac.Messages;

   Default_Path : constant String := "tests/vectors/mdoc_witness.txt";
   Mdoc_Dir     : constant String := "tests/vectors/upstream/mdoc/";
   Cases_Dir    : constant String := Mdoc_Dir & "testcases/";

   Passed  : Natural := 0;
   Failed  : Natural := 0;
   Line_No : Natural := 0;

   Parse_Error : exception;

   type Byte_Array_Access is access Byte_Array;
   procedure Free is new Ada.Unchecked_Deallocation (Byte_Array, Byte_Array_Access);
   type Hash_Access is access SAH.Element_Array;
   procedure Free is new Ada.Unchecked_Deallocation (SAH.Element_Array, Hash_Access);
   type Sig_Access is access SAP.Element_Array;
   procedure Free is new Ada.Unchecked_Deallocation (SAP.Element_Array, Sig_Access);

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

   function Digest_Hex (Ctx : Sha256.Context) return String is
      D : constant Bytes_32 := Sha256.Digest (Ctx);
   begin
      return Hex_Of (D);
   end Digest_Hex;

   --  A natural in decimal without the leading blank of 'Image.
   function Dec (N : Natural) return String is
      S : constant String := N'Image;
   begin
      return S (S'First + 1 .. S'Last);
   end Dec;

   function Lower (S : String) return String is
     (Ada.Characters.Handling.To_Lower (S));

   --  A P-256 coordinate from its hex (0x prefix allowed), as the
   --  request files write them.
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
         raise Parse_Error with "a coordinate is 1 to 64 hex digits: " & S;
      end if;
      for K in 0 .. N - 1 loop
         L := P256_Field.Limb_Index (K / 16);
         R (L) := R (L) or Shift_Left
           (Unsigned_64 (Hex_Digit (S (S'Last - K))), 4 * (K mod 16));
      end loop;
      if not P256_Field.Is_Canonical (R) then
         raise Parse_Error with "a coordinate is below p: " & S;
      end if;
      return P256_Field.From_Canonical (R);
   end Coordinate;

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

   --  The request of a test case: the issuer's key and the document
   --  type.
   type Case_Request is record
      Pk_X, Pk_Y : P256_Field.Element := P256_Field.Zero;
      Doc_Type   : Byte_Array_Access;
   end record;

   function Request_Of (Case_Name : String) return Case_Request is
      F    : TIO.File_Type;
      Text : String (1 .. 1024);
      Last : Natural;
      R    : Case_Request;
   begin
      TIO.Open (F, TIO.In_File, Cases_Dir & Case_Name & "/request.txt");
      while not TIO.End_Of_File (F) loop
         TIO.Get_Line (F, Text, Last);
         if Last >= 9 and then Text (1 .. 9) = "doc_type " then
            R.Doc_Type := new Byte_Array (0 .. Last - 10);
            for I in 10 .. Last loop
               R.Doc_Type (I - 10) := Character'Pos (Text (I));
            end loop;
         elsif Last >= 4 and then Text (1 .. 4) = "pkx " then
            R.Pk_X := Coordinate (Text (5 .. Last));
         elsif Last >= 4 and then Text (1 .. 4) = "pky " then
            R.Pk_Y := Coordinate (Text (5 .. Last));
         end if;
      end loop;
      TIO.Close (F);
      if R.Doc_Type = null then
         raise Parse_Error with Case_Name & ": no doc_type in request.txt";
      end if;
      return R;
   end Request_Of;

   --  The requested attributes from fields "id_hex:value_hex".
   function Attributes_Of (Line : String; Starts, Stops : Field_Array;
                           From, Count : Natural)
                           return Mdoc_Inputs.Attribute_List
   is
      A : Mdoc_Inputs.Attribute_List (1 .. Count);
   begin
      for K in 1 .. Count loop
         declare
            F     : constant String := Line (Starts (From + K - 1) .. Stops (From + K - 1));
            Colon : Natural := 0;
         begin
            for I in F'Range loop
               if F (I) = ':' then
                  Colon := I;
                  exit;
               end if;
            end loop;
            if Colon = 0 then
               raise Parse_Error with "attribute without ':' " & F;
            end if;
            declare
               Id  : Byte_Array_Access := To_Bytes (F (F'First .. Colon - 1));
               Val : Byte_Array_Access := To_Bytes (F (Colon + 1 .. F'Last));
            begin
               A (K).Id_Len := Id'Length;
               A (K).Id (0 .. Id'Length - 1) := Id.all;
               A (K).Value_Len := Val'Length;
               A (K).Value (0 .. Val'Length - 1) := Val.all;
               Free (Id); Free (Val);
            end;
         end;
      end loop;
      return A;
   end Attributes_Of;

   --  The fixed pads of the witness cases: pad H of message I has the
   --  bytes ((16 (2 I + H) + K) 7 + 1) mod 256, K = 0 .. 15, as the
   --  generator defines them.
   function Fixed_Pads return Mdoc_Mac.Pads is
      Ap : Mdoc_Mac.Pads;
      B  : Bytes_16;
      Ok : Boolean;
   begin
      for I in Mdoc_Mac.Message_Index loop
         for H in Mdoc_Mac.Half_Index loop
            for K in 0 .. 15 loop
               B (K) := Unsigned_8 (((16 * (2 * I + H) + K) * 7 + 1) mod 256);
            end loop;
            GF2_128.From_Bytes (B, Ap (I) (H), Ok);
         end loop;
      end loop;
      return Ap;
   end Fixed_Pads;

   --  The digests of the two witnesses: the elements as little-endian
   --  bytes, 16 and 32 each.
   function Hash_Digest (W : SAH.Element_Array) return String is
      Ctx : Sha256.Context := Sha256.Initial;
   begin
      for E of W loop
         Sha256.Update (Ctx, GF2_128.To_Bytes (E));
      end loop;
      return Digest_Hex (Ctx);
   end Hash_Digest;

   function Sig_Digest (W : SAP.Element_Array) return String is
      Ctx : Sha256.Context := Sha256.Initial;
   begin
      for E of W loop
         Sha256.Update (Ctx, P256_Field.To_Bytes (E));
      end loop;
      return Digest_Hex (Ctx);
   end Sig_Digest;

   --  Whether the witness a builder refused is all zero, as the
   --  contracts say: the hash witness on its two refusals, the
   --  signature witness on its one.
   function All_Zero (W : SAH.Element_Array) return Boolean is
     (for all E of W => E = GF2_128.Zero);
   function All_Zero (W : SAP.Element_Array) return Boolean is
     (for all E of W => P256_Field.To_Bytes (E) = Bytes_32'[others => 0]);
   function Refused_Zero
     (R : Mdoc_Witness.Status; WH : SAH.Element_Array; WS : SAP.Element_Array)
      return Boolean
   is (case R is
         when Mdoc_Witness.Ok => True,
         when Mdoc_Witness.Signature_Not_Canonical => All_Zero (WS),
         when others => All_Zero (WH));

   --  Both witnesses of a parsed document; the result of the hash
   --  witness, and the signature witness's when the first is Ok.
   procedure Build
     (Version : Positive; Mdoc : Byte_Array; P : Mdoc_Parse.Parsed_Mdoc;
      Attrs   : Mdoc_Inputs.Attribute_List; Ap : Mdoc_Mac.Pads;
      Pk_X, Pk_Y : P256_Field.Element;
      WH : out Hash_Access; WS : out Sig_Access; R : out Mdoc_Witness.Status)
   is
   begin
      WH := new SAH.Element_Array
        (0 .. Mdoc_Witness.Hash_Count (Version, Attrs'Length) - 1);
      WS := new SAP.Element_Array (0 .. Mdoc_Witness.Sig_Count - 1);
      Mdoc_Witness.Hash_Witness (Version, Mdoc, P, Attrs, Ap, WH.all, R);
      if R = Mdoc_Witness.Ok then
         Mdoc_Witness.Sig_Witness (Mdoc, P, Pk_X, Pk_Y, Ap, WS.all, R);
      end if;
   end Build;

   --  The number of elements of a witness file's private part that
   --  differ from W, and the first such index.
   procedure Compare_Hash
     (File : Byte_Array; Npub : Natural; W : SAH.Element_Array;
      Diffs : out Natural; First_Diff : out Natural)
   is
      E  : GF2_128.Element;
      Ok : Boolean;
   begin
      Diffs := 0;
      First_Diff := 0;
      for I in W'Range loop
         GF2_128.From_Bytes (File (16 * (Npub + I) .. 16 * (Npub + I) + 15), E, Ok);
         if E /= W (I) then
            if Diffs = 0 then
               First_Diff := I;
            end if;
            Diffs := Diffs + 1;
         end if;
      end loop;
   end Compare_Hash;

   procedure Compare_Sig
     (File : Byte_Array; Npub : Natural; W : SAP.Element_Array;
      Diffs : out Natural; First_Diff : out Natural)
   is
   begin
      Diffs := 0;
      First_Diff := 0;
      for I in W'Range loop
         if File (32 * (Npub + I) .. 32 * (Npub + I) + 31) /= P256_Field.To_Bytes (W (I)) then
            if Diffs = 0 then
               First_Diff := I;
            end if;
            Diffs := Diffs + 1;
         end if;
      end loop;
   end Compare_Sig;

   procedure Process_Line (Line : String) is
      Starts, Stops : Field_Array (1 .. 64);
      N : Natural;
      function Fld (I : Positive) return String is (Line (Starts (I) .. Stops (I)));
   begin
      Split (Line, Starts, Stops, N);
      if N = 0 or else Line (Starts (1)) = '#' then
         return;
      end if;
      declare
         Op : constant String := Fld (1);
      begin
         if Op = "witness_file" then
            --  witness_file <case> <archive> <version> <npub_hash>
            --  <npub_sig> <id:value>
            declare
               Version : constant Positive := Positive'Value (Fld (4));
               Req     : Case_Request := Request_Of (Fld (2));
               Mdoc    : Byte_Array_Access := Read_File (Cases_Dir & Fld (2) & "/mdoc.bin");
               Tr      : Byte_Array_Access := Read_File (Cases_Dir & Fld (2) & "/transcript.bin");
               HF      : Byte_Array_Access := Read_File (Mdoc_Dir & Fld (3) & "_hash_witness.bin");
               SF      : Byte_Array_Access := Read_File (Mdoc_Dir & Fld (3) & "_sig_witness.bin");
               Npub_H  : constant Natural := Natural'Value (Fld (5));
               Npub_S  : constant Natural := Natural'Value (Fld (6));
               Attrs   : constant Mdoc_Inputs.Attribute_List :=
                 Attributes_Of (Line, Starts, Stops, 7, 1);
               P       : Mdoc_Parse.Parsed_Mdoc;
               R       : Mdoc_Parse.Status;
               D       : Cbor_Parse.Status;
               Priv    : Hash_Access :=
                 new SAH.Element_Array (0 .. HF'Length / 16 - Npub_H - 1);
               Ap      : Mdoc_Mac.Pads;
               M       : Mdoc_Mac.Messages;
               Ok      : Boolean;
               WH      : Hash_Access;
               WS      : Sig_Access;
               WR      : Mdoc_Witness.Status;
               Diffs, First_Diff : Natural;
            begin
               Mdoc_Parse.Parse (Mdoc.all, Tr.all, Req.Doc_Type.all, Version, P, R, D);
               if R /= Mdoc_Parse.Ok then
                  Report_Failure ("witness_file " & Fld (2) & ": parse " & Lower (R'Image));
                  return;
               end if;
               for I in Priv'Range loop
                  GF2_128.From_Bytes
                    (HF (16 * (Npub_H + I) .. 16 * (Npub_H + I) + 15), Priv (I), Ok);
               end loop;
               Mdoc_Inputs.Witness_Parts (Priv.all, Ap, M, Ok);
               Check (Ok, "witness_file " & Fld (3) & ": Witness_Parts refuses the file");
               Check (Ok and then Mdoc_Witness.Messages (P) = M,
                      "witness_file " & Fld (3) & ": the messages of the parse differ from the file's");
               Check (Priv'Length = Mdoc_Witness.Hash_Count (Version, 1),
                      "witness_file " & Fld (3) & ": the file has " & Dec (Priv'Length)
                      & " private elements, Hash_Count says "
                      & Dec (Mdoc_Witness.Hash_Count (Version, 1)));
               Check (SF'Length / 32 - Npub_S = Mdoc_Witness.Sig_Count,
                      "witness_file " & Fld (3) & ": the signature file has "
                      & Dec (SF'Length / 32 - Npub_S) & " private elements, Sig_Count says "
                      & Dec (Mdoc_Witness.Sig_Count));
               Build (Version, Mdoc.all, P, Attrs, Ap, Req.Pk_X, Req.Pk_Y, WH, WS, WR);
               if WR /= Mdoc_Witness.Ok then
                  Report_Failure ("witness_file " & Fld (3) & ": status " & Lower (WR'Image));
               else
                  Compare_Hash (HF.all, Npub_H, WH.all, Diffs, First_Diff);
                  Check (Diffs = 0, "witness_file " & Fld (3) & ": hash witness: "
                         & Dec (Diffs) & " elements differ, the first at " & Dec (First_Diff));
                  Compare_Sig (SF.all, Npub_S, WS.all, Diffs, First_Diff);
                  Check (Diffs = 0, "witness_file " & Fld (3) & ": signature witness: "
                         & Dec (Diffs) & " elements differ, the first at " & Dec (First_Diff));
               end if;
               Free (WH); Free (WS); Free (Priv);
               Free (Mdoc); Free (Tr); Free (HF); Free (SF); Free (Req.Doc_Type);
            end;
         elsif Op = "witness" or else Op = "witness_reject" then
            --  witness <case> <version> <n> <id:value>... <hash_digest> <sig_digest>
            --  witness_reject <case> <version> <n> <id:value>... <status>
            declare
               Version : constant Positive := Positive'Value (Fld (3));
               Count   : constant Natural := Natural'Value (Fld (4));
               Req     : Case_Request := Request_Of (Fld (2));
               Mdoc    : Byte_Array_Access := Read_File (Cases_Dir & Fld (2) & "/mdoc.bin");
               Tr      : Byte_Array_Access := Read_File (Cases_Dir & Fld (2) & "/transcript.bin");
               Attrs   : constant Mdoc_Inputs.Attribute_List :=
                 Attributes_Of (Line, Starts, Stops, 5, Count);
               P       : Mdoc_Parse.Parsed_Mdoc;
               R       : Mdoc_Parse.Status;
               D       : Cbor_Parse.Status;
               WH      : Hash_Access;
               WS      : Sig_Access;
               WR      : Mdoc_Witness.Status;
            begin
               Mdoc_Parse.Parse (Mdoc.all, Tr.all, Req.Doc_Type.all, Version, P, R, D);
               if R /= Mdoc_Parse.Ok then
                  Report_Failure (Op & " " & Fld (2) & ": parse " & Lower (R'Image));
                  return;
               end if;
               Build (Version, Mdoc.all, P, Attrs, Fixed_Pads, Req.Pk_X, Req.Pk_Y, WH, WS, WR);
               if Op = "witness" then
                  Check (WR = Mdoc_Witness.Ok
                         and then Hash_Digest (WH.all) = Fld (5 + Count)
                         and then Sig_Digest (WS.all) = Fld (6 + Count),
                         "witness " & Fld (2) & " v" & Fld (3) & ": " & Lower (WR'Image)
                         & ", digests " & Hash_Digest (WH.all) & " " & Sig_Digest (WS.all)
                         & ", expected " & Fld (5 + Count) & " " & Fld (6 + Count));
               else
                  Check (Lower (WR'Image) = Fld (5 + Count),
                         "witness_reject " & Fld (2) & ": got " & Lower (WR'Image)
                         & ", expected " & Fld (5 + Count));
                  Check (Refused_Zero (WR, WH.all, WS.all),
                         "witness_reject " & Fld (2) & ": a refused witness is not zero");
               end if;
               Free (WH); Free (WS); Free (Mdoc); Free (Tr); Free (Req.Doc_Type);
            end;
         elsif Op = "witness_hex" or else Op = "reject_hex" then
            --  witness_hex <name> <hex> <version> <n> <id:value>... <hash_digest> <sig_digest>
            --  reject_hex <name> <hex> <version> <n> <id:value>... <status>
            --  A synthetic document, parsed with an empty transcript and
            --  the document type "x", under the key of the archives.
            declare
               Mdoc    : Byte_Array_Access := To_Bytes (Fld (3));
               Version : constant Positive := Positive'Value (Fld (4));
               Count   : constant Natural := Natural'Value (Fld (5));
               Attrs   : constant Mdoc_Inputs.Attribute_List :=
                 Attributes_Of (Line, Starts, Stops, 6, Count);
               Tr      : constant Byte_Array (0 .. -1) := [];
               DT      : constant Byte_Array (0 .. 0) := [Character'Pos ('x')];
               Pk_X    : constant P256_Field.Element := Coordinate
                 ("0xdc1c1f55cff4cd5c76cf4169278f7217667f86ee81d8669b63f2e19bc12a0c9f");
               Pk_Y    : constant P256_Field.Element := Coordinate
                 ("0x12355dd0385fed3bc33bedc9781b9aad47b33e4c24704b8d14288b1b3cb45c28");
               P       : Mdoc_Parse.Parsed_Mdoc;
               R       : Mdoc_Parse.Status;
               D       : Cbor_Parse.Status;
               WH      : Hash_Access;
               WS      : Sig_Access;
               WR      : Mdoc_Witness.Status;
            begin
               Mdoc_Parse.Parse (Mdoc.all, Tr, DT, Version, P, R, D);
               if R /= Mdoc_Parse.Ok then
                  Report_Failure (Op & " " & Fld (2) & ": parse " & Lower (R'Image)
                                  & " " & Lower (D'Image));
                  return;
               end if;
               Build (Version, Mdoc.all, P, Attrs, Fixed_Pads, Pk_X, Pk_Y, WH, WS, WR);
               if Op = "witness_hex" then
                  Check (WR = Mdoc_Witness.Ok
                         and then Hash_Digest (WH.all) = Fld (6 + Count)
                         and then Sig_Digest (WS.all) = Fld (7 + Count),
                         "witness_hex " & Fld (2) & ": " & Lower (WR'Image)
                         & ", digests " & Hash_Digest (WH.all) & " " & Sig_Digest (WS.all)
                         & ", expected " & Fld (6 + Count) & " " & Fld (7 + Count));
               else
                  Check (Lower (WR'Image) = Fld (6 + Count),
                         "reject_hex " & Fld (2) & ": got " & Lower (WR'Image)
                         & ", expected " & Fld (6 + Count));
                  Check (Refused_Zero (WR, WH.all, WS.all),
                         "reject_hex " & Fld (2) & ": a refused witness is not zero");
               end if;
               Free (WH); Free (WS); Free (Mdoc);
            end;
         else
            Report_Failure ("unknown operation " & Op);
         end if;
      end;
   exception
      when E : Parse_Error | Constraint_Error =>
         Report_Failure ("line not understood: "
                         & Ada.Exceptions.Exception_Message (E));
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
   exception
      when TIO.Name_Error =>
         Report_Failure ("cannot open " & Path);
   end Process_File;

   --  The counts of the layout, without a vector file.
   procedure Built_In is
   begin
      Check (Mdoc_Witness.Hash_Count (7, 1) = 84_166,
             "Hash_Count (7, 1) is " & Dec (Mdoc_Witness.Hash_Count (7, 1)));
      Check (Mdoc_Witness.Hash_Count (6, 1) = 74_154,
             "Hash_Count (6, 1) is " & Dec (Mdoc_Witness.Hash_Count (6, 1)));
      Check (Mdoc_Witness.Sig_Count = 2_839,
             "Sig_Count is " & Dec (Mdoc_Witness.Sig_Count));
   end Built_In;

begin
   Built_In;
   if Ada.Command_Line.Argument_Count = 0 then
      TIO.Put_Line ("Mdoc_Witness known-answer tests: " & Default_Path);
      Process_File (Default_Path);
   else
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         TIO.Put_Line ("Mdoc_Witness known-answer tests: " & Ada.Command_Line.Argument (I));
         Process_File (Ada.Command_Line.Argument (I));
      end loop;
   end if;
   TIO.Put_Line ("passed" & Passed'Image & ", failed" & Failed'Image);
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end MDOC_WITNESS_KAT;
