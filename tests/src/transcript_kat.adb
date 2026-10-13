--  TRANSCRIPT_KAT: known-answer test harness for the Fiat-Shamir
--  transcript (stage 4): Sha256 and Aes256 against the NIST vectors,
--  and Transcript against Appendix B.2 of the draft, byte for byte
--  (ADR 0029, ADR 0032).
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads
--  the vector files given as arguments (default: sha256.txt,
--  aes256.txt and transcript_fs.txt under tests/vectors/) and checks
--  every case against the library. Built with -gnata, so the library's
--  executable contracts run; a contract violation surfaces here as a
--  failure with the offending line. This build is not the constant-
--  time build.
--
--  File format: '#' comments and blank lines are skipped; otherwise
--  one line per step, fields separated by blanks:
--    sha256 <message> <digest>        message as hex bytes, '-' if empty
--    aes256 <key> <block> <expected>  64, 32 and 32 hex digits
--    reset <label>                    a new transcript from the label
--    write_bytes <bytes>              the byte array frame ('-' if empty)
--    write_elt <bytes>                the element frame
--    write_slice <n> <bytes>          the array frame, n elements
--    elt <value>                      one element of the 4-word prime
--                                     field of B.2, drawn as 32 bytes
--                                     little-endian below p; the value
--                                     as the draft prints it, big-endian
--    nat <n> <result>                 Transcript.Nat
--    choose <n> <k> <list>            Transcript.Choose, comma-separated
--  with every byte string written as hex bytes in order. The transcript
--  lines are a chained run: state is carried from line to line, and
--  the three write lines count as setup, not as cases. The sha256 case
--  is checked twice: in one Update, and byte by byte through separate
--  Update calls, so that the block boundary handling is exercised.
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Exceptions;
with Ada.Text_IO;
with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with Sha256;
with Aes256;
with Transcript; use type Transcript.Index_Array;

procedure Transcript_KAT is

   package TIO renames Ada.Text_IO;

   Default_Sha256 : constant String := "tests/vectors/sha256.txt";
   Default_Aes256 : constant String := "tests/vectors/aes256.txt";
   Default_Fs     : constant String := "tests/vectors/transcript_fs.txt";

   --  The prime of Appendix B.2 (2^256 - 2^32 - 977), big-endian.
   B2_P_BE : constant Bytes_32 :=
     [16#FF#, 16#FF#, 16#FF#, 16#FF#, 16#FF#, 16#FF#, 16#FF#, 16#FF#,
      16#FF#, 16#FF#, 16#FF#, 16#FF#, 16#FF#, 16#FF#, 16#FF#, 16#FF#,
      16#FF#, 16#FF#, 16#FF#, 16#FF#, 16#FF#, 16#FF#, 16#FF#, 16#FF#,
      16#FF#, 16#FF#, 16#FF#, 16#FE#, 16#FF#, 16#FF#, 16#FC#, 16#2F#];

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

   --  Hex bytes in order; '-' is the empty array.
   function To_Bytes (S : String) return Byte_Array is
   begin
      if S = "-" then
         return Byte_Array'[];
      end if;
      if S'Length mod 2 /= 0 then
         raise Parse_Error with "odd number of hex digits in '" & S & "'";
      end if;
      declare
         R : Byte_Array (0 .. S'Length / 2 - 1);
      begin
         for I in R'Range loop
            R (I) :=
              Shift_Left (Hex_Digit (S (S'First + 2 * I)), 4)
              or Hex_Digit (S (S'First + 2 * I + 1));
         end loop;
         return R;
      end;
   end To_Bytes;

   function Image (B : Byte_Array) return String is
      Hex : constant String := "0123456789abcdef";
      S   : String (1 .. 2 * B'Length);
   begin
      for I in B'Range loop
         S (2 * (I - B'First) + 1) := Hex (Integer (Shift_Right (B (I), 4)) + 1);
         S (2 * (I - B'First) + 2) := Hex (Integer (B (I) and 15) + 1);
      end loop;
      return S;
   end Image;

   --  Blank-separated fields of a line, as index bounds into it.
   type Field_Bounds is record
      Lo, Hi : Natural;
   end record;
   type Field_Array is array (1 .. 4) of Field_Bounds;

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

   procedure Check_Sha256 (Msg : Byte_Array; Want : Byte_Array) is
      Ctx  : Sha256.Context := Sha256.Initial;
      Ctx1 : Sha256.Context := Sha256.Initial;
   begin
      if Want'Length /= 32 then
         raise Parse_Error with "sha256 digest must be 32 bytes";
      end if;
      Sha256.Update (Ctx, Msg);
      declare
         Got : constant Bytes_32 := Sha256.Digest (Ctx);
      begin
         if Got /= Want then
            Report_Failure
              ("sha256 " & Image (Msg) & " expected " & Image (Want)
               & " got " & Image (Got));
            return;
         end if;
      end;
      --  Byte by byte, and the digest twice: the context must survive.
      for I in Msg'Range loop
         Sha256.Update (Ctx1, Msg (I .. I));
      end loop;
      declare
         Got1 : constant Bytes_32 := Sha256.Digest (Ctx1);
         Got2 : constant Bytes_32 := Sha256.Digest (Ctx1);
      begin
         if Got1 /= Want then
            Report_Failure
              ("sha256 " & Image (Msg) & " byte by byte expected "
               & Image (Want) & " got " & Image (Got1));
         elsif Got2 /= Want then
            Report_Failure
              ("sha256 " & Image (Msg) & " second digest got "
               & Image (Got2));
         else
            Passed := Passed + 1;
         end if;
      end;
   end Check_Sha256;

   procedure Check_Aes256 (Key, Block, Want : Byte_Array) is
   begin
      if Key'Length /= 32 or else Block'Length /= 16
        or else Want'Length /= 16
      then
         raise Parse_Error with "aes256 expects 32, 16 and 16 bytes";
      end if;
      declare
         KS  : constant Aes256.Key_Schedule := Aes256.Expand_Key (Key);
         Got : constant Bytes_16 := Aes256.Encrypt (KS, Block);
      begin
         if Got = Want then
            Passed := Passed + 1;
         else
            Report_Failure
              ("aes256 " & Image (Key) & " " & Image (Block)
               & " expected " & Image (Want) & " got " & Image (Got));
         end if;
      end;
   end Check_Aes256;

   --  Big-endian view of a little-endian byte string.
   function Reversed (B : Byte_Array) return Byte_Array is
      R : Byte_Array (0 .. B'Length - 1);
   begin
      for I in R'Range loop
         R (I) := B (B'Last - I);
      end loop;
      return R;
   end Reversed;

   --  Lexicographic comparison of two big-endian 32-byte values.
   function Less (A, B : Bytes_32) return Boolean is
   begin
      for I in A'Range loop
         if A (I) /= B (I) then
            return A (I) < B (I);
         end if;
      end loop;
      return False;
   end Less;

   --  The sampler of Section 3.4.3 for the 4-word field of B.2, in
   --  the harness because the library has no such field: 32 bytes,
   --  little-endian, rejected at or above p, so that byte consumption
   --  is the draft's.
   procedure Check_Elt (Want : String) is
      B  : Bytes_32;
      BE : Bytes_32;
   begin
      loop
         Transcript.Get_Random_Bytes (B);
         BE := Reversed (B);
         exit when Less (BE, B2_P_BE);
      end loop;
      if Image (BE) = Want then
         Passed := Passed + 1;
      else
         Report_Failure ("elt expected " & Want & " got " & Image (BE));
      end if;
   end Check_Elt;

   procedure Check_Nat (N : Positive; Want : Natural) is
      Got : Natural;
   begin
      Transcript.Nat (N, Got);
      if Got = Want then
         Passed := Passed + 1;
      else
         Report_Failure
           ("nat" & N'Image & " expected" & Want'Image & " got" & Got'Image);
      end if;
   end Check_Nat;

   --  The comma-separated list of K naturals.
   function To_List (S : String; K : Natural) return Transcript.Index_Array
   is
      R     : Transcript.Index_Array (0 .. K - 1);
      Count : Natural := 0;
      I     : Natural := S'First;
      J     : Natural;
   begin
      while I <= S'Last loop
         J := I;
         while J < S'Last and then S (J + 1) /= ',' loop
            J := J + 1;
         end loop;
         if Count = K then
            raise Parse_Error with "more than" & K'Image & " values";
         end if;
         R (Count) := Natural'Value (S (I .. J));
         Count := Count + 1;
         I := J + 2;
      end loop;
      if Count /= K then
         raise Parse_Error with "expected" & K'Image & " values";
      end if;
      return R;
   end To_List;

   procedure Check_Choose (N, K : Natural; Want : Transcript.Index_Array)
   is
      Got : Transcript.Index_Array (0 .. K - 1);
   begin
      Transcript.Choose (N, K, Got);
      if Got = Want then
         Passed := Passed + 1;
      else
         Report_Failure ("choose" & N'Image & K'Image & " differs");
         for I in Got'Range loop
            if Got (I) /= Want (I) then
               TIO.Put_Line
                 ("   position" & I'Image & ": expected" & Want (I)'Image
                  & " got" & Got (I)'Image);
            end if;
         end loop;
      end if;
   end Check_Choose;

   procedure Check_Case (Line : String) is
      Fields : Field_Array;
      Count  : Natural;
   begin
      Split (Line, Fields, Count);
      if Count = 0 then
         return;
      end if;
      declare
         Op : constant String := Line (Fields (1).Lo .. Fields (1).Hi);
      begin
         if Op = "sha256" then
            if Count /= 3 then
               raise Parse_Error with "sha256 expects 2 values";
            end if;
            Check_Sha256
              (To_Bytes (Line (Fields (2).Lo .. Fields (2).Hi)),
               To_Bytes (Line (Fields (3).Lo .. Fields (3).Hi)));
         elsif Op = "aes256" then
            if Count /= 4 then
               raise Parse_Error with "aes256 expects 3 values";
            end if;
            Check_Aes256
              (To_Bytes (Line (Fields (2).Lo .. Fields (2).Hi)),
               To_Bytes (Line (Fields (3).Lo .. Fields (3).Hi)),
               To_Bytes (Line (Fields (4).Lo .. Fields (4).Hi)));
         elsif Op = "reset" then
            if Count /= 2 then
               raise Parse_Error with "reset expects 1 value";
            end if;
            Transcript.Reset
              (To_Bytes (Line (Fields (2).Lo .. Fields (2).Hi)));
         elsif Op = "write_bytes" then
            if Count /= 2 then
               raise Parse_Error with "write_bytes expects 1 value";
            end if;
            Transcript.Write_Bytes
              (To_Bytes (Line (Fields (2).Lo .. Fields (2).Hi)));
         elsif Op = "write_elt" then
            if Count /= 2 then
               raise Parse_Error with "write_elt expects 1 value";
            end if;
            Transcript.Write_Element
              (To_Bytes (Line (Fields (2).Lo .. Fields (2).Hi)));
         elsif Op = "write_slice" then
            if Count /= 3 then
               raise Parse_Error with "write_slice expects 2 values";
            end if;
            Transcript.Write_Slice
              (Natural'Value (Line (Fields (2).Lo .. Fields (2).Hi)),
               To_Bytes (Line (Fields (3).Lo .. Fields (3).Hi)));
         elsif Op = "elt" then
            if Count /= 2 then
               raise Parse_Error with "elt expects 1 value";
            end if;
            Check_Elt (Line (Fields (2).Lo .. Fields (2).Hi));
         elsif Op = "nat" then
            if Count /= 3 then
               raise Parse_Error with "nat expects 2 values";
            end if;
            Check_Nat
              (Positive'Value (Line (Fields (2).Lo .. Fields (2).Hi)),
               Natural'Value (Line (Fields (3).Lo .. Fields (3).Hi)));
         elsif Op = "choose" then
            if Count /= 4 then
               raise Parse_Error with "choose expects 3 values";
            end if;
            declare
               N : constant Natural :=
                 Natural'Value (Line (Fields (2).Lo .. Fields (2).Hi));
               K : constant Natural :=
                 Natural'Value (Line (Fields (3).Lo .. Fields (3).Hi));
            begin
               Check_Choose
                 (N, K, To_List (Line (Fields (4).Lo .. Fields (4).Hi), K));
            end;
         else
            raise Parse_Error with "unknown operation '" & Op & "'";
         end if;
      end;
   exception
      when E : others =>
         --  Parse errors and contract violations (assertion failures
         --  raised inside the library) both count as failures.
         Report_Failure
           (Ada.Exceptions.Exception_Name (E) & ": "
            & Ada.Exceptions.Exception_Message (E));
   end Check_Case;

   procedure Run_File (Path : String) is
      File : TIO.File_Type;
   begin
      TIO.Put_Line ("Transcript known-answer tests: " & Path);
      TIO.Open (File, TIO.In_File, Path);
      Line_No := 0;
      while not TIO.End_Of_File (File) loop
         declare
            Line : constant String := TIO.Get_Line (File);
         begin
            Line_No := Line_No + 1;
            if Line'Length > 0 and then Line (Line'First) /= '#' then
               Check_Case (Line);
            end if;
         end;
      end loop;
      TIO.Close (File);
   end Run_File;

begin
   if Ada.Command_Line.Argument_Count = 0 then
      Run_File (Default_Sha256);
      Run_File (Default_Aes256);
      Run_File (Default_Fs);
   else
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         Run_File (Ada.Command_Line.Argument (I));
      end loop;
   end if;

   TIO.Put_Line
     ("passed" & Passed'Image & ", failed" & Failed'Image);
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end Transcript_KAT;
