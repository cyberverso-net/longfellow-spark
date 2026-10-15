--  LIGERO_KAT: known-answer test harness for stage 5. At block 2 it
--  covers the Merkle tree (ADR 0040, tier 1 from Appendix B.1.1, tier 2
--  from the generator's independent reference, negative cases); the
--  geometry, Lagrange and Ligero cases come with the later blocks.
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads
--  the vector files given as arguments (default: merkle.txt under
--  tests/vectors/) and checks every case against the library. Built
--  with -gnata, so the library's executable contracts run; a contract
--  violation surfaces here as a failure with the offending line.
--
--  File format: '#' comments and blank lines are skipped; otherwise
--  one case per line, fields separated by blanks, digests as 64 hex
--  digits in memory order:
--    build <n> <n leaves> <root>
--        Merkle.Build of the leaves has this root
--    verify <n> <root> <k> <k indices> <k leaves> <m> <m path> <ok>
--        Merkle.Verify succeeds (ok = 1) or fails (ok = 0)
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Exceptions;
with Ada.Text_IO;
with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with Merkle;     use Merkle;

procedure Ligero_KAT is

   package TIO renames Ada.Text_IO;

   Default_Merkle : constant String := "tests/vectors/merkle.txt";

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

   function To_Digest (S : String) return Digest is
      R : Digest;
   begin
      if S'Length /= 64 then
         raise Parse_Error with "expected 64 hex digits, got '" & S & "'";
      end if;
      for I in R'Range loop
         R (I) :=
           Shift_Left (Hex_Digit (S (S'First + 2 * I)), 4)
           or Hex_Digit (S (S'First + 2 * I + 1));
      end loop;
      return R;
   end To_Digest;

   function Image (D : Digest) return String is
      Hex : constant String := "0123456789abcdef";
      S   : String (1 .. 64);
   begin
      for I in D'Range loop
         S (2 * I + 1) := Hex (Integer (Shift_Right (D (I), 4)) + 1);
         S (2 * I + 2) := Hex (Integer (D (I) and 15) + 1);
      end loop;
      return S;
   end Image;

   --  Blank-separated fields of a line, as index bounds into it.
   Max_Fields : constant := 4096;
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

   procedure Check_Case (Line : String) is
      Fields : Field_Array;
      Count  : Natural;

      function F (K : Positive) return String is
      begin
         if K > Count then
            raise Parse_Error with "missing field" & K'Image;
         end if;
         return Line (Fields (K).Lo .. Fields (K).Hi);
      end F;

      function Nat (K : Positive) return Natural is
      begin
         return Natural'Value (F (K));
      end Nat;
   begin
      Split (Line, Fields, Count);
      if Count = 0 then
         return;
      end if;
      declare
         Op : constant String := F (1);
      begin
         if Op = "build" then
            declare
               N      : constant Natural := Nat (2);
               Leaves : Digest_Array (0 .. N - 1);
               Heap   : Digest_Array (0 .. 2 * N - 1);
               Want   : Digest;
            begin
               if N = 0 or else Count /= N + 3 then
                  raise Parse_Error with "build expects n, n leaves, root";
               end if;
               for I in 0 .. N - 1 loop
                  Leaves (I) := To_Digest (F (3 + I));
               end loop;
               Want := To_Digest (F (N + 3));
               Build (Leaves, Heap);
               if Heap (1) = Want then
                  Passed := Passed + 1;
               else
                  Report_Failure
                    ("build" & N'Image & " expected root " & Image (Want)
                     & " got " & Image (Heap (1)));
               end if;
            end;
         elsif Op = "verify" then
            declare
               N    : constant Natural := Nat (2);
               Root : constant Digest  := To_Digest (F (3));
               K    : constant Natural := Nat (4);
               Idx  : Index_Array (0 .. K - 1);
               Lvs  : Digest_Array (0 .. K - 1);
               M    : Natural;
               Pos  : Natural := 5;
               Ok   : Boolean;
               Want : Boolean;
            begin
               for I in 0 .. K - 1 loop
                  Idx (I) := Nat (Pos + I);
               end loop;
               Pos := Pos + K;
               for I in 0 .. K - 1 loop
                  Lvs (I) := To_Digest (F (Pos + I));
               end loop;
               Pos := Pos + K;
               M := Nat (Pos);
               Pos := Pos + 1;
               declare
                  Path : Digest_Array (0 .. M - 1);
               begin
                  for I in 0 .. M - 1 loop
                     Path (I) := To_Digest (F (Pos + I));
                  end loop;
                  Pos := Pos + M;
                  if Count /= Pos then
                     raise Parse_Error with "verify: field count";
                  end if;
                  Want := Nat (Pos) = 1;
                  Verify (N, Root, Idx, Lvs, Path, Ok);
                  if Ok = Want then
                     Passed := Passed + 1;
                  else
                     Report_Failure
                       ("verify" & N'Image & " k" & K'Image & " expected "
                        & Want'Image & " got " & Ok'Image);
                  end if;
               end;
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
      TIO.Put_Line ("Ligero known-answer tests: " & Path);
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
      Run_File (Default_Merkle);
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
end Ligero_KAT;
