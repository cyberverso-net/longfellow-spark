--  GF2_128_KAT: known-answer test harness for GF2_128.
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads the
--  vector files given as arguments (default: gf2_128_mul.txt,
--  gf2_128_square.txt, gf2_128_inv.txt and gf2_128_bytes.txt under
--  tests/vectors/) and checks every case against the library.
--  Built with -gnata, so the library's executable contracts run; a
--  contract violation surfaces here as a failure with the offending
--  line. The Post of Mul against Mul_Ref is proof-only (ADR 0044) and
--  does not run: what this harness checks of Mul is its result. This
--  build is not the constant-time build.
--
--  File format: '#' comments and blank lines are skipped; otherwise
--  one case per line, fields separated by blanks:
--    mul <a> <b> <expected>
--    square <a> <expected>
--    inv <a> <expected>        (also checks a * Inv (a) = One for a /= 0)
--    bytes <a> <encoding>      To_Bytes (a) = encoding, From_Bytes back
--  with each element written as 32 big-endian hex digits of the 128-bit
--  integer whose bit i is the coefficient of x^i (the first 16 digits
--  are Limbs (1), the last 16 are Limbs (0)), and the encoding as the
--  16 bytes in memory order (Section 7.2.1, little-endian).
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Exceptions;
with Ada.Text_IO;
with Interfaces; use Interfaces;
with Bytes;      use type Bytes.Byte_Array;
with GF2_128;    use GF2_128;

procedure GF2_128_KAT is

   package TIO renames Ada.Text_IO;

   Default_Mul    : constant String := "tests/vectors/gf2_128_mul.txt";
   Default_Square : constant String := "tests/vectors/gf2_128_square.txt";
   Default_Inv    : constant String := "tests/vectors/gf2_128_inv.txt";
   Default_Bytes  : constant String := "tests/vectors/gf2_128_bytes.txt";

   Passed  : Natural := 0;
   Failed  : Natural := 0;
   Line_No : Natural := 0;

   Parse_Error : exception;

   function Hex_Digit (C : Character) return Unsigned_64 is
   begin
      case C is
         when '0' .. '9' =>
            return Unsigned_64 (Character'Pos (C) - Character'Pos ('0'));
         when 'a' .. 'f' =>
            return Unsigned_64 (Character'Pos (C) - Character'Pos ('a') + 10);
         when 'A' .. 'F' =>
            return Unsigned_64 (Character'Pos (C) - Character'Pos ('A') + 10);
         when others =>
            raise Parse_Error with "bad hex digit '" & C & "'";
      end case;
   end Hex_Digit;

   --  32 big-endian hex digits; the first 16 form Limbs (1).
   function To_Element (S : String) return Element is
      R : Element := Zero;
      L : Limb_Index;
   begin
      if S'Length /= 32 then
         raise Parse_Error with "expected 32 hex digits, got '" & S & "'";
      end if;
      for I in 0 .. 31 loop
         L := (if I < 16 then 1 else 0);
         R.Limbs (L) :=
           Shift_Left (R.Limbs (L), 4) or Hex_Digit (S (S'First + I));
      end loop;
      return R;
   end To_Element;

   --  16 bytes as 32 hex digits in memory order.
   function To_Bytes_16 (S : String) return Bytes_16 is
      R : Bytes_16;
   begin
      if S'Length /= 32 then
         raise Parse_Error with "expected 32 hex digits, got '" & S & "'";
      end if;
      for I in R'Range loop
         R (I) :=
           Unsigned_8
             (Shift_Left (Hex_Digit (S (S'First + 2 * I)), 4)
              or Hex_Digit (S (S'First + 2 * I + 1)));
      end loop;
      return R;
   end To_Bytes_16;

   function Image (B : Bytes_16) return String is
      Hex : constant String := "0123456789abcdef";
      S   : String (1 .. 32);
   begin
      for I in B'Range loop
         S (2 * I + 1) := Hex (Integer (Shift_Right (B (I), 4)) + 1);
         S (2 * I + 2) := Hex (Integer (B (I) and 15) + 1);
      end loop;
      return S;
   end Image;

   function Image (E : Element) return String is
      Hex : constant String := "0123456789abcdef";
      S   : String (1 .. 32);
      V   : Unsigned_64;
   begin
      for I in 0 .. 31 loop
         V := E.Limbs ((if I < 16 then 1 else 0));
         S (I + 1) :=
           Hex (Integer (Shift_Right (V, 60 - 4 * (I mod 16)) and 15) + 1);
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
      Fields := (others => (0, 0));
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
   begin
      Split (Line, Fields, Count);
      if Count = 0 then
         return;
      end if;
      declare
         Op : constant String := Line (Fields (1).Lo .. Fields (1).Hi);
      begin
         if Op = "mul" then
            if Count /= 4 then
               raise Parse_Error with "mul expects 3 values";
            end if;
            declare
               A    : constant Element :=
                 To_Element (Line (Fields (2).Lo .. Fields (2).Hi));
               B    : constant Element :=
                 To_Element (Line (Fields (3).Lo .. Fields (3).Hi));
               Want : constant Element :=
                 To_Element (Line (Fields (4).Lo .. Fields (4).Hi));
               Got  : constant Element := Mul (A, B);
            begin
               if Got = Want then
                  Passed := Passed + 1;
               else
                  Report_Failure
                    ("mul " & Image (A) & " " & Image (B)
                     & " expected " & Image (Want) & " got " & Image (Got));
               end if;
            end;
         elsif Op = "square" then
            if Count /= 3 then
               raise Parse_Error with "square expects 2 values";
            end if;
            declare
               A    : constant Element :=
                 To_Element (Line (Fields (2).Lo .. Fields (2).Hi));
               Want : constant Element :=
                 To_Element (Line (Fields (3).Lo .. Fields (3).Hi));
               Got  : constant Element := Square (A);
            begin
               if Got = Want then
                  Passed := Passed + 1;
               else
                  Report_Failure
                    ("square " & Image (A)
                     & " expected " & Image (Want) & " got " & Image (Got));
               end if;
            end;
         elsif Op = "inv" then
            if Count /= 3 then
               raise Parse_Error with "inv expects 2 values";
            end if;
            declare
               A    : constant Element :=
                 To_Element (Line (Fields (2).Lo .. Fields (2).Hi));
               Want : constant Element :=
                 To_Element (Line (Fields (3).Lo .. Fields (3).Hi));
               Got  : constant Element := Inv (A);
            begin
               if Got /= Want then
                  Report_Failure
                    ("inv " & Image (A)
                     & " expected " & Image (Want) & " got " & Image (Got));
               elsif A /= Zero and then Mul (A, Got) /= One then
                  Report_Failure
                    ("inv " & Image (A) & " times its input is "
                     & Image (Mul (A, Got)) & ", not one");
               else
                  Passed := Passed + 1;
               end if;
            end;
         elsif Op = "bytes" then
            if Count /= 3 then
               raise Parse_Error with "bytes expects 2 values";
            end if;
            declare
               A    : constant Element :=
                 To_Element (Line (Fields (2).Lo .. Fields (2).Hi));
               Want : constant Bytes_16 :=
                 To_Bytes_16 (Line (Fields (3).Lo .. Fields (3).Hi));
               Got  : constant Bytes_16 := To_Bytes (A);
               Back : Element;
               Ok   : Boolean;
            begin
               From_Bytes (Want, Back, Ok);
               if Got /= Want then
                  Report_Failure
                    ("bytes " & Image (A) & " expected " & Image (Want)
                     & " got " & Image (Got));
               elsif not Ok or else Back /= A then
                  Report_Failure
                    ("bytes " & Image (Want) & " read back as "
                     & Image (Back));
               else
                  Passed := Passed + 1;
               end if;
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
      TIO.Put_Line ("GF2_128 known-answer tests: " & Path);
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
      Run_File (Default_Mul);
      Run_File (Default_Square);
      Run_File (Default_Inv);
      Run_File (Default_Bytes);
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
end GF2_128_KAT;
