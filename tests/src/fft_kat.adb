--  FFT_KAT: test harness for Additive_Fft (Phase D, block 3, ADR 0057).
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Built with
--  -gnata, so the executable contracts of the library run. This build is
--  not the constant-time build.
--
--  Two kinds of check.
--  - The vector file given as argument (default tests/vectors/fft.txt,
--    written by gen_fft_vectors.py), one case per line, '#' comments:
--      what <i> <j> <value>          W_Hat (i, j) = value
--      twiddle <i> <u> <value>       Twiddle (i, u) = value
--      extend <n> <m> <y ...> <c ...>
--                                    Extend of the n values y gives the
--                                    m - n values c after them
--    with each element as 32 big-endian hex digits, as gf2_128_kat.
--  - The encoder of chapter 5: on pseudo-random rows of the lengths of
--    the Ligero geometries, Extend must agree with Lagrange.Evaluate on
--    every parity column. This is the test that the two encoders give
--    the same codeword, which is not proved (ADR 0057).
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Exceptions;
with Ada.Text_IO;
with Interfaces;    use Interfaces;
with GF2_128;       use GF2_128;
with Additive_Fft;
with Lagrange_GF2_128;

procedure FFT_KAT is

   package TIO renames Ada.Text_IO;
   package LG renames Lagrange_GF2_128;

   Default_File : constant String := "tests/vectors/fft.txt";

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
         when others =>
            raise Parse_Error with "bad hex digit '" & C & "'";
      end case;
   end Hex_Digit;

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

   procedure Check (Ok : Boolean; What : String) is
   begin
      if Ok then
         Passed := Passed + 1;
      else
         Failed := Failed + 1;
         TIO.Put_Line ("FAIL line" & Line_No'Image & ": " & What);
      end if;
   end Check;

   --  The blank-separated fields of a line.
   type Field_Bounds is record
      First, Last : Natural;
   end record;
   type Field_List is array (Positive range <>) of Field_Bounds;

   function Split (S : String) return Field_List is
      Result : Field_List (1 .. S'Length / 2 + 1);
      Count  : Natural := 0;
      I      : Natural := S'First;
   begin
      while I <= S'Last loop
         while I <= S'Last and then S (I) = ' ' loop
            I := I + 1;
         end loop;
         exit when I > S'Last;
         Count := Count + 1;
         Result (Count).First := I;
         while I <= S'Last and then S (I) /= ' ' loop
            I := I + 1;
         end loop;
         Result (Count).Last := I - 1;
      end loop;
      return Result (1 .. Count);
   end Split;

   procedure Run_File (Path : String) is
      File : TIO.File_Type;
   begin
      TIO.Open (File, TIO.In_File, Path);
      while not TIO.End_Of_File (File) loop
         declare
            Line : constant String := TIO.Get_Line (File);
            F    : constant Field_List := Split (Line);
            function Fld (K : Positive) return String is
              (Line (F (K).First .. F (K).Last));
            function Num (K : Positive) return Natural is
              (Natural'Value (Fld (K)));
         begin
            Line_No := Line_No + 1;
            if F'Length = 0 or else Line (F (1).First) = '#' then
               null;
            elsif Fld (1) = "what" then
               Check (Additive_Fft.W_Hat (Num (2), Num (3)) = To_Element (Fld (4)),
                      "W_Hat" & Num (2)'Image & Num (3)'Image);
            elsif Fld (1) = "twiddle" then
               Check (Additive_Fft.Twiddle (Num (2), Num (3)) = To_Element (Fld (4)),
                      "Twiddle" & Num (2)'Image & Num (3)'Image);
            elsif Fld (1) = "extend" then
               declare
                  N   : constant Positive := Num (2);
                  M   : constant Positive := Num (3);
                  Row : Additive_Fft.Element_Array (0 .. N - 1);
                  Enc : Additive_Fft.Element_Array (0 .. M - 1);
                  Ok  : Boolean := True;
               begin
                  if F'Length /= 3 + M then
                     raise Parse_Error with "extend: expected" & Natural'Image (M)
                       & " elements";
                  end if;
                  for X in 0 .. N - 1 loop
                     Row (X) := To_Element (Fld (4 + X));
                  end loop;
                  Additive_Fft.Extend (Row, Enc);
                  for X in 0 .. M - 1 loop
                     Ok := Ok and then Enc (X) = To_Element (Fld (4 + X));
                  end loop;
                  Check (Ok, "Extend n =" & N'Image & ", m =" & M'Image);
               end;
            else
               raise Parse_Error with "unknown operation '" & Fld (1) & "'";
            end if;
         exception
            when E : Parse_Error | Constraint_Error =>
               Failed := Failed + 1;
               TIO.Put_Line ("FAIL line" & Line_No'Image & ": "
                             & Ada.Exceptions.Exception_Message (E));
         end;
      end loop;
      TIO.Close (File);
   end Run_File;

   --  A 64-bit linear congruential generator for the rows (test only).
   State : Unsigned_64 := 16#2026_1020#;

   function Next return Unsigned_64 is
   begin
      State := State * 6364136223846793005 + 1442695040888963407;
      return State;
   end Next;

   --  Extend against Lagrange.Evaluate on every parity column of one
   --  random row of N values extended to M points.
   procedure Against_Lagrange (N, M : Positive) is
      Cols  : LG.Column_Array (0 .. M - N - 1);
      T     : LG.Table (0 .. N - 1, 0 .. M - N - 1);
      Inv_D : LG.Element_Array (0 .. N - 1);
      Coeff : LG.Element_Array (0 .. N - 1);
      Row   : Additive_Fft.Element_Array (0 .. N - 1);
      Enc   : Additive_Fft.Element_Array (0 .. M - 1);
      Ok    : Boolean;
      Same  : Boolean := True;
   begin
      for C in Cols'Range loop
         Cols (C) := N + C;
      end loop;
      LG.Build (N, Cols, T, Inv_D, Ok);
      for X in 0 .. N - 1 loop
         Row (X) := (Limbs => [0 => Next, 1 => Next]);
         Coeff (X) := Row (X);
      end loop;
      Additive_Fft.Extend (Row, Enc);
      for C in Cols'Range loop
         Same := Same and then Enc (N + C) = LG.Evaluate (Coeff, T, C);
      end loop;
      Check (Ok and then Same,
             "Extend /= Lagrange for n =" & N'Image & ", m =" & M'Image);
   end Against_Lagrange;

   type Shape is record
      N, M : Positive;
   end record;
   --  Small shapes, every power-of-two boundary, cosets, and the shapes
   --  of the two Phase C geometries (rows of 8 and 120 values over 256
   --  columns and their dblock rows).
   Shapes : constant array (Positive range <>) of Shape :=
     [(1, 2), (2, 3), (3, 4), (4, 9), (5, 64), (8, 8), (15, 47), (16, 17),
      (17, 18), (33, 200), (64, 256), (85, 256), (120, 256), (128, 300),
      (171, 256), (100, 600)];

begin
   if Ada.Command_Line.Argument_Count = 0 then
      Run_File (Default_File);
   else
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         Run_File (Ada.Command_Line.Argument (I));
      end loop;
   end if;
   for S of Shapes loop
      Against_Lagrange (S.N, S.M);
   end loop;
   TIO.Put_Line ("passed" & Passed'Image & ", failed" & Failed'Image);
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end FFT_KAT;
