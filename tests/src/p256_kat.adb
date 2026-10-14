--  P256_KAT: known-answer test harness for P256_Field.
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads the
--  vector files given as arguments (default: the p256_*.txt files under
--  tests/vectors/) and checks every case against the library. Built
--  with -gnata, so the library's contracts, including the ghost
--  big-integer model, execute at run time. Not the constant-time build.
--
--  File format: '#' comments and blank lines are skipped; otherwise one
--  case per line, fields separated by blanks, values as 64 hex digits of
--  the integer, most significant first:
--    add <a> <b> <expected>      sub <a> <b> <expected>     neg <a> <expected>
--    mul <a> <b> <expected>      square <a> <expected>      inv <a> <expected>
--    frombytes <32 bytes as 64 hex digits in memory order> <ok> <value>
--  Operations not yet implemented in the library are reported as
--  failures ("unknown operation"), so a vector file never passes
--  silently.
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Exceptions;
with Ada.Text_IO;
with Interfaces;  use Interfaces;
with Bytes;       use type Bytes.Byte_Array;
with P256_Field;  use P256_Field;

procedure P256_KAT is

   package TIO renames Ada.Text_IO;

   function Default_Path (I : Positive) return String is
     (case I is
         when 1 => "tests/vectors/p256_add.txt",
         when 2 => "tests/vectors/p256_mul.txt",
         when 3 => "tests/vectors/p256_inv.txt",
         when others => "tests/vectors/p256_bytes.txt");

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

   --  64 big-endian hex digits; the first 16 form Limbs (3).
   function To_Limbs (S : String) return Limb_Array is
      R : Limb_Array := [others => 0];
      L : Limb_Index;
   begin
      if S'Length /= 64 then
         raise Parse_Error with "expected 64 hex digits, got '" & S & "'";
      end if;
      for I in 0 .. 63 loop
         L := Limb_Index (3 - I / 16);
         R (L) := Shift_Left (R (L), 4) or Hex_Digit (S (S'First + I));
      end loop;
      return R;
   end To_Limbs;

   function To_Element (S : String) return Element is
      L : constant Limb_Array := To_Limbs (S);
   begin
      if not Is_Canonical (L) then
         raise Parse_Error with "value not below p: " & S;
      end if;
      return (Limbs => L);
   end To_Element;

   --  64 hex digits in memory order: byte 0 first.
   function To_Bytes_32 (S : String) return Bytes_32 is
      R : Bytes_32 := [others => 0];
   begin
      if S'Length /= 64 then
         raise Parse_Error with "expected 64 hex digits of bytes";
      end if;
      for I in 0 .. 31 loop
         R (I) := Unsigned_8 (Shift_Left (Hex_Digit (S (S'First + 2 * I)), 4)
                              or Hex_Digit (S (S'First + 2 * I + 1)));
      end loop;
      return R;
   end To_Bytes_32;

   function Image (L : Limb_Array) return String is
      Hex : constant String := "0123456789abcdef";
      S   : String (1 .. 64);
      V   : Unsigned_64;
   begin
      for I in 0 .. 63 loop
         V := L (Limb_Index (3 - I / 16));
         S (I + 1) :=
           Hex (Integer (Shift_Right (V, 60 - 4 * (I mod 16)) and 15) + 1);
      end loop;
      return S;
   end Image;

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

   procedure Check (Ok : Boolean; Msg : String) is
   begin
      if Ok then
         Passed := Passed + 1;
      else
         Report_Failure (Msg);
      end if;
   end Check;

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
         function F (K : Positive) return String is
           (Line (Fields (K).Lo .. Fields (K).Hi));
      begin
         if Op = "add" or else Op = "sub" then
            if Count /= 4 then
               raise Parse_Error with Op & " expects 3 values";
            end if;
            declare
               A    : constant Element := To_Element (F (2));
               B    : constant Element := To_Element (F (3));
               Want : constant Element := To_Element (F (4));
               Got  : constant Element :=
                 (if Op = "add" then Add (A, B) else Sub (A, B));
            begin
               Check (Got = Want,
                      Op & " " & F (2) & " " & F (3) & " expected " & F (4)
                      & " got " & Image (Got.Limbs));
            end;
         elsif Op = "mul" then
            if Count /= 4 then
               raise Parse_Error with "mul expects 3 values";
            end if;
            declare
               A    : constant Element := To_Element (F (2));
               B    : constant Element := To_Element (F (3));
               Want : constant Element := To_Element (F (4));
               Got  : constant Element := Mul (A, B);
            begin
               Check (Got = Want,
                      "mul " & F (2) & " " & F (3) & " expected " & F (4)
                      & " got " & Image (Got.Limbs));
            end;
         elsif Op = "square" then
            if Count /= 3 then
               raise Parse_Error with "square expects 2 values";
            end if;
            declare
               A    : constant Element := To_Element (F (2));
               Want : constant Element := To_Element (F (3));
               Got  : constant Element := Square (A);
            begin
               Check (Got = Want,
                      "square " & F (2) & " expected " & F (3)
                      & " got " & Image (Got.Limbs));
            end;
         elsif Op = "inv" then
            if Count /= 3 then
               raise Parse_Error with "inv expects 2 values";
            end if;
            declare
               A    : constant Element := To_Element (F (2));
               Want : constant Element := To_Element (F (3));
               Got  : constant Element := Inv (A);
            begin
               if Got /= Want then
                  Report_Failure ("inv " & F (2) & " expected " & F (3)
                                  & " got " & Image (Got.Limbs));
               elsif A /= Zero and then Mul (A, Got) /= One then
                  Report_Failure ("inv " & F (2)
                                  & " times its input is not one");
               else
                  Passed := Passed + 1;
               end if;
            end;
         elsif Op = "neg" then
            if Count /= 3 then
               raise Parse_Error with "neg expects 2 values";
            end if;
            declare
               A    : constant Element := To_Element (F (2));
               Want : constant Element := To_Element (F (3));
               Got  : constant Element := Neg (A);
            begin
               Check (Got = Want,
                      "neg " & F (2) & " expected " & F (3)
                      & " got " & Image (Got.Limbs));
            end;
         elsif Op = "frombytes" then
            if Count /= 4 then
               raise Parse_Error with "frombytes expects 3 fields";
            end if;
            declare
               B       : constant Bytes_32 := To_Bytes_32 (F (2));
               Want_Ok : constant Boolean := F (3) = "1";
               Want    : constant Limb_Array := To_Limbs (F (4));
               E       : Element;
               Ok      : Boolean;
            begin
               From_Bytes (B, E, Ok);
               if Ok /= Want_Ok then
                  Report_Failure ("frombytes " & F (2) & " expected ok="
                                  & F (3) & " got " & Ok'Image);
               elsif E.Limbs /= Want then
                  Report_Failure ("frombytes " & F (2) & " expected value "
                                  & F (4) & " got " & Image (E.Limbs));
               elsif Ok and then To_Bytes (E) /= B then
                  Report_Failure ("to_bytes round trip failed for " & F (2));
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
         Report_Failure
           (Ada.Exceptions.Exception_Name (E) & ": "
            & Ada.Exceptions.Exception_Message (E));
   end Check_Case;

   procedure Run_File (Path : String) is
      File : TIO.File_Type;
   begin
      TIO.Put_Line ("P256_Field known-answer tests: " & Path);
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
      for I in 1 .. 4 loop
         Run_File (Default_Path (I));
      end loop;
   else
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         Run_File (Ada.Command_Line.Argument (I));
      end loop;
   end if;

   TIO.Put_Line ("passed" & Passed'Image & ", failed" & Failed'Image);
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end P256_KAT;
