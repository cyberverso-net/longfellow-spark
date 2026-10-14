--  SUMCHECK_KAT: known-answer test harness for Sumcheck_Algebra over
--  both fields (ADR 0027). Test code, outside the proof perimeter.
--
--  Reads the vector files given as arguments (default: sumcheck_gf2_128.txt
--  and sumcheck_p256.txt under tests/vectors/, plus every
--  sumcheck_core_*.txt under tests/vectors/upstream/ when present); the
--  first non-comment line of a file, "field <name>", selects the
--  instance. Built with
--  -gnata, so every contract and ghost reference of the library executes:
--  in particular the Post of Eval_Circuit evaluates Acc_Ref on every wire.
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Directories;
with Ada.Text_IO;
with Interfaces; use Interfaces;
with GF2_128;
with P256_Field;
with Sumcheck_Algebra_GF2_128;
with Sumcheck_Algebra_P256;
with Sumcheck_Expression_GF2_128;
with Sumcheck_Expression_P256;
with Sumcheck_Verifier_GF2_128;
with Sumcheck_Verifier_P256;
with Sumcheck_Transcript_GF2_128;
with Sumcheck_Transcript_P256;
with Sumcheck_KAT_Generic;

procedure Sumcheck_KAT is

   package TIO renames Ada.Text_IO;

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

   Hex : constant String := "0123456789abcdef";

   --  GF(2^128): 32 big-endian hex digits; the first 16 form Limbs (1).
   function GF_To_Element (S : String) return GF2_128.Element is
      R : GF2_128.Element := GF2_128.Zero;
      L : GF2_128.Limb_Index;
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
   end GF_To_Element;

   function GF_Image (E : GF2_128.Element) return String is
      S : String (1 .. 32);
      V : Unsigned_64;
   begin
      for I in 0 .. 31 loop
         V := E.Limbs ((if I < 16 then 1 else 0));
         S (I + 1) :=
           Hex (Integer (Shift_Right (V, 60 - 4 * (I mod 16)) and 15) + 1);
      end loop;
      return S;
   end GF_Image;

   --  P-256: 64 big-endian hex digits; the first 16 form Limbs (3).
   function P_To_Element (S : String) return P256_Field.Element is
      R : P256_Field.Limb_Array := [others => 0];
      L : P256_Field.Limb_Index;
   begin
      if S'Length /= 64 then
         raise Parse_Error with "expected 64 hex digits, got '" & S & "'";
      end if;
      for I in 0 .. 63 loop
         L := P256_Field.Limb_Index (3 - I / 16);
         R (L) := Shift_Left (R (L), 4) or Hex_Digit (S (S'First + I));
      end loop;
      if not P256_Field.Is_Canonical (R) then
         raise Parse_Error with "value not below p: " & S;
      end if;
      return (Limbs => R);
   end P_To_Element;

   function P_Image (E : P256_Field.Element) return String is
      S : String (1 .. 64);
      V : Unsigned_64;
   begin
      for I in 0 .. 63 loop
         V := E.Limbs (P256_Field.Limb_Index (3 - I / 16));
         S (I + 1) :=
           Hex (Integer (Shift_Right (V, 60 - 4 * (I mod 16)) and 15) + 1);
      end loop;
      return S;
   end P_Image;

   package GF_KAT is new Sumcheck_KAT_Generic
     (SA => Sumcheck_Algebra_GF2_128, SE => Sumcheck_Expression_GF2_128,
      SV => Sumcheck_Verifier_GF2_128, ST => Sumcheck_Transcript_GF2_128,
      Field_Name => "gf2_128",
      To_Element => GF_To_Element, Image => GF_Image);

   package P_KAT is new Sumcheck_KAT_Generic
     (SA => Sumcheck_Algebra_P256, SE => Sumcheck_Expression_P256,
      SV => Sumcheck_Verifier_P256, ST => Sumcheck_Transcript_P256,
      Field_Name => "p256",
      To_Element => P_To_Element, Image => P_Image);

   Passed : Natural := 0;
   Failed : Natural := 0;

   --  The first non-comment line names the field.
   function Field_Of (Path : String) return String is
      File : TIO.File_Type;
   begin
      TIO.Open (File, TIO.In_File, Path);
      while not TIO.End_Of_File (File) loop
         declare
            Line : constant String := TIO.Get_Line (File);
         begin
            if Line'Length > 6 and then Line (Line'First) /= '#'
              and then Line (Line'First .. Line'First + 5) = "field "
            then
               TIO.Close (File);
               return Line (Line'First + 6 .. Line'Last);
            end if;
         end;
      end loop;
      TIO.Close (File);
      return "";
   end Field_Of;

   procedure Run (Path : String) is
      Field : constant String := Field_Of (Path);
   begin
      if Field = "gf2_128" then
         GF_KAT.Run_File (Path, Passed, Failed);
      elsif Field = "p256" then
         P_KAT.Run_File (Path, Passed, Failed);
      else
         TIO.Put_Line ("FAIL " & Path & ": no field line");
         Failed := Failed + 1;
      end if;
   end Run;

begin
   if Ada.Command_Line.Argument_Count = 0 then
      Run ("tests/vectors/sumcheck_gf2_128.txt");
      Run ("tests/vectors/sumcheck_p256.txt");
      declare
         use Ada.Directories;
         Search : Search_Type;
         Item   : Directory_Entry_Type;
      begin
         --  The zk_proof files first: each recording of tier 3 needs
         --  the proof of its circuit (stage 4, ADR 0032).
         Start_Search (Search, "tests/vectors", "zk_proof_*.txt");
         while More_Entries (Search) loop
            Get_Next_Entry (Search, Item);
            Run (Full_Name (Item));
         end loop;
         End_Search (Search);
         if Exists ("tests/vectors/upstream")
           and then Kind ("tests/vectors/upstream") = Directory
         then
            Start_Search (Search, "tests/vectors/upstream",
                          "sumcheck_core_*.txt");
            while More_Entries (Search) loop
               Get_Next_Entry (Search, Item);
               Run (Full_Name (Item));
            end loop;
            End_Search (Search);
         end if;
      end;
   else
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         Run (Ada.Command_Line.Argument (I));
      end loop;
   end if;

   TIO.Put_Line ("passed" & Passed'Image & ", failed" & Failed'Image);
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end Sumcheck_KAT;
