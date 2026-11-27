--  CHECKER_CENSUS: the circuit checker on a circuit file and a
--  certificate, for the comparison with scripts/census.py (ADR 0093).
--  It runs Circuit_Check, the checker on two files, and on acceptance
--  computes the digest of the facts with Layer_Coefficients and
--  Next_Layer (Checker_Facts). It prints one line:
--    <outcome> <status> <facts digest, or ->
--  The step vectors of scripts/check.sh runs it on the registered pair,
--  with the certificates census.py writes, and compares the digest with
--  census.py's.
--
--  GF(2^128) uses the library's instance Circuit_Checker_GF2_128, with
--  the limits of ADR 0093. P-256 uses an instance declared here with the
--  record's limits for the signature circuit; the proved instance for
--  P-256 comes with block 6.
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off.
--  Exit status: 0 when the checker ran (whatever its outcome), 2 on a
--  wrong argument or an unreadable file.

pragma SPARK_Mode (Off);

with Ada.Characters.Handling;
with Ada.Command_Line;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with GF2_128;
with P256_Field;
with Circuit_Status;
with Circuit_Certificates;
with Sumcheck_Algebra_GF2_128;
with Packed_Circuits_GF2_128;
with Circuit_Reader_GF2_128;
with Circuit_Checker_GF2_128;
with Circuit_Check_GF2_128;
with Sumcheck_Algebra_P256;
with Packed_Circuits_P256;
with Circuit_Reader_P256;
with Sumcheck_Algebra;
with Packed_Circuits;
with Circuit_Reader;
with Circuit_Checker;
with Circuit_Check;
with Checker_Facts;

procedure Checker_Census is

   package TIO renames Ada.Text_IO;
   package CC renames Circuit_Certificates;
   use type Circuit_Status.Status;
   use type CC.Status;

   type Byte_Access is access Byte_Array;

   function Read_File (Path : String) return Byte_Access is
      use Ada.Streams.Stream_IO;
      F : Ada.Streams.Stream_IO.File_Type;
   begin
      Open (F, In_File, Path);
      declare
         N : constant Natural := Natural (Size (F));
         B : constant Byte_Access := new Byte_Array (0 .. N - 1);
      begin
         Byte_Array'Read (Stream (F), B.all);
         Close (F);
         return B;
      end;
   end Read_File;

   function To_Hex (B : Byte_Array) return String is
      Hex : constant String := "0123456789abcdef";
      R   : String (1 .. 2 * B'Length);
   begin
      for I in 0 .. B'Length - 1 loop
         R (2 * I + 1) := Hex (Integer (Shift_Right (B (B'First + I), 4)) + 1);
         R (2 * I + 2) := Hex (Integer (B (B'First + I) and 15) + 1);
      end loop;
      return R;
   end To_Hex;

   function Lower (S : String) return String
     renames Ada.Characters.Handling.To_Lower;

   --  One field: the checker on the two files, the line printed.
   generic
      with package SA is new Sumcheck_Algebra (<>);
      with package PC is new Packed_Circuits (SA);
      with package CR is new Circuit_Reader (SA, PC, others => <>);
      with package CK is new Circuit_Checker (SA, PC, others => <>);
      with package Chk is new Circuit_Check (SA, PC, CR, CK);
      Pool_Size : Positive;
      with function To_Bytes (E : SA.Element) return Byte_Array;
   procedure Run (Circuit, Cert : Byte_Array);

   procedure Run (Circuit, Cert : Byte_Array) is
      use type Chk.Outcome;
      package Facts is new Checker_Facts (SA, PC, CK, Pool_Size, To_Bytes);
      R : Chk.Result;
   begin
      Chk.Check (Circuit, Cert, R);
      declare
         Status : constant String :=
           (case R.Outcome is
              when Chk.Certificate_Refused => Lower (R.Certificate'Image),
              when Chk.Walk_Refused        => Lower (R.Walk'Image),
              when Chk.Circuit_Refused     => Lower (R.Circuit'Image),
              when others                  => "-");
      begin
         if R.Outcome = Chk.Accepted then
            declare
               P   : CR.Packed_Access;
               H   : CR.Header;
               St  : Circuit_Status.Status;
               K   : CC.Cert_Access;
               KSt : CC.Status;
            begin
               CR.Read_Packed (Circuit, False, [others => 0], P, H, St);
               CC.Read (Cert, K, KSt);
               TIO.Put_Line ("accepted - "
                             & To_Hex (Facts.Facts_Digest (P.all, K.all)));
            end;
         else
            TIO.Put_Line (Lower (R.Outcome'Image) & " " & Status & " -");
         end if;
      end;
   end Run;

   --  The P-256 instance, with ADR 0093's limits for the signature
   --  circuit.
   package Checker_P256 is new Circuit_Checker
     (Sumcheck_Algebra_P256, Packed_Circuits_P256,
      Max_Form => 2, Max_Terms_Per_Wire => 769, Max_Slots => 769,
      Max_Layer_Slots => 2 ** 18, Max_Vars => 2 ** 18);
   package Check_P256 is new Circuit_Check
     (Sumcheck_Algebra_P256, Packed_Circuits_P256, Circuit_Reader_P256,
      Checker_P256);

   function GF2_Bytes (E : Sumcheck_Algebra_GF2_128.Element)
     return Byte_Array is (GF2_128.To_Bytes (E));
   function P256_Bytes (E : Sumcheck_Algebra_P256.Element)
     return Byte_Array is (Byte_Array (P256_Field.To_Bytes (E)));

   procedure Run_GF2_128 is new Run
     (Sumcheck_Algebra_GF2_128, Packed_Circuits_GF2_128,
      Circuit_Reader_GF2_128, Circuit_Checker_GF2_128, Circuit_Check_GF2_128,
      Pool_Size => 2 ** 22, To_Bytes => GF2_Bytes);
   procedure Run_P256 is new Run
     (Sumcheck_Algebra_P256, Packed_Circuits_P256, Circuit_Reader_P256,
      Checker_P256, Check_P256, Pool_Size => 2 ** 18, To_Bytes => P256_Bytes);

begin
   if Ada.Command_Line.Argument_Count /= 3 then
      TIO.Put_Line ("usage: checker_census gf2_128|p256 CIRCUIT CERTIFICATE");
      Ada.Command_Line.Set_Exit_Status (2);
      return;
   end if;
   declare
      Field   : constant String := Ada.Command_Line.Argument (1);
      Circuit : constant Byte_Access := Read_File (Ada.Command_Line.Argument (2));
      Cert    : constant Byte_Access := Read_File (Ada.Command_Line.Argument (3));
   begin
      if Field = "gf2_128" then
         Run_GF2_128 (Circuit.all, Cert.all);
      elsif Field = "p256" then
         Run_P256 (Circuit.all, Cert.all);
      else
         TIO.Put_Line ("checker_census: unknown field " & Field);
         Ada.Command_Line.Set_Exit_Status (2);
      end if;
   end;
end Checker_Census;
