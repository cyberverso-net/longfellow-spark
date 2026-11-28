--  longfellow_check_circuit: run the circuit checker's walk on a circuit
--  file and its certificate (ADR 0093, ADR 0094), and print the verdict
--  with the circuit's identifier and the digests of both files. Outside
--  the proof perimeter (SPARK_Mode is Off: file input and output);
--  everything it calls is the SPARK library.
--
--    longfellow_check_circuit --field gf2_128 --circuit FILE
--                             --certificate FILE
--
--  Reads both files, runs Circuit_Check_GF2_128.Check (the circuit
--  through the verifier's reader in its packed form, the certificate
--  through Circuit_Certificates.Read, the identifiers compared, the
--  walk), and prints:
--    - the circuit's identifier, as its header gives it;
--    - the SHA-256 of the circuit file and of the certificate file;
--    - where the check stopped, with the status of that step;
--    - what the verdict rests on: the walk is proved (its postcondition
--      is Circuit_Checker.Accepts, and Lemma_Accepts gives the facts),
--      and the catalogue's check, which compares the facts with the
--      relation's gadgets, is not run yet (#222).
--  Only the field of the hash circuit, GF(2^128), has a proved instance
--  of the checker yet; the signature circuit's comes with its block.
--
--  Exit status: 0 when the walk accepts, 1 when a step refuses, 2 on a
--  usage or file error.
--  Documentation: docs/guide/10-certified-circuits.md, Section 4.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Exceptions;
with Ada.Characters.Handling;
with Ada.Text_IO;
with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with Sha256;
with Circuit_Check_GF2_128;
with Mdoc_Cli;

procedure Longfellow_Check_Circuit is

   package TIO renames Ada.Text_IO;
   package CL renames Ada.Command_Line;
   package Chk renames Circuit_Check_GF2_128;
   use type Chk.Outcome;

   Usage_Error : exception;

   function Lower (S : String) return String
     renames Ada.Characters.Handling.To_Lower;

   --  The files are read by Mdoc_Cli.Read_File: on the heap, at most
   --  Mdoc_Cli.Max_File_Bytes (16 MB), a file that grows, cannot be
   --  opened or cannot be read a usage error (Mdoc_Cli.Usage_Error).
   function Read_File (Path : String) return Mdoc_Cli.Byte_Array_Access
     renames Mdoc_Cli.Read_File;

   function Hex (B : Byte_Array) return String is
      Digits_Hex : constant String := "0123456789abcdef";
      S : String (1 .. 2 * B'Length);
      I : Positive := 1;
   begin
      for X of B loop
         S (I) := Digits_Hex (Natural (Shift_Right (X, 4)) + 1);
         S (I + 1) := Digits_Hex (Natural (X and 16#0F#) + 1);
         I := I + 2;
      end loop;
      return S;
   end Hex;

   function Digest (B : Byte_Array) return Bytes_32 is
      Ctx : Sha256.Context := Sha256.Initial;
   begin
      Sha256.Update (Ctx, B);
      return Sha256.Digest (Ctx);
   end Digest;

   procedure Usage is
   begin
      TIO.Put_Line
        ("usage: longfellow_check_circuit --field gf2_128 --circuit FILE"
         & " --certificate FILE");
   end Usage;

   Field       : access String;
   Circuit     : access String;
   Certificate : access String;
   I           : Positive := 1;

begin
   while I <= CL.Argument_Count loop
      declare
         A : constant String := CL.Argument (I);
      begin
         if A = "--help" then
            Usage;
            return;
         end if;
         if I = CL.Argument_Count then
            raise Usage_Error with "missing value after " & A;
         end if;
         if A = "--field" then
            Field := new String'(CL.Argument (I + 1));
         elsif A = "--circuit" then
            Circuit := new String'(CL.Argument (I + 1));
         elsif A = "--certificate" then
            Certificate := new String'(CL.Argument (I + 1));
         else
            raise Usage_Error with "unknown option " & A;
         end if;
         I := I + 2;
      end;
   end loop;
   if Field = null or else Circuit = null or else Certificate = null then
      raise Usage_Error with "--field, --circuit and --certificate are needed";
   end if;
   if Field.all /= "gf2_128" then
      raise Usage_Error
        with "field " & Field.all & ": only gf2_128 has a proved checker yet";
   end if;

   declare
      C : constant Mdoc_Cli.Byte_Array_Access := Read_File (Circuit.all);
      K : constant Mdoc_Cli.Byte_Array_Access :=
        Read_File (Certificate.all);
      R : Chk.Result;
   begin
      Chk.Check (C.all, K.all, R);
      TIO.Put_Line ("circuit identifier:  " & Hex (R.Id));
      TIO.Put_Line ("circuit file SHA-256: " & Hex (Digest (C.all)));
      TIO.Put_Line ("certificate SHA-256:  " & Hex (Digest (K.all)));
      case R.Outcome is
         when Chk.Accepted =>
            TIO.Put_Line ("walk: accepted");
         when Chk.Circuit_Refused =>
            TIO.Put_Line ("circuit refused: " & Lower (R.Circuit'Image));
         when Chk.Certificate_Refused =>
            TIO.Put_Line
              ("certificate refused: " & Lower (R.Certificate'Image));
         when Chk.Wrong_Circuit =>
            TIO.Put_Line ("wrong circuit: the certificate names another");
         when Chk.Walk_Refused =>
            TIO.Put_Line ("walk refused: " & Lower (R.Walk'Image));
      end case;
      TIO.Put_Line
        ("proved: the walk accepts exactly when Circuit_Checker.Accepts"
         & " holds, and then every fact holds at a satisfying evaluation"
         & " (Lemma_Accepts)");
      TIO.Put_Line
        ("not run: the catalogue's check of the facts against the"
         & " relation's gadgets (#222)");
      CL.Set_Exit_Status
        (if R.Outcome = Chk.Accepted then CL.Success else 1);
   end;
exception
   when E : Usage_Error | Mdoc_Cli.Usage_Error =>
      TIO.Put_Line
        (TIO.Standard_Error,
         "longfellow_check_circuit: " & Ada.Exceptions.Exception_Message (E));
      Usage;
      CL.Set_Exit_Status (2);
end Longfellow_Check_Circuit;
