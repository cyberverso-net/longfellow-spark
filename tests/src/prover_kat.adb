--  PROVER_KAT: the known-answer harness of the prover (Phase C, ADR
--  0053), block 3: the sumcheck prover of Section 6.6 on the Appendix
--  B.3 circuits and the Z-assertion circuit, against the independent
--  reference prover of gen_prover_vectors.py run with the same seeded
--  source (Simple_Rng), the same label, root and circuit identifier:
--  the pads drawn and the padded proof, written in the order of Section
--  7.3, must be identical. Then the proof is handed to the verifier
--  side: the challenges replayed from the proof by Replay_Challenges
--  must be the ones the prover recorded, and the linear and quadratic
--  constraints Verifier_Core emits on the witness vector (private
--  inputs, then pads) must hold, so that the proof is one a Ligero
--  commitment of that vector can satisfy (blocks 4 and 5).
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads
--  the vector files given as arguments (default: sumcheck_prover.txt
--  under tests/vectors/). Built with -gnata, so the library's
--  executable contracts run (the circuits here are small).
--
--  File format: '#' comments and blank lines are skipped; otherwise
--    sumcheck <name> <field> <seed> <label> <root> <circuit lfc2>
--             <nwit> <witness...> <npads> <pads...> <proof bytes>
--  with elements as big-endian hex integers, bytes as hex.
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Exceptions;
with Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with GF2_128;
with P256_Field;
with Transcript;
with Circuit_Status;
with Sumcheck_Verifier;
with Field_Signature;
with Field_GF2_128;
with Field_P256;
with Sumcheck_Algebra;
with Sumcheck_Expression;
with Sumcheck_Transcript;
with Ligero_Proof;
with Lagrange;
with Ligero_Verifier;
with Circuit_Reader;
with Proof_Writer;
with Sumcheck_Prover;
with Simple_Rng;
with Sumcheck_Algebra_GF2_128;
with Sumcheck_Algebra_P256;
with Sumcheck_Expression_GF2_128;
with Sumcheck_Expression_P256;
with Sumcheck_Verifier_GF2_128;
with Sumcheck_Verifier_P256;
with Sumcheck_Transcript_GF2_128;
with Sumcheck_Transcript_P256;
with Ligero_Proof_GF2_128;
with Ligero_Proof_P256;
with Lagrange_GF2_128;
with Lagrange_P256;
with Ligero_Verifier_GF2_128;
with Ligero_Verifier_P256;
with Circuit_Reader_GF2_128;
with Circuit_Reader_P256;
with Proof_Writer_GF2_128;
with Proof_Writer_P256;
with Sumcheck_Prover_GF2_128;
with Sumcheck_Prover_P256;

procedure Prover_KAT is

   package TIO renames Ada.Text_IO;

   Default_File : constant String := "tests/vectors/sumcheck_prover.txt";

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

   type Byte_Array_Access is access Byte_Array;
   procedure Free is
     new Ada.Unchecked_Deallocation (Byte_Array, Byte_Array_Access);

   function To_Bytes (S : String) return Byte_Array_Access is
      R : Byte_Array_Access;
   begin
      if S'Length mod 2 /= 0 then
         raise Parse_Error with "odd number of hex digits";
      end if;
      R := new Byte_Array (0 .. S'Length / 2 - 1);
      for I in R'Range loop
         R (I) := Shift_Left (Hex_Digit (S (S'First + 2 * I)), 4)
                  or Hex_Digit (S (S'First + 2 * I + 1));
      end loop;
      return R;
   end To_Bytes;

   function To_Label (S : String) return Byte_Array is
      R : Byte_Array (0 .. S'Length - 1);
   begin
      for I in R'Range loop
         R (I) := Character'Pos (S (S'First + I));
      end loop;
      return R;
   end To_Label;

   function GF_To_Element (S : String) return GF2_128.Element is
      R : GF2_128.Element := GF2_128.Zero;
      L : GF2_128.Limb_Index;
   begin
      if S'Length /= 32 then
         raise Parse_Error with "expected 32 hex digits, got '" & S & "'";
      end if;
      for I in 0 .. 31 loop
         L := (if I < 16 then 1 else 0);
         R.Limbs (L) := Shift_Left (R.Limbs (L), 4)
                        or Unsigned_64 (Hex_Digit (S (S'First + I)));
      end loop;
      return R;
   end GF_To_Element;

   function P_To_Element (S : String) return P256_Field.Element is
      R : P256_Field.Limb_Array := [others => 0];
      L : P256_Field.Limb_Index;
   begin
      if S'Length /= 64 then
         raise Parse_Error with "expected 64 hex digits, got '" & S & "'";
      end if;
      for I in 0 .. 63 loop
         L := P256_Field.Limb_Index (3 - I / 16);
         R (L) := Shift_Left (R (L), 4)
                  or Unsigned_64 (Hex_Digit (S (S'First + I)));
      end loop;
      if not P256_Field.Is_Canonical (R) then
         raise Parse_Error with "value not below p: " & S;
      end if;
      return (Limbs => R);
   end P_To_Element;

   Max_Fields : constant := 512;
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

   generic
      with package FS is new Field_Signature (<>);
      with package SA is new Sumcheck_Algebra (F => FS);
      with package SE is new Sumcheck_Expression (SA => SA);
      with package SV is new Sumcheck_Verifier (SA => SA, SE => SE);
      with package ST is new Sumcheck_Transcript
        (SA => SA, SE => SE, SV => SV);
      with package LP is new Ligero_Proof (SA => SA);
      with package L is new Lagrange (F => FS);
      with package LV is new Ligero_Verifier (ST => ST, LP => LP, L => L);
      with package CR is new Circuit_Reader (SA => SA, others => <>);
      with package PW is new Proof_Writer (LV => LV);
      with package SPR is new Sumcheck_Prover (ST => ST, others => <>);
      with function To_Element (S : String) return SA.Element;
   procedure Check_Sumcheck
     (Name  : String;
      F     : access function (K : Positive) return String;
      Count : Natural);

   procedure Check_Sumcheck
     (Name  : String;
      F     : access function (K : Positive) return String;
      Count : Natural)
   is
      use type Circuit_Status.Status;
      use SA;
      use type FS.Element;
      use type SV.Challenges;
      Seed  : constant Unsigned_64 := Unsigned_64'Value (F (4));
      Label : constant Byte_Array := To_Label (F (5));
      Root  : Byte_Array_Access := To_Bytes (F (6));
      Circ  : Byte_Array_Access := To_Bytes (F (7));
      Nwit  : constant Natural := Natural'Value (F (8));
      Npads : constant Natural := Natural'Value (F (9 + Nwit));
      Want  : Byte_Array_Access := To_Bytes (F (10 + Nwit + Npads));
      C     : CR.Circuit_Access;
      H     : CR.Header;
      CSt   : Circuit_Status.Status;
   begin
      if Count /= 10 + Nwit + Npads or else Root'Length /= 32 then
         raise Parse_Error with "sumcheck: field count or root";
      end if;
      CR.Read (Circ.all, C, H, CSt);
      if CSt /= Circuit_Status.Ok then
         Report_Failure (Name & ": circuit " & CSt'Image);
         return;
      end if;
      declare
         W     : SA.Element_Array (0 .. Nwit - 1);
         Wires : SA.Element_Array (0 .. SA.Total_Wires (C.all) - 1) :=
           [others => SA.Zero];
         Pads  : SA.Element_Array (0 .. SPR.Pad_Total (C.all) - 1);
         Proof : SV.Sumcheck_Proof (Last => SV.Proof_Total (C.all) - 1);
         Ch    : SV.Challenges (Last => SV.Chal_Total (C.all) - 1);
         Out_B : Byte_Array (0 .. PW.Sumcheck_Len (C.all) - 1);
         Ok    : Boolean;
      begin
         if Nwit /= C.Ninput or else Npads /= Pads'Length then
            Report_Failure (Name & ": witness or pad count");
            CR.Free (C);
            return;
         end if;
         for I in W'Range loop
            W (I) := To_Element (F (9 + I));
         end loop;
         SA.Eval_Circuit (C.all, W, Wires, Ok);
         if not Ok then
            Report_Failure (Name & ": the witness does not satisfy");
            CR.Free (C);
            return;
         end if;
         Transcript.Reset (Label);
         Transcript.Write_Bytes (Root.all);
         ST.Write_Sumcheck_Statement (H.Id, C.all, W (0 .. C.Npublic - 1));
         Simple_Rng.Seed (Seed);
         SPR.Sample_Pads (C.all, Pads);
         for I in Pads'Range loop
            if Pads (I) /= To_Element (F (10 + Nwit + I)) then
               Report_Failure (Name & ": pad" & I'Image & " differs");
               CR.Free (C);
               return;
            end if;
         end loop;
         SPR.Prove (C.all, Wires, Pads, Proof, Ch);
         PW.Write_Sumcheck_Proof (C.all, Proof, Out_B);
         if Out_B'Length /= Want'Length then
            Report_Failure (Name & ": proof length" & Out_B'Length'Image
                            & ", expected" & Want'Length'Image);
            CR.Free (C);
            return;
         end if;
         for I in Out_B'Range loop
            if Out_B (I) /= Want (I) then
               Report_Failure (Name & ": proof byte" & I'Image
                               & " differs (element"
                               & Natural'Image (I / LP.Size) & ")");
               CR.Free (C);
               return;
            end if;
         end loop;
         --  The verifier side on the proof just made.
         declare
            use type ST.Status;
            Npriv : constant Natural := C.Ninput - C.Npublic;
            Ch2   : SV.Challenges (Last => Ch.Last);
            VSt   : ST.Status;
            A     : SV.Ligero_Terms (Max => SV.A_Bound (C.all) - 1);
            Bv    : SA.Element_Array (0 .. C.Last_Layer + 1);
            Lqc   : SV.Lqc_Array (0 .. C.Last_Layer);
            Wv    : constant SA.Element_Array
              (0 .. SV.Witness_Count (C.all) - 1) :=
              W (C.Npublic .. C.Ninput - 1) & Pads;
            Acc   : SA.Element_Array (Bv'Range) := [others => SA.Zero];
         begin
            ST.Replay_Challenges
              (Label, Root.all, H.Id, C.all, W (0 .. C.Npublic - 1),
               Proof, Ch2, VSt);
            if VSt /= ST.Ok then
               Report_Failure (Name & ": replay " & VSt'Image);
               CR.Free (C);
               return;
            end if;
            if Ch2 /= Ch then
               Report_Failure (Name & ": the replayed challenges differ "
                               & "from the recorded ones");
               CR.Free (C);
               return;
            end if;
            SV.Verifier_Core (C.all, W (0 .. C.Npublic - 1), Proof, Ch,
                              A, Bv, Lqc);
            if Wv'Length /= Npriv + Npads then
               Report_Failure (Name & ": witness vector length");
               CR.Free (C);
               return;
            end if;
            for K in 0 .. A.Count - 1 loop
               Acc (A.Constraint (K)) :=
                 Acc (A.Constraint (K)) + A.Coeff (K) * Wv (A.Witness (K));
            end loop;
            for J in Bv'Range loop
               if Acc (J) + Bv (J) /= SA.Zero then
                  Report_Failure (Name & ": linear constraint" & J'Image
                                  & " not satisfied");
                  CR.Free (C);
                  return;
               end if;
            end loop;
            for Q in Lqc'Range loop
               if Wv (Lqc (Q).X) * Wv (Lqc (Q).Y) /= Wv (Lqc (Q).Z) then
                  Report_Failure (Name & ": quadratic constraint" & Q'Image
                                  & " not satisfied");
                  CR.Free (C);
                  return;
               end if;
            end loop;
            TIO.Put_Line ("  " & Name & ":" & Npads'Image & " pads and"
                          & Natural'Image (Out_B'Length)
                          & " proof bytes as the reference;"
                          & Natural'Image (Bv'Length) & " linear and"
                          & Natural'Image (Lqc'Length)
                          & " quadratic constraints satisfied");
         end;
         Passed := Passed + 1;
      end;
      CR.Free (C);
      Free (Root);
      Free (Circ);
      Free (Want);
   end Check_Sumcheck;

   procedure Check_GF is new Check_Sumcheck
     (FS => Field_GF2_128.Sig,
      SA => Sumcheck_Algebra_GF2_128, SE => Sumcheck_Expression_GF2_128,
      SV => Sumcheck_Verifier_GF2_128, ST => Sumcheck_Transcript_GF2_128,
      LP => Ligero_Proof_GF2_128, L => Lagrange_GF2_128,
      LV => Ligero_Verifier_GF2_128, CR => Circuit_Reader_GF2_128,
      PW => Proof_Writer_GF2_128, SPR => Sumcheck_Prover_GF2_128,
      To_Element => GF_To_Element);
   procedure Check_P is new Check_Sumcheck
     (FS => Field_P256.Sig,
      SA => Sumcheck_Algebra_P256, SE => Sumcheck_Expression_P256,
      SV => Sumcheck_Verifier_P256, ST => Sumcheck_Transcript_P256,
      LP => Ligero_Proof_P256, L => Lagrange_P256,
      LV => Ligero_Verifier_P256, CR => Circuit_Reader_P256,
      PW => Proof_Writer_P256, SPR => Sumcheck_Prover_P256,
      To_Element => P_To_Element);

   procedure Check_Line (Line : String) is
      Fields : Field_Array;
      Count  : Natural;

      function F (K : Positive) return String is
      begin
         if K > Count then
            raise Parse_Error with "missing field" & K'Image;
         end if;
         return Line (Fields (K).Lo .. Fields (K).Hi);
      end F;
   begin
      Split (Line, Fields, Count);
      if Count = 0 then
         return;
      end if;
      if F (1) /= "sumcheck" then
         raise Parse_Error with "unknown op " & F (1);
      end if;
      if F (3) = "gf2_128" then
         Check_GF (F (2), F'Access, Count);
      elsif F (3) = "p256" then
         Check_P (F (2), F'Access, Count);
      else
         raise Parse_Error with "unknown field " & F (3);
      end if;
   exception
      when E : Parse_Error =>
         Report_Failure (Ada.Exceptions.Exception_Message (E));
      when E : others =>
         Report_Failure
           ("exception " & Ada.Exceptions.Exception_Information (E));
   end Check_Line;

   procedure Run_File (Path : String) is
      File : TIO.File_Type;
   begin
      TIO.Put_Line ("Prover known-answer tests: " & Path);
      TIO.Open (File, TIO.In_File, Path);
      Line_No := 0;
      while not TIO.End_Of_File (File) loop
         declare
            Line : constant String := TIO.Get_Line (File);
         begin
            Line_No := Line_No + 1;
            if Line'Length > 0 and then Line (Line'First) /= '#' then
               Check_Line (Line);
            end if;
         end;
      end loop;
      TIO.Close (File);
   end Run_File;

begin
   if Ada.Command_Line.Argument_Count = 0 then
      Run_File (Default_File);
   else
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         Run_File (Ada.Command_Line.Argument (I));
      end loop;
   end if;
   TIO.Put_Line ("passed" & Passed'Image & ", failed" & Failed'Image);
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end Prover_KAT;
