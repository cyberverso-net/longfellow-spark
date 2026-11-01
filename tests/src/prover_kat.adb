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
--  Block 4 adds the Ligero commitment of Section 4.3 (ADR 0053): on
--  the commit lines the pads are drawn, the witness vector assembled
--  (private inputs, then pads), the quadratic triples generated and
--  Ligero_Prover.Commit run under the given configuration; the root,
--  the systematic part of every row and one batch opening
--  (Merkle.Open, then checked with Merkle.Verify on the leaves of the
--  heap) must equal the reference's. On the root lines (tier 1) the
--  same commitment on an upstream circuit and its inputs must give the
--  root stored in the upstream proof file.
--
--  Block 5 adds the complete prover (ADR 0049, 0053): on the prove
--  lines Zk_Prover.Prove runs on a small circuit under the case name as
--  label and must report the expected status; on ok the proof must be
--  accepted by Zk_Verifier (completeness, tested). The byte identity
--  with the upstream proof files is the cli step's (longfellow_prove,
--  release build).
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads
--  the vector files given as arguments (default: sumcheck_prover.txt,
--  ligero_commit.txt and zk_prove.txt under tests/vectors/). Built with
--  -gnata, so the library's executable contracts run.
--
--  File format: '#' comments and blank lines are skipped; otherwise
--    sumcheck <name> <field> <seed> <label> <root> <circuit lfc2>
--             <nwit> <witness...> <npads> <pads...> <proof bytes>
--    commit <name> <field> <seed> <rate_inv> <nreq> <ncol> <circuit>
--           <nin> <inputs...> <root> <nrow> {<k> <row...>} <nidx>
--           <idx...> <npath> <path...>
--    root <name> <field> <seed> <rate_inv> <nreq> <ncol> <circuit>
--         <nin> <inputs...> <root>
--    prove <name> <field> <seed> <rate_inv> <nreq> <ncol> <circuit>
--          <nin> <inputs...> <status>
--  with elements as big-endian hex integers, bytes as hex, and
--  <circuit> as hex or path:<file relative to the repository root>.
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Calendar;
with Ada.Characters.Handling;
with Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with GF2_128;
with P256_Field;
with Transcript;
with Merkle;
with Ligero_Geometry;
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
with Ligero_Prover;
with Zk_Prover;
with Zk_Verifier;
with Prover_Status;
with Verifier_Status;
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
with Ligero_Prover_GF2_128;
with Ligero_Prover_P256;
with Zk_Prover_GF2_128;
with Zk_Prover_P256;
with Zk_Verifier_GF2_128;
with Zk_Verifier_P256;

procedure Prover_KAT is

   package TIO renames Ada.Text_IO;

   Default_File   : constant String := "tests/vectors/sumcheck_prover.txt";
   Default_File_2 : constant String := "tests/vectors/ligero_commit.txt";
   Default_File_3 : constant String := "tests/vectors/zk_prove.txt";

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

   function Read_File (Path : String) return Byte_Array_Access is
      use Ada.Streams;
      use Ada.Streams.Stream_IO;
      F    : File_Type;
      Size : constant Natural := Natural (Ada.Directories.Size (Path));
      S    : Stream_Element_Array (1 .. Stream_Element_Offset (Size));
      Last : Stream_Element_Offset;
      R    : Byte_Array_Access;
   begin
      Open (F, In_File, Path);
      Read (F, S, Last);
      Close (F);
      if Natural (Last) /= Size then
         raise Parse_Error with "short read of " & Path;
      end if;
      R := new Byte_Array (0 .. Size - 1);
      for I in S'Range loop
         R (Natural (I) - 1) := Unsigned_8 (S (I));
      end loop;
      return R;
   end Read_File;

   --  hex bytes, or path:<file>.
   function Load (Spec : String) return Byte_Array_Access is
   begin
      if Spec'Length > 5
        and then Spec (Spec'First .. Spec'First + 4) = "path:"
      then
         return Read_File (Spec (Spec'First + 5 .. Spec'Last));
      else
         return To_Bytes (Spec);
      end if;
   end Load;

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
      return P256_Field.From_Canonical (R);
   end P_To_Element;

   Max_Fields : constant := 8192;
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
      with package LPR is new Ligero_Prover (LV => LV, others => <>);
      with package ZKP is new Zk_Prover (LPR => LPR, SPR => SPR, PW => PW);
      with package ZK is new Zk_Verifier (LV => LV);
      with function To_Element (S : String) return SA.Element;
   procedure Check_Sumcheck
     (Name  : String;
      F     : access function (K : Positive) return String;
      Count : Natural;
      Op    : String);

   procedure Check_Sumcheck
     (Name  : String;
      F     : access function (K : Positive) return String;
      Count : Natural;
      Op    : String)
   is
      use type Circuit_Status.Status;
      use SA;
      use type FS.Element;
      use type SV.Challenges;

      --  The commit and root lines.
      procedure Check_Commit (Root_Only : Boolean) is
         use Ligero_Geometry;
         Seed  : constant Unsigned_64 := Unsigned_64'Value (F (4));
         Cfg   : constant Config :=
           (Rate_Inv    => Positive'Value (F (5)),
            Num_Queries => Positive'Value (F (6)),
            Encoded_Len => Positive'Value (F (7)));
         Circ  : Byte_Array_Access := Load (F (8));
         Nin   : constant Natural := Natural'Value (F (9));
         Want  : Byte_Array_Access := To_Bytes (F (10 + Nin));
         C     : CR.Circuit_Access;
         H     : CR.Header;
         CSt   : Circuit_Status.Status;
         Com   : LPR.Commitment_Access;
         Ok    : Boolean;
         T0    : Ada.Calendar.Time;
         Secs  : Duration;
         use type Ada.Calendar.Time;
      begin
         if Want'Length /= 32 then
            raise Parse_Error with "root: 32 bytes expected";
         end if;
         if not Valid (Cfg) then
            Report_Failure (Name & ": configuration invalid");
            return;
         end if;
         CR.Read (Circ.all, C, H, CSt);
         if CSt /= Circuit_Status.Ok then
            Report_Failure (Name & ": circuit " & CSt'Image);
            return;
         end if;
         if Nin /= C.Ninput then
            Report_Failure (Name & ": input count");
            CR.Free (C);
            return;
         end if;
         declare
            Sh    : constant SA.Shape := SA.Shape_Of (C.all);
            W     : SA.Element_Array (0 .. Nin - 1);
            Pads  : SA.Element_Array (0 .. SPR.Pad_Total (Sh) - 1);
            Lqc   : SV.Lqc_Array (0 .. C.Last_Layer);
            Sfb   : constant Natural :=
              (if H.Subfield_Boundary > C.Npublic
               then H.Subfield_Boundary - C.Npublic else 0);
         begin
            for I in W'Range loop
               W (I) := To_Element (F (10 + I));
            end loop;
            Simple_Rng.Seed (Seed);
            SPR.Sample_Pads (Sh, Pads);
            SPR.Lqc_Triples (Sh, Lqc);
            declare
               Wv : constant SA.Element_Array
                 (0 .. C.Ninput - C.Npublic + Pads'Length - 1) :=
                 W (C.Npublic .. C.Ninput - 1) & Pads;
               G  : constant Valid_Geometry :=
                 Make (Cfg, Wv'Length, Lqc'Length);
               NL : constant Natural := Num_Leaves (G);
            begin
               if Wv'Length /= SV.Witness_Count (Sh) then
                  Report_Failure (Name & ": witness vector length");
                  CR.Free (C);
                  return;
               end if;
               if not LPR.Prover_Fits (G) then
                  Report_Failure (Name & ": the geometry does not fit");
                  CR.Free (C);
                  return;
               end if;
               T0 := Ada.Calendar.Clock;
               LPR.Commit (G, Wv, Lqc, Sfb, Com, Ok);
               Secs := Ada.Calendar.Clock - T0;
               if not Ok then
                  Report_Failure (Name & ": Commit not Ok");
                  CR.Free (C);
                  return;
               end if;
               if Byte_Array (Com.Root) /= Want.all then
                  Report_Failure (Name & ": root differs");
                  LPR.Free (Com);
                  CR.Free (C);
                  return;
               end if;
               if Root_Only then
                  TIO.Put_Line ("  " & Name & ": root of the upstream proof"
                                & " reproduced (" & G.Total_Rows'Image
                                & " rows," & G.Encoded_Len'Image
                                & " columns," & NL'Image & " leaves,"
                                & Duration'Image (Secs) & " s)");
                  LPR.Free (Com);
                  CR.Free (C);
                  Free (Circ);
                  Free (Want);
                  Passed := Passed + 1;
                  return;
               end if;
               --  The systematic part of every row.
               declare
                  P    : Natural := 11 + Nin;
                  Nrow : constant Natural := Natural'Value (F (P));
               begin
                  if Nrow /= G.Total_Rows then
                     Report_Failure (Name & ": row count" & Nrow'Image);
                     LPR.Free (Com);
                     CR.Free (C);
                     return;
                  end if;
                  P := P + 1;
                  for R in 0 .. Nrow - 1 loop
                     declare
                        K : constant Natural := Natural'Value (F (P));
                     begin
                        for X in 0 .. K - 1 loop
                           if Com.Tab (R, X) /= To_Element (F (P + 1 + X))
                           then
                              Report_Failure
                                (Name & ": row" & R'Image & " element"
                                 & X'Image & " differs");
                              LPR.Free (Com);
                              CR.Free (C);
                              return;
                           end if;
                        end loop;
                        P := P + 1 + K;
                     end;
                  end loop;
                  --  The batch opening, against the reference and
                  --  through Merkle.Verify on the heap's leaves.
                  declare
                     Nidx  : constant Natural := Natural'Value (F (P));
                     Idx   : Merkle.Index_Array (0 .. Nidx - 1);
                     Path  : Merkle.Digest_Array (0 .. 2 * NL - 1);
                     Cnt   : Natural;
                     Leaves : Merkle.Digest_Array (0 .. Nidx - 1);
                     Ok2   : Boolean;
                  begin
                     for I in Idx'Range loop
                        Idx (I) := Natural'Value (F (P + 1 + I));
                     end loop;
                     P := P + 1 + Nidx;
                     Merkle.Open (NL, Com.Heap, Idx, Path, Cnt);
                     if Cnt /= Natural'Value (F (P)) then
                        Report_Failure (Name & ": path length" & Cnt'Image
                                        & ", expected " & F (P));
                        LPR.Free (Com);
                        CR.Free (C);
                        return;
                     end if;
                     for I in 0 .. Cnt - 1 loop
                        if Byte_Array (Path (I))
                           /= To_Bytes (F (P + 1 + I)).all
                        then
                           Report_Failure (Name & ": path digest" & I'Image
                                           & " differs");
                           LPR.Free (Com);
                           CR.Free (C);
                           return;
                        end if;
                     end loop;
                     for I in Idx'Range loop
                        Leaves (I) := Com.Heap (NL + Idx (I));
                     end loop;
                     Merkle.Verify (NL, Com.Root, Idx, Leaves,
                                    Path (0 .. Cnt - 1), Ok2);
                     if not Ok2 then
                        Report_Failure (Name & ": Merkle.Verify refuses the"
                                        & " opening");
                        LPR.Free (Com);
                        CR.Free (C);
                        return;
                     end if;
                     TIO.Put_Line ("  " & Name & ": root," & Nrow'Image
                                   & " rows and an opening of" & Cnt'Image
                                   & " digests as the reference ("
                                   & Duration'Image (Secs) & " s)");
                  end;
               end;
               LPR.Free (Com);
            end;
         end;
         CR.Free (C);
         Free (Circ);
         Free (Want);
         Passed := Passed + 1;
      end Check_Commit;

      --  The prove lines (block 5).
      procedure Check_Prove is
         use Ligero_Geometry;
         use type Prover_Status.Status;
         use type Verifier_Status.Status;
         Seed  : constant Unsigned_64 := Unsigned_64'Value (F (4));
         Cfg   : constant Config :=
           (Rate_Inv    => Positive'Value (F (5)),
            Num_Queries => Positive'Value (F (6)),
            Encoded_Len => Positive'Value (F (7)));
         Circ  : Byte_Array_Access := Load (F (8));
         Nin   : constant Natural := Natural'Value (F (9));
         Want  : constant String := F (10 + Nin);
         C     : CR.Circuit_Access;
         H     : CR.Header;
         CSt   : Circuit_Status.Status;
         PSt   : Prover_Status.Status;
         VSt   : Verifier_Status.Status;
         Len   : Natural;
         Label : constant Byte_Array := To_Label (Name);
         T0    : Ada.Calendar.Time;
         Secs  : Duration;
         use type Ada.Calendar.Time;

         function Got (S : String) return Boolean is
           (Ada.Characters.Handling.To_Lower (S) = Want);

         --  The prover of ADR 0053 that skips the checks: its proof of
         --  false inputs must be refused by the verifier.
         package ZKP_U is new Zk_Prover
           (LPR => LPR, SPR => SPR, PW => PW, Validate => False);
      begin
         if Count /= 10 + Nin then
            raise Parse_Error with "prove: field count";
         end if;
         CR.Read (Circ.all, C, H, CSt);
         if CSt /= Circuit_Status.Ok then
            Report_Failure (Name & ": circuit " & CSt'Image);
            return;
         end if;
         if not Valid (Cfg)
           or else not ZKP.Config_Fits (Cfg, SA.Shape_Of (C.all))
         then
            if Got ("config_invalid") then
               TIO.Put_Line ("  " & Name & ": config_invalid as expected");
               Passed := Passed + 1;
            else
               Report_Failure (Name & ": config_invalid, expected " & Want);
            end if;
            CR.Free (C);
            Free (Circ);
            return;
         end if;
         declare
            W   : SA.Element_Array (0 .. Nin - 1);
            Max : constant Natural :=
              ZKP.Max_Proof_Len
                (Cfg, SA.Shape_Of (C.all), H.Subfield_Boundary);
            B   : Byte_Array_Access := new Byte_Array (0 .. Max - 1);
         begin
            for I in W'Range loop
               W (I) := To_Element (F (10 + I));
            end loop;
            Simple_Rng.Seed (Seed);
            T0 := Ada.Calendar.Clock;
            ZKP.Prove (Label, H.Id, H.Subfield_Boundary, Cfg, C.all, W,
                       B.all, Len, PSt);
            Secs := Ada.Calendar.Clock - T0;
            if not Got (PSt'Image) then
               Report_Failure (Name & ": status "
                               & Ada.Characters.Handling.To_Lower (PSt'Image)
                               & ", expected " & Want);
               CR.Free (C);
               Free (B);
               return;
            end if;
            if PSt = Prover_Status.Ok then
               if Nin < C.Npublic then
                  Report_Failure (Name & ": public inputs");
                  CR.Free (C);
                  Free (B);
                  return;
               end if;
               ZK.Verify (Label, H.Id, Cfg, C.all, W (0 .. C.Npublic - 1),
                          B (0 .. Len - 1), VSt);
               if VSt /= Verifier_Status.Ok then
                  Report_Failure (Name & ": the verifier reports "
                                  & VSt'Image & " on the proof");
                  CR.Free (C);
                  Free (B);
                  return;
               end if;
               TIO.Put_Line ("  " & Name & ":" & Len'Image
                             & " bytes, accepted by Zk_Verifier ("
                             & Duration'Image (Secs) & " s)");
            elsif PSt in Prover_Status.Not_Satisfied
                       | Prover_Status.Not_In_Subfield
            then
               Simple_Rng.Seed (Seed);
               ZKP_U.Prove (Label, H.Id, H.Subfield_Boundary, Cfg, C.all, W,
                            B.all, Len, PSt);
               if PSt /= Prover_Status.Ok then
                  Report_Failure (Name & ": the unchecked prover reports "
                                  & PSt'Image);
                  CR.Free (C);
                  Free (B);
                  return;
               end if;
               ZK.Verify (Label, H.Id, Cfg, C.all, W (0 .. C.Npublic - 1),
                          B (0 .. Len - 1), VSt);
               if VSt = Verifier_Status.Ok then
                  Report_Failure (Name & ": the verifier accepts the proof"
                                  & " of false inputs");
                  CR.Free (C);
                  Free (B);
                  return;
               end if;
               TIO.Put_Line ("  " & Name & ": " & Want & " as expected; the"
                             & " unchecked prover's proof refused ("
                             & Ada.Characters.Handling.To_Lower (VSt'Image)
                             & ")");
            else
               TIO.Put_Line ("  " & Name & ": " & Want & " as expected");
            end if;
            Free (B);
         end;
         CR.Free (C);
         Free (Circ);
         Passed := Passed + 1;
      end Check_Prove;

      --  The sumcheck lines (block 3).
      procedure Check_Sum is
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
            Sh    : constant SA.Shape := SA.Shape_Of (C.all);
            W     : SA.Element_Array (0 .. Nwit - 1);
            Wires : SA.Element_Array (0 .. SA.Total_Wires (Sh) - 1) :=
              [others => SA.Zero];
            Pads  : SA.Element_Array (0 .. SPR.Pad_Total (Sh) - 1);
            Proof : SV.Sumcheck_Proof (Last => SV.Proof_Total (Sh) - 1);
            Ch    : SV.Challenges (Last => SV.Chal_Total (Sh) - 1);
            BQ    : SA.Element_Array (0 .. C.Last_Layer);
            Out_B : Byte_Array (0 .. PW.Sumcheck_Len (Sh) - 1);
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
            ST.Write_Sumcheck_Statement (H.Id, Sh, W (0 .. C.Npublic - 1));
            Simple_Rng.Seed (Seed);
            SPR.Sample_Pads (Sh, Pads);
            for I in Pads'Range loop
               if Pads (I) /= To_Element (F (10 + Nwit + I)) then
                  Report_Failure (Name & ": pad" & I'Image & " differs");
                  CR.Free (C);
                  return;
               end if;
            end loop;
            SPR.Prove (C.all, Wires, Pads, Proof, Ch, BQ);
            --  ADR 0071: the bound quad of every layer, from the sumcheck
            --  of the prover, against the verifier's Eval_Bound_Quad_T
            --  (term by term beyond the tables).
            declare
               BQV : SA.Element_Array (0 .. C.Last_Layer);
            begin
               SV.Bound_Quads (C.all, Ch, BQV);
               for J in BQ'Range loop
                  if BQ (J) /= BQV (J) then
                     Report_Failure (Name & ": the bound quad of layer"
                                     & J'Image & " differs from the "
                                     & "verifier's");
                     CR.Free (C);
                     return;
                  end if;
               end loop;
            end;
            --  ADR 0075: the claim of every round, tracked from the
            --  unpadded proof as upstream's layer does (Lagrange at the
            --  challenge, p (1) = claim - p (0)), meets at the end of each
            --  layer the claims times the bound quad, upstream's assert.
            declare
               Cl0, Cl1, Sum, P0, P1, P2v : SA.Element := SA.Zero;
               L : SA.Basis;
            begin
               for J in 0 .. C.Last_Layer loop
                  declare
                     Lw    : constant Natural := C.Layers (J).Logw;
                     Off_P : constant Natural := SV.Proof_Off (Sh, J);
                     Off_C : constant Natural := SV.Chal_Off (Sh, J);
                     Off_D : constant Natural := SV.Pad_Off (Sh, J, 0);
                  begin
                     Sum := Cl0 + Ch.Layer (Off_C) * Cl1;
                     for R in 0 .. Lw - 1 loop
                        for H in 0 .. 1 loop
                           P0  := Proof.Evals (Off_P + 4 * R + 2 * H)
                             + Pads (Off_D + 4 * R + 2 * H);
                           P2v := Proof.Evals (Off_P + 4 * R + 2 * H + 1)
                             + Pads (Off_D + 4 * R + 2 * H + 1);
                           P1  := Sum - P0;
                           L   := SA.Lagrange_Basis
                             (Ch.Layer (Off_C + 2 + 2 * R + H));
                           Sum := L (0) * P0 + L (1) * P1 + L (2) * P2v;
                        end loop;
                     end loop;
                     Cl0 := Proof.Evals (Off_P + 4 * Lw)
                       + Pads (Off_D + 4 * Lw);
                     Cl1 := Proof.Evals (Off_P + 4 * Lw + 1)
                       + Pads (Off_D + 4 * Lw + 1);
                     if Sum /= Cl0 * Cl1 * BQ (J) then
                        Report_Failure (Name & ": the claim tracked over "
                                        & "layer" & J'Image & " differs "
                                        & "from the claims times the "
                                        & "bound quad");
                        CR.Free (C);
                        return;
                     end if;
                  end;
               end loop;
            end;
            PW.Write_Sumcheck_Proof (Sh, Proof, Out_B);
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
            --  Phase D, M1: the dense round polynomial agrees with the
            --  term-by-term one, both hands, on the first round of every
            --  layer at the honest wires (the fast form is tested against
            --  the reference form).
            for J in 0 .. C.Last_Layer loop
               declare
                  NW  : constant Natural := C.Layers (J).NW_In;
                  Seg : constant Natural := SA.Off (Sh, J + 1);
                  T   : constant SA.Term_Array :=
                    C.Terms (C.Layers (J).First .. C.Layers (J).Last);
                  A   : constant SA.Element_Array (0 .. NW - 1) :=
                    Wires (Seg .. Seg + NW - 1);
                  B   : SA.Element_Array (0 .. NW - 1);
                  QW  : SA.Element_Array (0 .. NW - 1);
                  X2  : constant SA.Element :=
                    Pads (Pads'First) * Pads (Pads'Last) + SA.One;
                  E0, E2, D0, D2, Ld, Sum : SA.Element;
               begin
                  for I in B'Range loop
                     B (I) := A (NW - 1 - I) * X2 + SA.One;
                  end loop;
                  for H in SPR.Hand loop
                     SPR.Round_Evals (T, A, NW, B, NW, H, X2, E0, E2);
                     --  ADR 0075: the dense form at the true claim, the
                     --  sum of qw times the active wires.
                     SPR.Round_Evals_Dense
                       (T, A, NW, B, NW, H, X2, SA.Zero, QW, D0, D2, Ld);
                     Sum := SA.Zero;
                     for X in 0 .. NW - 1 loop
                        Sum := Sum + QW (X) * A (X);
                     end loop;
                     SPR.Round_Evals_Dense
                       (T, A, NW, B, NW, H, X2, Sum, QW, D0, D2, Ld);
                     if E0 /= D0 or else E2 /= D2 then
                        Report_Failure (Name & ": layer" & J'Image
                                        & " hand" & H'Image
                                        & ": dense round differs");
                        CR.Free (C);
                        return;
                     end if;
                  end loop;
               end;
            end loop;
            --  The merged terms (bind_g with the eq2 table, the runs
            --  merged, bind_h at every round) give the round polynomial
            --  of the reference terms (Bind_G, Update_Terms), every
            --  round, both hands, at fixed wires and claim points (the
            --  identity is linear in the terms, for any wires).
            declare
               Lv : Natural := CR.Ceil_Lg2 (C.Noutput);
            begin
               for J in 0 .. C.Last_Layer loop
                  declare
                     type Elems_Access is access SA.Element_Array;
                     procedure Free is new Ada.Unchecked_Deallocation
                       (SA.Element_Array, Elems_Access);
                     NW  : constant Natural := C.Layers (J).NW_In;
                     Lw  : constant Natural := C.Layers (J).Logw;
                     Seg : constant Natural := SA.Off (Sh, J + 1);
                     TR  : SA.Term_Array :=
                       C.Terms (C.Layers (J).First .. C.Layers (J).Last);
                     TF  : SA.Term_Array := TR;
                     A   : constant SA.Element_Array (0 .. NW - 1) :=
                       Wires (Seg .. Seg + NW - 1);
                     B   : SA.Element_Array (0 .. NW - 1);
                     QW  : SA.Element_Array (0 .. NW - 1);
                     G0, G1 : SA.Element_Array (0 .. SA.Max_Logw - 1);
                     Al  : constant SA.Element := Pads (Pads'First) + SA.One;
                     Be  : constant SA.Element := Pads (Pads'Last) + Al;
                     X   : SA.Element := Al * Be + SA.One;
                     NT, NB : Natural;
                     E0, E2, D0, D2, L0, L2, Sum : SA.Element;
                  begin
                     for I in B'Range loop
                        B (I) := A (NW - 1 - I) * X + SA.One;
                     end loop;
                     for I in G0'Range loop
                        G0 (I) :=
                          X * Al + Pads (Pads'First + I mod Pads'Length);
                        G1 (I) := G0 (I) * Be + SA.One;
                     end loop;
                     SA.Bind_G (TR, Lv, G0, G1, Al, Be);
                     if Lv <= SA.Max_Bindeq_Log then
                        declare
                           E : Elems_Access := new SA.Element_Array'
                             (0 .. SA.Table_Len (Lv) - 1 => SA.Zero);
                        begin
                           SA.Eq2_Table (Lv, G0, G1, Al, E.all);
                           SV.HQ.Bind_G_T (TF, E.all, Be);
                           Free (E);
                        end;
                     else
                        SA.Bind_G (TF, Lv, G0, G1, Al, Be);
                     end if;
                     SV.HQ.Merge_Runs (TF, NT);
                     for R in 0 .. Lw - 1 loop
                        for H in SPR.Hand loop
                           --  The same claim for both, any claim: the
                           --  identity is linear in the terms.
                           Sum := X * Al;
                           SPR.Round_Evals_Dense
                             (TR, A, NW, B, NW, H, X, Sum, QW, E0, E2, L0);
                           SPR.Round_Evals_Dense
                             (TF (TF'First .. TF'First + NT - 1), A, NW, B,
                              NW, H, X, Sum, QW, D0, D2, L2);
                           if E0 /= D0 or else E2 /= D2 or else L0 /= L2
                           then
                              Report_Failure
                                (Name & ": layer" & J'Image & " round"
                                 & R'Image & " hand" & H'Image
                                 & ": merged terms differ");
                              CR.Free (C);
                              return;
                           end if;
                           SPR.Update_Terms (TR, H, X);
                           SV.HQ.Bind_H
                             (TF (TF'First .. TF'First + NT - 1), H, X, NB);
                           NT := NB;
                           X := X * X + Al;
                        end loop;
                     end loop;
                     Lv := Lw;
                  end;
               end loop;
            end;
            --  The verifier side on the proof just made.
            declare
               use type ST.Status;
               Npriv : constant Natural := C.Ninput - C.Npublic;
               Ch2   : SV.Challenges (Last => Ch.Last);
               VSt   : ST.Status;
               A     : SV.Ligero_Terms (Max => SV.A_Bound (Sh) - 1);
               Bv    : SA.Element_Array (0 .. C.Last_Layer + 1);
               Lqc   : SV.Lqc_Array (0 .. C.Last_Layer);
               Wv    : constant SA.Element_Array
                 (0 .. SV.Witness_Count (Sh) - 1) :=
                 W (C.Npublic .. C.Ninput - 1) & Pads;
               Acc   : SA.Element_Array (Bv'Range) := [others => SA.Zero];
            begin
               ST.Replay_Challenges
                 (Label, Root.all, H.Id, Sh,
                  W (0 .. C.Npublic - 1), Proof, Ch2, VSt);
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
                                 BQ, A, Bv, Lqc);
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
      end Check_Sum;

   begin
      if Op = "commit" then
         Check_Commit (Root_Only => False);
      elsif Op = "root" then
         Check_Commit (Root_Only => True);
      elsif Op = "prove" then
         Check_Prove;
      else
         Check_Sum;
      end if;
   end Check_Sumcheck;

   procedure Check_GF is new Check_Sumcheck
     (FS => Field_GF2_128.Sig,
      SA => Sumcheck_Algebra_GF2_128, SE => Sumcheck_Expression_GF2_128,
      SV => Sumcheck_Verifier_GF2_128, ST => Sumcheck_Transcript_GF2_128,
      LP => Ligero_Proof_GF2_128, L => Lagrange_GF2_128,
      LV => Ligero_Verifier_GF2_128, CR => Circuit_Reader_GF2_128,
      PW => Proof_Writer_GF2_128, SPR => Sumcheck_Prover_GF2_128,
      LPR => Ligero_Prover_GF2_128, ZKP => Zk_Prover_GF2_128,
      ZK => Zk_Verifier_GF2_128, To_Element => GF_To_Element);
   procedure Check_P is new Check_Sumcheck
     (FS => Field_P256.Sig,
      SA => Sumcheck_Algebra_P256, SE => Sumcheck_Expression_P256,
      SV => Sumcheck_Verifier_P256, ST => Sumcheck_Transcript_P256,
      LP => Ligero_Proof_P256, L => Lagrange_P256,
      LV => Ligero_Verifier_P256, CR => Circuit_Reader_P256,
      PW => Proof_Writer_P256, SPR => Sumcheck_Prover_P256,
      LPR => Ligero_Prover_P256, ZKP => Zk_Prover_P256,
      ZK => Zk_Verifier_P256, To_Element => P_To_Element);

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
      if F (1) /= "sumcheck" and then F (1) /= "commit"
        and then F (1) /= "root" and then F (1) /= "prove"
      then
         raise Parse_Error with "unknown op " & F (1);
      end if;
      if F (3) = "gf2_128" then
         Check_GF (F (2), F'Access, Count, F (1));
      elsif F (3) = "p256" then
         Check_P (F (2), F'Access, Count, F (1));
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
      Run_File (Default_File_2);
      Run_File (Default_File_3);
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
