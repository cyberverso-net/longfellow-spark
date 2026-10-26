pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;
with Interfaces; use Interfaces;
with Merkle;

package body Zk_Prover is

   --  The predicate of Circuit is checked where a circuit enters the
   --  program. Inside this body every predicate check is proved by
   --  GNATprove, and the property does not depend on the formal Fill.
   --  The instances for the command line, compiled with checks (ADR
   --  0068), would otherwise scan the whole circuit at every call that
   --  passes it, once per layer.
   pragma Suppress (Predicate_Check);

   use LPR.LV.ST.SA.F;
   package SV renames LPR.LV.ST.SV;
   package LP renames LPR.LV.LP;

   subtype Index is LPR.LV.Index;

   -------------------------------------------------------------------
   --  Pad_Off with a base is the base plus Pad_Off from zero
   -------------------------------------------------------------------

   procedure Lemma_Pad_Shift (C : Circuit; J : Natural; Base : Natural) with
     Ghost, Global => null,
     Pre  => J <= C.Last_Layer + 1 and then Base <= LPR.LV.ST.SA.Max_Wires,
     Post => SV.Pad_Off (C, J, Base) = Base + SV.Pad_Off (C, J, 0),
     Subprogram_Variant => (Decreases => J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", SV.Pad_Off);
   begin
      if J > 0 then
         Lemma_Pad_Shift (C, J - 1, Base);
         SV.Lemma_Pad_Step (C, J - 1, Base);
         SV.Lemma_Pad_Step (C, J - 1, 0);
      end if;
   end Lemma_Pad_Shift;

   --  The wires buffer holds at least the inputs: Total_Wires = Off (C,
   --  Last_Layer + 2) = Off (C, Last_Layer + 1) + Ninput.
   procedure Lemma_Wires_Cover (C : Circuit) with
     Ghost, Global => null,
     Post => LPR.LV.ST.SA.Total_Wires (C) >= C.Ninput
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         LPR.LV.ST.SA.Off);
   begin
      null;
   end Lemma_Wires_Cover;

   -------------------------------------------------------------------
   --  The working set (ADR 0047)
   -------------------------------------------------------------------

   type Work
     (Wires_Last, Pads_Last, Wv_Last, Lqc_Last : Index;
      Proof_Last, Chal_Last, Terms_Max, B_Last  : Index;
      Ldt_Last, Linear_Last, Low_Last, High_Last, Nonce_Last, Col_Last : Index;
      Path_Last : Merkle.Node_Index)
   is record
      Wires  : Element_Array (0 .. Wires_Last);
      Pads   : Element_Array (0 .. Pads_Last);
      Wv     : Element_Array (0 .. Wv_Last);
      Lqc    : SV.Lqc_Array (0 .. Lqc_Last);
      Lqc2   : SV.Lqc_Array (0 .. Lqc_Last);
      BQ     : Element_Array (0 .. Lqc_Last);
      SProof : SV.Sumcheck_Proof (Last => Proof_Last);
      Ch     : SV.Challenges (Last => Chal_Last);
      A      : SV.Ligero_Terms (Max => Terms_Max);
      Bv     : Element_Array (0 .. B_Last);
      Lig    : LP.Proof (Ldt_Last, Linear_Last, Low_Last, High_Last,
                         Nonce_Last, Col_Last, Path_Last);
   end record;

   type Work_Access is access Work;

   procedure Free_Work is new Ada.Unchecked_Deallocation (Work, Work_Access);

   procedure Free_Com is
     new Ada.Unchecked_Deallocation (LPR.Commitment, LPR.Commitment_Access);

   function Work_Shape
     (Wk : Work; C : Circuit; G : Valid_Geometry) return Boolean
   is
     (Wk.Wires_Last + 1 = LPR.LV.ST.SA.Total_Wires (C)
      and then Wk.Pads_Last + 1 = SPR.Pad_Total (C)
      and then Wk.Wv_Last + 1 = Witness_Count (C)
      and then Wk.Lqc_Last = C.Last_Layer
      and then Wk.Proof_Last + 1 = SV.Proof_Total (C)
      and then Wk.Chal_Last + 1 = SV.Chal_Total (C)
      and then Wk.Terms_Max = SV.A_Bound (C)
      and then Wk.B_Last = C.Last_Layer + 1
      and then Wk.Ldt_Last + 1 = G.Block_Len
      and then Wk.Linear_Last + 1 = G.Dblock_Len
      and then Wk.Low_Last + 1 = G.Num_Queries
      and then Wk.High_Last + 1 = G.Dblock_Len - G.Block_Len
      and then Wk.Nonce_Last + 1 = G.Num_Queries
      and then Wk.Col_Last + 1 = LP.Opened (G)
      and then Wk.Path_Last + 1 = 2 * Num_Leaves (G))
   with Global => null, Pre => LPR.Prover_Fits (G);

   --  The working set, allocated and zeroed.
   procedure Allocate_Work
     (C : Circuit; G : Valid_Geometry; Wk : out Work_Access)
   with
     Pre  => LPR.Prover_Fits (G) and then C.Ninput >= 1,
     Post => Wk /= null and then Work_Shape (Wk.all, C, G)
   is
   begin
      Lemma_Wires_Cover (C);
      Wk := new Work'
        (Wires_Last  => LPR.LV.ST.SA.Total_Wires (C) - 1,
         Pads_Last   => SPR.Pad_Total (C) - 1,
         Wv_Last     => Witness_Count (C) - 1,
         Lqc_Last    => C.Last_Layer,
         Proof_Last  => SV.Proof_Total (C) - 1,
         Chal_Last   => SV.Chal_Total (C) - 1,
         Terms_Max   => SV.A_Bound (C),
         B_Last      => C.Last_Layer + 1,
         Ldt_Last    => G.Block_Len - 1,
         Linear_Last => G.Dblock_Len - 1,
         Low_Last    => G.Num_Queries - 1,
         High_Last   => G.Dblock_Len - G.Block_Len - 1,
         Nonce_Last  => G.Num_Queries - 1,
         Col_Last    => LP.Opened (G) - 1,
         Path_Last   => 2 * Num_Leaves (G) - 1,
         Wires       => [others => Zero],
         Pads        => [others => Zero],
         Wv          => [others => Zero],
         Lqc         => [others => (X => 0, Y => 0, Z => 0)],
         Lqc2        => [others => (X => 0, Y => 0, Z => 0)],
         BQ          => [others => Zero],
         SProof      => (Last => SV.Proof_Total (C) - 1,
                         Evals => [others => Zero]),
         Ch          => (Last        => SV.Chal_Total (C) - 1,
                         G           => [others => Zero],
                         Layer       => [others => Zero],
                         Alpha_Input => Zero),
         A           => (Max        => SV.A_Bound (C),
                         Count      => 0,
                         Coeff      => [others => Zero],
                         Constraint => [others => 0],
                         Witness    => [others => 0]),
         Bv          => [others => Zero],
         Lig         => (Ldt_Last    => G.Block_Len - 1,
                         Linear_Last => G.Dblock_Len - 1,
                         Low_Last    => G.Num_Queries - 1,
                         High_Last   => G.Dblock_Len - G.Block_Len - 1,
                         Nonce_Last  => G.Num_Queries - 1,
                         Col_Last    => LP.Opened (G) - 1,
                         Path_Last   => 2 * Num_Leaves (G) - 1,
                         Ldt_Poly    => [others => Zero],
                         Linear_Poly => [others => Zero],
                         Quad_Low    => [others => Zero],
                         Quad_High   => [others => Zero],
                         Nonces      => [others => [others => 0]],
                         Columns     => [others => Zero],
                         Path        => [others => [others => 0]],
                         Path_Count  => 0));
   end Allocate_Work;

   -------------------------------------------------------------------
   --  The subfield check (ADR 0049, 0051)
   -------------------------------------------------------------------

   --  The first Count private inputs, projected on the subfield and
   --  re-injected, equal themselves; the differences are accumulated in
   --  one mask over the bytes of the two encodings.
   function Prefix_In_Subfield
     (C : Circuit; Inputs : Element_Array; Count : Natural) return Boolean
   with
     Global => null,
     Pre    => Inputs'First = 0 and then Inputs'Length = C.Ninput
               and then Count <= C.Ninput - C.Npublic
   is
      Mask : Unsigned_8 := 0;
      E2   : Element;
      Ok2  : Boolean;
   begin
      for I in C.Npublic .. C.Npublic + Count - 1 loop
         From_Subfield_Bytes (To_Subfield_Bytes (Inputs (I)), E2, Ok2);
         if not Ok2 then
            Mask := Mask or 1;
         end if;
         declare
            Bx : constant Byte_Array := To_Bytes (E2);
            By : constant Byte_Array := To_Bytes (Inputs (I));
         begin
            if Bx'Length /= By'Length then
               Mask := Mask or 1;
            else
               for K in Bx'Range loop
                  Mask := Mask or (Bx (K) xor By (By'First + (K - Bx'First)));
               end loop;
            end if;
         end;
      end loop;
      return Mask = 0;
   end Prefix_In_Subfield;

   --  The witnesses the writer projects: the first Sub_Rows WR of the
   --  witness vector; none when the field is its own subfield (the
   --  projection is the identity, P-256).
   function Projected_Count
     (G : Valid_Geometry; Sfb_W : Natural) return Natural
   is
     (if LP.Sub_Size = LP.Size then 0
      else PW.Sub_Rows (G, Sfb_W) * G.Witnesses_Per_Row)
   with Global => null, Pre => LPR.Prover_Fits (G);

   -------------------------------------------------------------------
   --  Prove
   -------------------------------------------------------------------

   procedure Prove
     (Label  : Byte_Array;
      Id     : Bytes_32;
      Sfb    : Natural;
      Cfg    : Config;
      C      : Circuit;
      Inputs : Element_Array;
      B      : out Byte_Array;
      Len    : out Natural;
      St     : out Status)
   is
      G     : constant Valid_Geometry := Geometry_Of (Cfg, C);
      Npriv : constant Natural := C.Ninput - C.Npublic;
      Sfb_W : constant Natural := Boundary_Of (C, Sfb);
      NP    : constant Natural := SPR.Pad_Total (C);
      Wk    : Work_Access;
      Com   : LPR.Commitment_Access;
      Ok_E, Ok_C, Ok_P : Boolean;
   begin
      B   := [others => 0];
      Len := 0;
      if Inputs'Length /= C.Ninput then
         St := Input_Length;
         return;
      end if;
      if C.Npublic > 0 and then Inputs (0) /= LPR.LV.ST.SA.One then
         St := Input_Not_One;
         return;
      end if;
      pragma Assert
        (G.Num_Quad_Rows
         = (C.Last_Layer + 1 + G.Witnesses_Per_Row - 1)
           / G.Witnesses_Per_Row);
      Lemma_Pad_Shift (C, C.Last_Layer + 1, Npriv);
      Allocate_Work (C, G, Wk);

      --  Validation: the circuit is satisfied, the inputs below the
      --  boundary lie in the subfield.
      LPR.LV.ST.SA.Eval_Circuit (C, Inputs, Wk.Wires, Ok_E);
      if Validate and then not Ok_E then
         Free_Work (Wk);
         St := Not_Satisfied;
         return;
      end if;
      if Validate
        and then (Projected_Count (G, Sfb_W) > Npriv
                  or else not Prefix_In_Subfield
                               (C, Inputs, Projected_Count (G, Sfb_W)))
      then
         Free_Work (Wk);
         St := Not_In_Subfield;
         return;
      end if;

      --  commit: the pads, the witness vector, the triples, Ligero.
      SPR.Sample_Pads (C, Wk.Pads);
      for I in 0 .. Npriv - 1 loop
         Wk.Wv (I) := Inputs (C.Npublic + I);
      end loop;
      for K in 0 .. NP - 1 loop
         Wk.Wv (Npriv + K) := Wk.Pads (K);
      end loop;
      SPR.Lqc_Triples (C, Wk.Lqc);
      SV.Lemma_Pads_Below (C);
      LPR.Commit (G, Wk.Wv, Wk.Lqc, Sfb_W, Com, Ok_C);
      if not Ok_C then
         Free_Work (Wk);
         St := Config_Invalid;
         return;
      end if;

      --  prove: the transcript, the sumcheck, the core, Ligero.
      Transcript.Reset (Label);
      Transcript.Write_Bytes (Com.Root);
      LPR.LV.ST.Write_Sumcheck_Statement (Id, C, Inputs (0 .. C.Npublic - 1));
      SPR.Prove (C, Wk.Wires, Wk.Pads, Wk.SProof, Wk.Ch, Wk.BQ);
      SV.Verifier_Core (C, Inputs (0 .. C.Npublic - 1), Wk.SProof, Wk.Ch,
                        Wk.BQ, Wk.A, Wk.Bv, Wk.Lqc2);
      LPR.LV.Lemma_Vector_Len_Covers (G);
      pragma Assert (Wk.Lqc'Length = C.Last_Layer + 1);
      pragma Assert
        (G.Num_Quad_Rows
         = (Wk.Lqc'Length + G.Witnesses_Per_Row - 1) / G.Witnesses_Per_Row);
      LPR.Prove (G, Com.all, Wk.Lqc, Wk.A, Wk.Bv, Default_Statement_Hash,
                 Wk.Lig, Ok_P);
      if not Ok_P then
         Free_Com (Com);
         Free_Work (Wk);
         St := Exhausted;
         return;
      end if;

      --  The bytes.
      Len := PW.Proof_Len (C, G, Sfb_W, Wk.Lig.Path_Count);
      PW.Write_Proof (C, G, Sfb_W, Com.Root, Wk.SProof, Wk.Lig,
                      B (0 .. Len - 1));
      Free_Com (Com);
      Free_Work (Wk);
      St := Ok;
   end Prove;

end Zk_Prover;
