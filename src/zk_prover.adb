pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;
with Interfaces; use Interfaces;

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

   -------------------------------------------------------------------
   --  Pad_Off with a base is the base plus Pad_Off from zero
   -------------------------------------------------------------------

   procedure Lemma_Pad_Shift (S : Shape; J : Natural; Base : Natural) with
     Ghost, Global => null,
     Pre  => J <= S.Last_Layer + 1 and then Base <= LPR.LV.ST.SA.Max_Wires,
     Post => SV.Pad_Off (S, J, Base) = Base + SV.Pad_Off (S, J, 0),
     Subprogram_Variant => (Decreases => J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", SV.Pad_Off);
   begin
      if J > 0 then
         Lemma_Pad_Shift (S, J - 1, Base);
         SV.Lemma_Pad_Step (S, J - 1, Base);
         SV.Lemma_Pad_Step (S, J - 1, 0);
      end if;
   end Lemma_Pad_Shift;

   -------------------------------------------------------------------
   --  The working set (ADR 0047); its type is in the private part of
   --  the specification, so that Committed can hold it.
   -------------------------------------------------------------------

   procedure Free_Work is new Ada.Unchecked_Deallocation (Work, Work_Access);

   procedure Free_Com is
     new Ada.Unchecked_Deallocation (LPR.Commitment, LPR.Commitment_Access);

   procedure Free_Shape is
     new Ada.Unchecked_Deallocation (Shape, Shape_Access);

   --  The full input vector of the evaluation, on the heap.
   procedure Free_Inputs is
     new Ada.Unchecked_Deallocation
       (Element_Array, LPR.LV.ST.SA.Seg_Access);

   --  The quad rows of the geometry of S under Cfg, from Make's
   --  postcondition with NQ = S.Last_Layer + 1, in a context of its
   --  own: stated inside the phases, the assertion reached the step
   --  limit in one instance or the other.
   procedure Lemma_Quad_Rows (Cfg : Config; S : Shape) with
     Ghost,
     Global => null,
     Pre    => Valid (Cfg),
     Post   =>
       Geometry_Of (Cfg, S).Num_Quad_Rows
       = (S.Last_Layer + 1 + Geometry_Of (Cfg, S).Witnesses_Per_Row - 1)
         / Geometry_Of (Cfg, S).Witnesses_Per_Row
   is
   begin
      null;
   end Lemma_Quad_Rows;

   --  The working set, allocated and zeroed.
   procedure Allocate_Work
     (S : Shape; G : Valid_Geometry; Wk : out Work_Access)
   with
     Pre  => LPR.Prover_Fits (G) and then S.Ninput >= 1,
     Post => Wk /= null and then Work_Shape (Wk.all, S, G)
   is
   begin
      Wk := new Work'
        (Pads_Last   => SPR.Pad_Total (S) - 1,
         Wv_Last     => Witness_Count (S) - 1,
         Lqc_Last    => S.Last_Layer,
         Proof_Last  => SV.Proof_Total (S) - 1,
         Chal_Last   => SV.Chal_Total (S) - 1,
         Terms_Max   => SV.A_Bound (S),
         B_Last      => S.Last_Layer + 1,
         Ldt_Last    => G.Block_Len - 1,
         Linear_Last => G.Dblock_Len - 1,
         Low_Last    => G.Num_Queries - 1,
         High_Last   => G.Dblock_Len - G.Block_Len - 1,
         Nonce_Last  => G.Num_Queries - 1,
         Col_Last    => LP.Opened (G) - 1,
         Path_Last   => 2 * Num_Leaves (G) - 1,
         Pads        => [others => Zero],
         Wv          => [others => Zero],
         Lqc         => [others => (X => 0, Y => 0, Z => 0)],
         Lqc2        => [others => (X => 0, Y => 0, Z => 0)],
         BQ          => [others => Zero],
         SProof      => (Last => SV.Proof_Total (S) - 1,
                         Evals => [others => Zero]),
         Ch          => (Last        => SV.Chal_Total (S) - 1,
                         G           => [others => Zero],
                         Layer       => [others => Zero],
                         Alpha_Input => Zero),
         A           => (Max        => SV.A_Bound (S),
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
     (Priv : Element_Array; Count : Natural) return Boolean
   with
     Global => null,
     Pre    => Priv'First = 0 and then Count <= Priv'Length
   is
      Mask : Unsigned_8 := 0;
      E2   : Element;
      Ok2  : Boolean;
   begin
      for I in 0 .. Count - 1 loop
         From_Subfield_Bytes (To_Subfield_Bytes (Priv (I)), E2, Ok2);
         if not Ok2 then
            Mask := Mask or 1;
         end if;
         declare
            Bx : constant Byte_Array := To_Bytes (E2);
            By : constant Byte_Array := To_Bytes (Priv (I));
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
   --  The two phases (ADR 0085), and Prove as their composition
   -------------------------------------------------------------------

   procedure Release (C : in out Committed) is
   begin
      if C.Wk /= null then
         Free_Work (C.Wk);
      end if;
      if C.Com /= null then
         Free_Com (C.Com);
      end if;
      if C.S /= null then
         Free_Shape (C.S);
      end if;
   end Release;

   procedure Commit
     (Sfb  : Natural;
      Cfg  : Config;
      P    : Packed_Circuit;
      Priv : Element_Array;
      C    : out Committed;
      St   : out Status)
   is
      S     : constant Shape := Shape_Of (P);
      G     : constant Valid_Geometry := Geometry_Of (Cfg, S);
      Npriv : constant Natural := P.Ninput - P.Npublic;
      Sfb_W : constant Natural := Boundary_Of (S, Sfb);
      NP    : constant Natural := SPR.Pad_Total (S);
      Wk    : Work_Access;
      Com   : LPR.Commitment_Access;
      Ok_C  : Boolean;
   begin
      C := (Wk => null, Com => null, S => null, Sfb_W => 0);
      if Priv'Length /= Npriv then
         St := Input_Length;
         return;
      end if;
      pragma Assert (S.Last_Layer = P.Last_Layer);
      pragma Assert (S.Ninput = P.Ninput and then S.Npublic = P.Npublic);
      --  The quad rows of the geometry, from Make's postcondition in
      --  the shape's terms, then in the circuit's.
      Lemma_Quad_Rows (Cfg, S);
      pragma Assert
        (G.Num_Quad_Rows
         = (S.Last_Layer + 1 + G.Witnesses_Per_Row - 1)
           / G.Witnesses_Per_Row);
      pragma Assert
        (G.Num_Quad_Rows
         = (P.Last_Layer + 1 + G.Witnesses_Per_Row - 1)
           / G.Witnesses_Per_Row);
      --  The witnesses the writer will project lie in the subfield
      --  (ADR 0049, 0051); the satisfiability check needs the public
      --  inputs and belongs to Prove_Committed.
      if Validate
        and then (Projected_Count (G, Sfb_W) > Npriv
                  or else not Prefix_In_Subfield
                               (Priv, Projected_Count (G, Sfb_W)))
      then
         St := Not_In_Subfield;
         return;
      end if;
      Lemma_Pad_Shift (S, P.Last_Layer + 1, Npriv);
      Allocate_Work (S, G, Wk);

      --  commit: the pads, the witness vector, the triples, Ligero.
      SPR.Sample_Pads (S, Wk.Pads);
      for I in 0 .. Npriv - 1 loop
         Wk.Wv (I) := Priv (I);
      end loop;
      for K in 0 .. NP - 1 loop
         Wk.Wv (Npriv + K) := Wk.Pads (K);
      end loop;
      SPR.Lqc_Triples (S, Wk.Lqc);
      SV.Lemma_Pads_Below (S);
      pragma Assert (Wk.Lqc'Length = P.Last_Layer + 1);
      LPR.Commit (G, Wk.Wv, Wk.Lqc, Sfb_W, Com, Ok_C);
      if not Ok_C then
         Free_Work (Wk);
         St := Config_Invalid;
         return;
      end if;
      --  The root, on the transcript as it is (the reference's
      --  LigeroProver::commit writes it at this point).
      Transcript.Write_Bytes (Com.Root);
      C  := (Wk => Wk, Com => Com, S => new Shape'(S), Sfb_W => Sfb_W);
      St := Ok;
   end Commit;

   procedure Prove_Committed
     (Id  : Bytes_32;
      Sfb : Natural;
      Cfg : Config;
      P   : Packed_Circuit;
      Pub : Element_Array;
      C   : in out Committed;
      B   : out Byte_Array;
      Len : out Natural;
      St  : out Status)
   is
      S     : constant Shape := Shape_Of (P);
      G     : constant Valid_Geometry := Geometry_Of (Cfg, S);
      Npriv : constant Natural := P.Ninput - P.Npublic;
      Sfb_W : constant Natural := Boundary_Of (S, Sfb);
      Segs  : LPR.LV.ST.SA.Seg_Array_Access;
      Full  : LPR.LV.ST.SA.Seg_Access;
      Ok_E, Ok_P : Boolean;
   begin
      B   := [others => 0];
      Len := 0;
      if Pub'Length /= P.Npublic then
         Release (C);
         St := Input_Length;
         return;
      end if;
      if P.Npublic > 0 and then Pub (0) /= LPR.LV.ST.SA.One then
         Release (C);
         St := Input_Not_One;
         return;
      end if;
      pragma Assert (S.Last_Layer = P.Last_Layer);
      pragma Assert (S.Ninput = P.Ninput and then S.Npublic = P.Npublic);
      --  The quad rows of the geometry, from Make's postcondition in
      --  the shape's terms, then in the circuit's.
      Lemma_Quad_Rows (Cfg, S);
      pragma Assert
        (G.Num_Quad_Rows
         = (S.Last_Layer + 1 + G.Witnesses_Per_Row - 1)
           / G.Witnesses_Per_Row);
      pragma Assert
        (G.Num_Quad_Rows
         = (P.Last_Layer + 1 + G.Witnesses_Per_Row - 1)
           / G.Witnesses_Per_Row);

      --  Validation: the circuit is satisfied by the public inputs and
      --  the private ones of the commitment, evaluated together. The
      --  wires come one heap segment per layer (ADR 0080, block 4);
      --  Sumcheck_Prover.Prove frees each as its layer is proved, and
      --  the array goes right after.
      Full := new Element_Array'(0 .. P.Ninput - 1 => Zero);
      for I in 0 .. P.Npublic - 1 loop
         Full (I) := Pub (I);
      end loop;
      for I in 0 .. Npriv - 1 loop
         Full (P.Npublic + I) := C.Wk.Wv (I);
      end loop;
      LPR.LV.ST.SA.Allocate_Segs (S, Segs);
      PE.Eval_Circuit (P, Full.all, Segs.all, Ok_E);
      Free_Inputs (Full);
      if Validate and then not Ok_E then
         LPR.LV.ST.SA.Release_Segs (Segs);
         Release (C);
         St := Not_Satisfied;
         return;
      end if;

      --  prove: the statement, the sumcheck, the core, Ligero.
      LPR.LV.ST.Write_Sumcheck_Statement (Id, S, Pub);
      SPR.Prove (P, Segs.all, C.Wk.Pads, C.Wk.SProof, C.Wk.Ch, C.Wk.BQ);
      LPR.LV.ST.SA.Release_Segs (Segs);
      --  The bound quads the core receives are those of the challenges
      --  (ADR 0071), from the prover's own sumcheck, on the expansion of
      --  the packed circuit; the core reads the shape only.
      pragma Assert
        (Proof_Only =>
           (for all J in 0 .. P.Last_Layer =>
              Same (C.Wk.BQ (J), SV.BQ_Ref (SPR.Exp (P), C.Wk.Ch, J))));
      SV.Verifier_Core (S, Pub, C.Wk.SProof, C.Wk.Ch, C.Wk.BQ,
                        C.Wk.A, C.Wk.Bv, C.Wk.Lqc2);
      --  The triples of the commitment, restated for the proof: their
      --  values are those of Lqc_Triples, which the record does not
      --  carry across the phases.
      SPR.Lqc_Triples (S, C.Wk.Lqc);
      Lemma_Pad_Shift (S, P.Last_Layer + 1, Npriv);
      SV.Lemma_Pads_Below (S);
      LPR.LV.Lemma_Vector_Len_Covers (G);
      pragma Assert (C.Wk.Lqc'Length = P.Last_Layer + 1);
      pragma Assert
        (G.Num_Quad_Rows
         = (C.Wk.Lqc'Length + G.Witnesses_Per_Row - 1)
           / G.Witnesses_Per_Row);
      LPR.Prove (G, C.Com.all, C.Wk.Lqc, C.Wk.A, C.Wk.Bv,
                 Default_Statement_Hash, C.Wk.Lig, Ok_P);
      if not Ok_P then
         Release (C);
         St := Exhausted;
         return;
      end if;

      --  The bytes.
      Len := PW.Proof_Len (S, G, Sfb_W, C.Wk.Lig.Path_Count);
      PW.Write_Proof (S, G, Sfb_W, C.Com.Root, C.Wk.SProof, C.Wk.Lig,
                      B (0 .. Len - 1));
      Release (C);
      St := Ok;
   end Prove_Committed;

   procedure Prove
     (Label  : Byte_Array;
      Id     : Bytes_32;
      Sfb    : Natural;
      Cfg    : Config;
      P      : Packed_Circuit;
      Inputs : Element_Array;
      B      : out Byte_Array;
      Len    : out Natural;
      St     : out Status)
   is
      Npriv : constant Natural := P.Ninput - P.Npublic;
      Priv  : LPR.LV.ST.SA.Seg_Access;
      C     : Committed;
   begin
      B   := [others => 0];
      Len := 0;
      if Inputs'Length /= P.Ninput then
         St := Input_Length;
         return;
      end if;
      if P.Npublic > 0 and then Inputs (0) /= LPR.LV.ST.SA.One then
         St := Input_Not_One;
         return;
      end if;
      --  The private inputs as their own array, indexed from 0.
      Priv := new Element_Array'(0 .. Npriv - 1 => Zero);
      for I in 0 .. Npriv - 1 loop
         Priv (I) := Inputs (P.Npublic + I);
      end loop;
      Transcript.Reset (Label);
      Commit (Sfb, Cfg, P, Priv.all, C, St);
      Free_Inputs (Priv);
      if St /= Ok then
         return;
      end if;
      Prove_Committed (Id, Sfb, Cfg, P, Inputs (0 .. P.Npublic - 1),
                       C, B, Len, St);
   end Prove;

end Zk_Prover;
