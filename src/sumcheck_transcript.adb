pragma SPARK_Mode (On);

with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Lemmas.Integer_Arithmetic;

package body Sumcheck_Transcript is

   ----------------------------------------------------------------------
   --  Offsets of the stage 3 layouts: one step and monotonicity, from
   --  the hidden recursive definitions (as in sumcheck_verifier.adb).
   ----------------------------------------------------------------------

   procedure Lemma_Chal_Step (C : Circuit; J : Natural) with
     Ghost,
     Global => null,
     Pre    => J <= C.Last_Layer,
     Post   => Chal_Off (C, J + 1) = Chal_Off (C, J) + Chal_Size (C, J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Chal_Off);
   begin
      null;
   end Lemma_Chal_Step;

   procedure Lemma_Chal_Mono (C : Circuit; I, J : Natural) with
     Ghost,
     Global             => null,
     Pre                => I <= J and then J <= C.Last_Layer + 1,
     Post               => Chal_Off (C, I) <= Chal_Off (C, J),
     Subprogram_Variant => (Decreases => J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Chal_Off);
   begin
      if J > I then
         Lemma_Chal_Mono (C, I, J - 1);
      end if;
   end Lemma_Chal_Mono;

   procedure Lemma_Proof_Step (C : Circuit; J : Natural) with
     Ghost,
     Global => null,
     Pre    => J <= C.Last_Layer,
     Post   => Proof_Off (C, J + 1) = Proof_Off (C, J) + Proof_Size (C, J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Proof_Off);
   begin
      null;
   end Lemma_Proof_Step;

   procedure Lemma_Proof_Mono (C : Circuit; I, J : Natural) with
     Ghost,
     Global             => null,
     Pre                => I <= J and then J <= C.Last_Layer + 1,
     Post               => Proof_Off (C, I) <= Proof_Off (C, J),
     Subprogram_Variant => (Decreases => J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Proof_Off);
   begin
      if J > I then
         Lemma_Proof_Mono (C, I, J - 1);
      end if;
   end Lemma_Proof_Mono;

   --  The block of layer J fits in the total.
   procedure Lemma_Layer_Fits (C : Circuit; J : Natural) with
     Ghost,
     Global => null,
     Pre    => J <= C.Last_Layer,
     Post   =>
       Chal_Off (C, J) + Chal_Size (C, J) <= Chal_Total (C)
       and then Proof_Off (C, J) + Proof_Size (C, J) <= Proof_Total (C)
   is
   begin
      Lemma_Chal_Step (C, J);
      Lemma_Chal_Mono (C, J + 1, C.Last_Layer + 1);
      Lemma_Proof_Step (C, J);
      Lemma_Proof_Mono (C, J + 1, C.Last_Layer + 1);
   end Lemma_Layer_Fits;

   ----------------------------------------------------------------------
   --  Serialisation
   ----------------------------------------------------------------------

   function Serialise (Es : Element_Array) return Byte_Array is
      R : Byte_Array (0 .. Es'Length * Size - 1) := [others => 0];
   begin
      for I in 0 .. Es'Length - 1 loop
         R (I * Size .. I * Size + Size - 1) :=
           SA.F.To_Bytes (Es (Es'First + I));
         pragma Loop_Invariant
           (for all K in 0 .. I =>
              R (K * Size .. K * Size + Size - 1)
              = SA.F.To_Bytes (Es (Es'First + K)));
      end loop;
      return R;
   end Serialise;

   ----------------------------------------------------------------------
   --  The sampler
   ----------------------------------------------------------------------

   procedure Sample (E : out Element) is
      Ex0      : constant Boolean := Transcript.Is_Exhausted with Ghost;
      B        : Elt_Bytes;
      Accepted : Boolean;
   begin
      Transcript.Get_Random_Bytes (B);
      SA.F.From_Bytes (B, E, Accepted);
      if SA.F.Sampling_Rejects then
         --  Rejection sampling with no cap (ADR 0030); this loop is
         --  the whole reason Sample is declared possibly
         --  non-terminating for the fields that reject.
         while not Accepted loop
            pragma Loop_Invariant (Ex0 <= Transcript.Is_Exhausted);
            Transcript.Get_Random_Bytes (B);
            SA.F.From_Bytes (B, E, Accepted);
         end loop;
      end if;
   end Sample;

   ----------------------------------------------------------------------
   --  Frames and statement
   ----------------------------------------------------------------------

   procedure Write_Element (E : Element) is
   begin
      Transcript.Write_Element (SA.F.To_Bytes (E));
   end Write_Element;

   procedure Write_Element_Slice (Es : Element_Array) is
   begin
      Transcript.Write_Slice (Es'Length, Serialise (Es));
   end Write_Element_Slice;

   procedure Write_Sumcheck_Statement
     (Id : Bytes_32; C : Circuit; Pub : Element_Array)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Publics_Frame);
      Ex0  : constant Boolean := Transcript.Is_Exhausted with Ghost;
      Base : Byte_Seq with Ghost => SPARKlib_Full;
   begin
      Transcript.Write_Bytes (Id);
      Base := Transcript.Absorbed;
      for I in Pub'Range loop
         Write_Element (Pub (I));
         pragma Loop_Invariant
           (SPARKlib_Full =>
              Ex0 <= Transcript.Is_Exhausted
              and then Byte_Seqs.Logical_Eq
                (Transcript.Absorbed,
                 Publics_Frame (Base, Pub, I - Pub'First + 1)));
      end loop;
      Write_Element (Zero);
      Transcript.Write0 (C.NT);
   end Write_Sumcheck_Statement;

   ----------------------------------------------------------------------
   --  Protocol helpers
   ----------------------------------------------------------------------

   procedure Begin_Circuit (G : out Challenge_Vector) is
      Ex0 : constant Boolean := Transcript.Is_Exhausted with Ghost;
      Q   : Element;
   begin
      for I in 1 .. Max_Logw loop
         pragma Loop_Invariant (Ex0 <= Transcript.Is_Exhausted);
         Sample (Q);
      end loop;
      for I in G'Range loop
         pragma Loop_Invariant (Ex0 <= Transcript.Is_Exhausted);
         Sample (G (I));
      end loop;
   end Begin_Circuit;

   procedure Begin_Layer (Alpha, Beta : out Element) is
   begin
      Sample (Alpha);
      Sample (Beta);
   end Begin_Layer;

   procedure Round_Poly (P0, P2 : Element; Ch : out Element) is
   begin
      Write_Element (P0);
      Write_Element (P2);
      Sample (Ch);
   end Round_Poly;

   procedure End_Layer (Claim0, Claim1 : Element) is
   begin
      Write_Element_Slice (Claims_Pair (Claim0, Claim1));
   end End_Layer;

   ----------------------------------------------------------------------
   --  Replay
   ----------------------------------------------------------------------

   --  One layer: alpha and beta, the 2 logw round challenges, the two
   --  claims absorbed. LP is the layer's block of the padded proof in
   --  the pad order, LC the layer's block of challenges. Indices here
   --  are relative to the blocks, so that the checks are linear in
   --  logw and the transcript contracts weigh on one short loop only.
   procedure Replay_Layer
     (Logw : Logw_Type; LP : Element_Array; LC : out Element_Array)
   with
     Global            => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Always_Terminates => not SA.F.Sampling_Rejects,
     Pre               =>
       LP'First = 0 and then LP'Length = 4 * Logw + 2
       and then LC'First = 0 and then LC'Length = 2 * Logw + 2
   is
      Alpha, Beta : Element;
   begin
      LC := [others => Zero];
      Begin_Layer (Alpha, Beta);
      LC (0) := Alpha;
      LC (1) := Beta;
      for R in 0 .. Logw - 1 loop
         for H in 0 .. 1 loop
            Round_Poly
              (LP (4 * R + 2 * H), LP (4 * R + 2 * H + 1), LC (2 + 2 * R + H));
         end loop;
      end loop;
      End_Layer (LP (4 * Logw), LP (4 * Logw + 1));
   end Replay_Layer;

   procedure Replay_Challenges
     (Label : Byte_Array;
      Root  : Bytes_32;
      Id    : Bytes_32;
      C     : Circuit;
      Pub   : Element_Array;
      Proof : Sumcheck_Proof;
      Ch    : out Challenges;
      St    : out Status)
   is
   begin
      Ch := (Last        => Ch.Last,
             G           => [others => Zero],
             Layer       => [others => Zero],
             Alpha_Input => Zero);
      Transcript.Reset (Label);
      Transcript.Write_Bytes (Root);
      Write_Sumcheck_Statement (Id, C, Pub);
      Begin_Circuit (Ch.G);
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant (Ch.Last = Chal_Total (C) - 1);
         Lemma_Layer_Fits (C, J);
         declare
            Off_C : constant Natural   := Chal_Off (C, J);
            Off_P : constant Natural   := Proof_Off (C, J);
            Logw  : constant Logw_Type := C.Layers (J).Logw;
            LP    : constant Element_Array (0 .. 4 * Logw + 1) :=
              Proof.Evals (Off_P .. Off_P + 4 * Logw + 1);
            LC    : Element_Array (0 .. 2 * Logw + 1);
         begin
            Replay_Layer (Logw, LP, LC);
            Ch.Layer (Off_C .. Off_C + 2 * Logw + 1) := LC;
         end;
      end loop;
      Sample (Ch.Alpha_Input);
      St := (if Transcript.Is_Exhausted then Exhausted else Ok);
   end Replay_Challenges;

   ----------------------------------------------------------------------
   --  Reader
   ----------------------------------------------------------------------

   --  Element K of Total occupies bytes K * Size .. K * Size + Size - 1
   --  of Total * Size: multiplication by Size is monotonic. A lemma of
   --  its own, on big integers, so that the nonlinear step is proved
   --  in a small context from SPARKlib's lemma.
   procedure Lemma_Element_Fits (K, Total : Natural) with
     Ghost,
     Global => null,
     Pre    => K < Total,
     Post   =>
       To_Big_Integer (K) * To_Big_Integer (Size) + To_Big_Integer (Size)
       <= To_Big_Integer (Total) * To_Big_Integer (Size)
   is
   begin
      SPARK.Lemmas.Integer_Arithmetic.Lemma_Mult_Is_Monotonic
        (K + 1, Total, Size);
   end Lemma_Element_Fits;

   --  Element K of the serialisation B of Total elements.
   procedure Take
     (B        : Byte_Array;
      Total    : Natural;
      K        : Natural;
      E        : out Element;
      Accepted : out Boolean)
   with
     Global => null,
     Pre    =>
       B'First = 0
       and then To_Big_Integer (B'Length)
                = To_Big_Integer (Total) * To_Big_Integer (Size)
       and then K < Total
   is
   begin
      Lemma_Element_Fits (K, Total);
      SA.F.From_Bytes (B (K * Size .. K * Size + Size - 1), E, Accepted);
   end Take;

   procedure Read_Sumcheck_Proof
     (B     : Byte_Array;
      C     : Circuit;
      Proof : out Sumcheck_Proof;
      St    : out Status)
   is
      Total : constant Natural := Proof_Total (C);
      Off  : Natural;
      Logw : Logw_Type;
      K    : Natural := 0;
      Acc  : Boolean;
   begin
      Proof := (Last => Proof.Last, Evals => [others => Zero]);
      St    := Ok;
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant (K = Proof_Off (C, J));
         pragma Loop_Invariant (St in Ok | Bad_Element);
         Lemma_Layer_Fits (C, J);
         Off  := Proof_Off (C, J);
         Logw := C.Layers (J).Logw;
         for R in 0 .. Logw - 1 loop
            pragma Loop_Invariant
              (Off = Proof_Off (C, J) and then Logw = C.Layers (J).Logw
               and then Off + Proof_Size (C, J) <= Total);
            pragma Loop_Invariant (K = Off + 4 * R);
            pragma Loop_Invariant (St in Ok | Bad_Element);
            --  l (P0), r (P0), l (P2), r (P2): slots 0, 2, 1, 3.
            Take (B, Total, K, Proof.Evals (Off + 4 * R), Acc);
            St := (if Acc then St else Bad_Element);
            Take (B, Total, K + 1, Proof.Evals (Off + 4 * R + 2), Acc);
            St := (if Acc then St else Bad_Element);
            Take (B, Total, K + 2, Proof.Evals (Off + 4 * R + 1), Acc);
            St := (if Acc then St else Bad_Element);
            Take (B, Total, K + 3, Proof.Evals (Off + 4 * R + 3), Acc);
            St := (if Acc then St else Bad_Element);
            K := K + 4;
         end loop;
         Take (B, Total, K, Proof.Evals (Off + 4 * Logw), Acc);
         St := (if Acc then St else Bad_Element);
         Take (B, Total, K + 1, Proof.Evals (Off + 4 * Logw + 1), Acc);
         St := (if Acc then St else Bad_Element);
         K := K + 2;
         Lemma_Proof_Step (C, J);
      end loop;
   end Read_Sumcheck_Proof;

end Sumcheck_Transcript;
