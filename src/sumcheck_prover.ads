--  Sumcheck_Prover: the padded sumcheck proof of draft Section 6.6
--  (Phase C, ADR 0049, 0050, 0051, 0052), sumcheck_prove, sumcheck_
--  prove_layer, eval_round_poly and bind of the reference
--  (docs/specs/rust/src/sumcheck/prover.rs at d5e6be7) and the pads of
--  sumcheck/pad.rs. Generic over the transcript glue of a field, which
--  carries the algebra and the verifier core (hence the layouts of the
--  padded proof, of the challenges and of the pad variables), and over
--  the sampling instance of that field, which carries the randomness
--  source (ADR 0050).
--
--  The prover drives the live transcript (one transcript at a time,
--  ADR 0031): the caller has written the label, the root and the
--  statement; Prove then draws and absorbs exactly what Replay_
--  Challenges of stage 4 replays, records every challenge it draws in
--  the Challenges record of stage 3 and draws alpha_input last, so
--  that Verifier_Core can be called with the challenges as input where
--  the reference replays the core on a copy of the transcript (ADR
--  0049). The wires of every layer come from Eval_Circuit of stage 3,
--  the pads from Sample_Pads in the order the reference consumes its
--  randomness: per layer, per round the two pads of hand 0 then the
--  two of hand 1, then the two claim pads, the product pad computed.
--  Lqc_Triples numbers the quadratic constraints of the claim pads in
--  the witness vector of the commitment (generate_lqc_triples).
--
--  Documentation: docs/guide/07-prover.md.
--
--  Proof status (per instance). Silver with the ownership checks on
--  the heap buffers. Gold, structural (ADR 0052): Round_Evals equals
--  the ghost transcription Ev0_Ref, Ev2_Ref of eval_round_poly in its
--  order of operations, through the logical equality Same (p (1) is
--  not emitted, so its sum is not transcribed). Since M1 (ADR 0063)
--  Prove computes the round polynomial in the dense form of the
--  production prover, Round_Evals_Dense, Gold against QW_Ref, D0_Ref
--  and D2_Ref; Round_Evals stays as the reference, and the harness
--  checks that the two agree. Prove keeps the terms merged as the
--  production prover does: Bind_G_T (Gold against the eq2 table),
--  Merge_Runs (Gold, structural, against Run_Id and Run_Sum) and Bind_H
--  (Gold, structural, against Rd and Corner_K); Bind_G and Update_Terms
--  stay as the reference, and the harness checks that the round
--  polynomials agree on every round.
--  The padded values are the evaluations minus the pads by the two
--  statements that compute them. Completeness (the verifier accepts the
--  honest proof) is tested, not proved.
--
--  Constant-time discipline (ADR 0051): constant time by construction.
--  Round_Evals loops over the terms of the layer, a public structure,
--  and branches on the parity of a wire index of the term, public;
--  Round_Evals_Dense writes at a wire index of the term and loops over
--  the pairs of a public length; Merge_Runs and Bind_H compare the
--  wire indices of the terms, public, and Bind_G_T compares the
--  constant of a term, public, with zero;
--  Bind is a fixed loop; the pads depend on the randomness. The wires
--  and the pads are secret, and so are the evaluations until padded.
--  The guarantee is scoped to builds with assertions disabled (ADR
--  0006).

pragma SPARK_Mode (On);

with Proof_Levels;
with Sumcheck_Transcript;
with Sampling;

generic
   with package ST is new Sumcheck_Transcript (<>);
   with package SP is new Sampling (F => ST.SA.F, others => <>);
package Sumcheck_Prover is

   subtype Element is ST.SA.Element;
   subtype Element_Array is ST.SA.Element_Array;
   subtype Circuit is ST.SA.Circuit;
   subtype Term is ST.SA.Term;
   subtype Term_Array is ST.SA.Term_Array;
   subtype Sumcheck_Proof is ST.SV.Sumcheck_Proof;
   subtype Challenges is ST.SV.Challenges;

   use ST.SA.F;
   use type ST.SV.Lqc_Triple;
   use type ST.SA.Term;

   -------------------------------------------------------------------
   --  The pads (Section 6.5)
   -------------------------------------------------------------------

   --  The pad variables of every layer, 4 logw + 3 each, numbered from
   --  0 (Pad_Off of the core with Base 0).
   function Pad_Total (C : Circuit) return Natural is
     (ST.SV.Pad_Off (C, C.Last_Layer + 1, 0))
   with Global => null;

   --  CircuitPad::sample: for every layer, for every round the two
   --  pads of hand 0 (p (0), p (P2)) then the two of hand 1, then the
   --  claim pads c0 and c1, and cr = c0 * c1 (computed).
   procedure Sample_Pads (C : Circuit; Pads : out Element_Array) with
     Always_Terminates => not ST.SA.F.Sampling_Rejects,
     Pre => Pads'First = 0 and then Pads'Length = Pad_Total (C);

   --  generate_lqc_triples of zk/common.rs: the quadratic constraint of
   --  layer J ties the claim pads c0, c1 and their product, numbered in
   --  the witness vector of the commitment (the private inputs first,
   --  then the pads), exactly the triples Verifier_Core emits.
   procedure Lqc_Triples (C : Circuit; Lqc : out ST.SV.Lqc_Array) with
     Global => null,
     Pre    => Lqc'First = 0 and then Lqc'Last = C.Last_Layer,
     Post   =>
       (for all J in 0 .. C.Last_Layer =>
          Lqc (J) = (X => ST.SV.Pad_Off (C, J, C.Ninput - C.Npublic)
                            + 4 * C.Layers (J).Logw,
                     Y => ST.SV.Pad_Off (C, J, C.Ninput - C.Npublic)
                            + 4 * C.Layers (J).Logw + 1,
                     Z => ST.SV.Pad_Off (C, J, C.Ninput - C.Npublic)
                            + 4 * C.Layers (J).Logw + 2));

   -------------------------------------------------------------------
   --  eval_round_poly (Section 6.6)
   -------------------------------------------------------------------

   subtype Hand is Natural range 0 .. 1;

   --  vector_ref: entry I of the first N, zero beyond.
   function Ref (A : Element_Array; N, I : Natural) return Element is
     (if I < N then A (I) else Zero)
   with Global => null, Pre => A'First = 0 and then N <= A'Length;

   function Hand_Index (T : Term; H : Hand) return Natural is
     (if H = 0 then T.H0 else T.H1)
   with Global => null;

   --  The two sums over the first K terms, in the order of operations
   --  of eval_round_poly: coef = k * other, wx2 = w0 + x2 * (w1 - w0);
   --  an even pair index adds coef * w0 to ev0 and (coef * (1 - x2))
   --  * wx2 to ev2, an odd one adds (coef * x2) * wx2 to ev2 (and
   --  coef * w1 to the unused p (1)). Recursive, hence hidden; the
   --  lemmas of the body unhide them one step at a time.
   function Ev0_Ref
     (T      : Term_Array;
      Active : Element_Array;
      NA     : Natural;
      Other  : Element_Array;
      NO     : Natural;
      H      : Hand;
      X2     : Element;
      K      : Natural) return Element
   is
     (if K = 0 then Zero
      else
        (declare
           Tm   : constant Term := T (T'First + K - 1);
           Hb   : constant Natural := Hand_Index (Tm, H);
           Pair : constant Natural := Hb - Hb mod 2;
           W0   : constant Element := Ref (Active, NA, Pair);
           Coef : constant Element :=
             Tm.K * Ref (Other, NO, Hand_Index (Tm, 1 - H));
         begin
           (if Hb mod 2 = 0
            then Ev0_Ref (T, Active, NA, Other, NO, H, X2, K - 1) + Coef * W0
            else Ev0_Ref (T, Active, NA, Other, NO, H, X2, K - 1))))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => Active'First = 0 and then NA <= Active'Length
               and then Other'First = 0 and then NO <= Other'Length
               and then K <= T'Length,
        Subprogram_Variant => (Decreases => K);

   function Ev2_Ref
     (T      : Term_Array;
      Active : Element_Array;
      NA     : Natural;
      Other  : Element_Array;
      NO     : Natural;
      H      : Hand;
      X2     : Element;
      K      : Natural) return Element
   is
     (if K = 0 then Zero
      else
        (declare
           Tm   : constant Term := T (T'First + K - 1);
           Hb   : constant Natural := Hand_Index (Tm, H);
           Pair : constant Natural := Hb - Hb mod 2;
           W0   : constant Element := Ref (Active, NA, Pair);
           W1   : constant Element := Ref (Active, NA, Pair + 1);
           Coef : constant Element :=
             Tm.K * Ref (Other, NO, Hand_Index (Tm, 1 - H));
           Wx2  : constant Element := W0 + X2 * (W1 - W0);
         begin
           (if Hb mod 2 = 0
            then Ev2_Ref (T, Active, NA, Other, NO, H, X2, K - 1)
                 + (Coef * (One - X2)) * Wx2
            else Ev2_Ref (T, Active, NA, Other, NO, H, X2, K - 1)
                 + (Coef * X2) * Wx2)))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => Active'First = 0 and then NA <= Active'Length
               and then Other'First = 0 and then NO <= Other'Length
               and then K <= T'Length,
        Subprogram_Variant => (Decreases => K);

   --  The evaluations of the round polynomial of hand H in 0 and in
   --  X2 (= P2) over the terms T (the reference also forms p (1), which
   --  the proof never uses), on the active wires of that hand (the
   --  first NA entries, zero beyond) and the wires of the other hand.
   procedure Round_Evals
     (T      : Term_Array;
      Active : Element_Array;
      NA     : Natural;
      Other  : Element_Array;
      NO     : Natural;
      H      : Hand;
      X2     : Element;
      Ev0    : out Element;
      Ev2    : out Element)
   with
     Global => null,
     Pre    => Active'First = 0 and then NA <= Active'Length
               and then Other'First = 0 and then NO <= Other'Length,
     Post   =>
       (Proof_Only =>
          Same (Ev0, Ev0_Ref (T, Active, NA, Other, NO, H, X2, T'Length))
          and then
          Same (Ev2, Ev2_Ref (T, Active, NA, Other, NO, H, X2, T'Length)));

   -------------------------------------------------------------------
   --  The dense round polynomial (Phase D, M1; ADR 0063), as the
   --  production prover computes it (rust/runtime/sumcheck/src/
   --  prover.rs, layer and quad_round_poly): each term adds k times its
   --  other-hand wire to qw at its active-hand index, then p (0) and
   --  p (P2) are sums over the pairs (2 i, 2 i + 1) of qw and of the
   --  active wires. The same values as Round_Evals, which stays as the
   --  reference: their agreement is distributivity, tested.
   -------------------------------------------------------------------

   --  qw at X after the first N terms, in their order.
   function QW_Ref
     (T     : Term_Array;
      Other : Element_Array;
      NO    : Natural;
      H     : Hand;
      X     : Natural;
      N     : Natural) return Element
   is
     (if N = 0 then Zero
      elsif Hand_Index (T (T'First + N - 1), H) = X
      then QW_Ref (T, Other, NO, H, X, N - 1)
           + T (T'First + N - 1).K
             * Ref (Other, NO, Hand_Index (T (T'First + N - 1), 1 - H))
      else QW_Ref (T, Other, NO, H, X, N - 1))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => Other'First = 0 and then NO <= Other'Length
               and then N <= T'Length,
        Subprogram_Variant => (Decreases => N);

   --  p (0) over the first M pairs: qw (2 i) times w (2 i).
   function D0_Ref
     (QW : Element_Array; A : Element_Array; NA : Natural; M : Natural)
      return Element
   is
     (if M = 0 then Zero
      else D0_Ref (QW, A, NA, M - 1)
           + Ref (QW, NA, 2 * (M - 1)) * Ref (A, NA, 2 * (M - 1)))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => QW'First = 0 and then A'First = 0
               and then NA <= QW'Length and then NA <= A'Length
               and then M <= Natural'Last / 2,
        Subprogram_Variant => (Decreases => M);

   --  p (P2) over the first M pairs: qw and w each at P2 on its pair.
   function D2_Ref
     (QW : Element_Array; A : Element_Array; NA : Natural; X2 : Element;
      M  : Natural) return Element
   is
     (if M = 0 then Zero
      else D2_Ref (QW, A, NA, X2, M - 1)
           + (Ref (QW, NA, 2 * (M - 1))
              + X2 * (Ref (QW, NA, 2 * M - 1) - Ref (QW, NA, 2 * (M - 1))))
             * (Ref (A, NA, 2 * (M - 1))
                + X2 * (Ref (A, NA, 2 * M - 1) - Ref (A, NA, 2 * (M - 1)))))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => QW'First = 0 and then A'First = 0
               and then NA <= QW'Length and then NA <= A'Length
               and then M <= Natural'Last / 2,
        Subprogram_Variant => (Decreases => M);

   --  The evaluations of hand H in 0 and in X2 by the dense form. QW is
   --  a work array of at least NA entries; on return its first NA hold
   --  qw.
   procedure Round_Evals_Dense
     (T      : Term_Array;
      Active : Element_Array;
      NA     : Natural;
      Other  : Element_Array;
      NO     : Natural;
      H      : Hand;
      X2     : Element;
      QW     : in out Element_Array;
      Ev0    : out Element;
      Ev2    : out Element)
   with
     Global => null,
     Pre    => Active'First = 0 and then NA <= Active'Length
               and then Other'First = 0 and then NO <= Other'Length
               and then QW'First = 0 and then NA <= QW'Length
               and then NA <= ST.SA.Max_Wires,
     Post   =>
       (Proof_Only =>
          (for all X in 0 .. NA - 1 =>
             Same (QW (X), QW_Ref (T, Other, NO, H, X, T'Length)))
          and then
          Same (Ev0, D0_Ref (QW, Active, NA, (NA + 1) / 2))
          and then
          Same (Ev2, D2_Ref (QW, Active, NA, X2, (NA + 1) / 2)));

   -------------------------------------------------------------------
   --  The merged terms (Phase D, M1; ADR 0063), as the production
   --  prover keeps them (rust/runtime/sumcheck/src/hquad.rs, bind_g and
   --  bind_h): g bound with the eq2 table, the consecutive terms with
   --  the same hands merged into one, then at each round the two
   --  corners (2 i, 2 i + 1) of the bound hand merged by affine
   --  interpolation, so that the terms shrink with the rounds. The
   --  coefficient of every corner is linear in the terms, so the round
   --  polynomial is the one of the reference terms, which Update_Terms
   --  keeps one by one: tested.
   -------------------------------------------------------------------

   --  The coefficients bound with the eq2 table E (Eq2_Table): beta
   --  times E (g) for a Z term, k times E (g) otherwise, zero beyond
   --  the table, as Bound_KT reads it; g set to 0.
   procedure Bind_G_T (T : in out Term_Array; E : Element_Array;
                       Beta : Element)
   with
     Global => null,
     Pre    => E'First = 0,
     Post   =>
       (for all I in T'Range =>
          Same (T (I).K,
                (if T'Old (I).K = Zero
                 then Beta * Ref (E, E'Length, T'Old (I).G)
                 else T'Old (I).K * Ref (E, E'Length, T'Old (I).G)))
          and then T (I).G = 0
          and then T (I).H0 = T'Old (I).H0
          and then T (I).H1 = T'Old (I).H1);

   function Same_Hands (A, B : Term) return Boolean is
     (A.H0 = B.H0 and then A.H1 = B.H1)
   with Global => null;

   --  The run of the term at offset I: 0 for the first, one more at
   --  each change of hands.
   function Run_Id (T : Term_Array; I : Natural) return Natural is
     (if I = 0 then 0
      elsif Same_Hands (T (T'First + I - 1), T (T'First + I))
      then Run_Id (T, I - 1)
      else Run_Id (T, I - 1) + 1)
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => I < T'Length,
        Post => Run_Id'Result <= I,
        Subprogram_Variant => (Decreases => I);

   --  The coefficient of run X after the first N terms: the sum of
   --  their coefficients, from zero, in their order.
   function Run_Sum (T : Term_Array; X : Natural; N : Natural)
      return Element
   is
     (if N = 0 then Zero
      elsif Run_Id (T, N - 1) = X
      then Run_Sum (T, X, N - 1) + T (T'First + N - 1).K
      else Run_Sum (T, X, N - 1))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => N <= T'Length,
        Subprogram_Variant => (Decreases => N);

   --  The runs of T merged in place: the first N terms are the runs,
   --  each with the hands of its terms and the sum of their
   --  coefficients.
   procedure Merge_Runs (T : in out Term_Array; N : out Natural)
   with
     Global => null,
     Post   =>
       (Runtime    => N <= T'Length,
        Proof_Only =>
          N = (if T'Length = 0 then 0
               else Run_Id (T'Old, T'Length - 1) + 1)
          and then
          (for all X in 0 .. N - 1 =>
             Same (T (T'First + X).K, Run_Sum (T'Old, X, T'Length)))
          and then
          (for all I in 0 .. T'Length - 1 =>
             Same_Hands (T (T'First + Run_Id (T'Old, I)),
                         T'Old (T'First + I))));

   --  Two corners at offset P for hand H: the next term has the same
   --  other hand and the next index of the same pair.
   function Two (T : Term_Array; P : Natural; H : Hand) return Boolean is
     (P + 1 < T'Length
      and then Hand_Index (T (T'First + P), 1 - H)
               = Hand_Index (T (T'First + P + 1), 1 - H)
      and then Hand_Index (T (T'First + P), H) / 2
               = Hand_Index (T (T'First + P + 1), H) / 2
      and then Hand_Index (T (T'First + P + 1), H)
               = Hand_Index (T (T'First + P), H) + 1)
   with Global => null,
        Pre => P < T'Length;

   --  The offset of the input read for output K: one corner or two.
   function Rd (T : Term_Array; H : Hand; K : Natural) return Natural is
     (if K = 0 then 0
      elsif Rd (T, H, K - 1) >= T'Length then Rd (T, H, K - 1)
      elsif Two (T, Rd (T, H, K - 1), H) then Rd (T, H, K - 1) + 2
      else Rd (T, H, K - 1) + 1)
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Post => Rd'Result <= T'Length,
        Subprogram_Variant => (Decreases => K);

   --  The coefficient of the corner read at P, bound at R:
   --  affine_interpolation for two corners, nz_z for an even one
   --  alone, z_nz for an odd one alone.
   function Corner_K (T : Term_Array; P : Natural; H : Hand; R : Element)
      return Element
   is
     (if Two (T, P, H)
      then T (T'First + P).K
           + (T (T'First + P + 1).K - T (T'First + P).K) * R
      elsif Hand_Index (T (T'First + P), H) mod 2 = 0
      then T (T'First + P).K - T (T'First + P).K * R
      else T (T'First + P).K * R)
   with Global => null,
        Pre => P < T'Length;

   --  bind_h: the corners of hand H merged in place at R; the first N
   --  terms are the merged ones, the bound hand halved.
   procedure Bind_H (T : in out Term_Array; H : Hand; R : Element;
                     N : out Natural)
   with
     Global => null,
     Post   =>
       (Runtime    => N <= T'Length,
        Proof_Only =>
          Rd (T'Old, H, N) = T'Length
          and then
          (for all K in 0 .. N - 1 =>
             Rd (T'Old, H, K) < T'Length
             and then
             Same (T (T'First + K).K,
                   Corner_K (T'Old, Rd (T'Old, H, K), H, R))
             and then
             Hand_Index (T (T'First + K), H)
             = Hand_Index (T'Old (T'First + Rd (T'Old, H, K)), H) / 2
             and then
             Hand_Index (T (T'First + K), 1 - H)
             = Hand_Index (T'Old (T'First + Rd (T'Old, H, K)), 1 - H)));

   --  The reference binding of hand H at X, term by term: an even
   --  index scales k by 1 - X, an odd one by X, the index halved.
   procedure Update_Terms (T : in out Term_Array; H : Hand; X : Element)
   with
     Global => null;

   -------------------------------------------------------------------
   --  sumcheck_prove
   -------------------------------------------------------------------

   --  The padded proof and every challenge, on the live transcript
   --  after the label, the root and the statement. Wires is the buffer
   --  of Eval_Circuit (every layer's values, the inputs last), Pads the
   --  pads of Sample_Pads.
   procedure Prove
     (C     : Circuit;
      Wires : Element_Array;
      Pads  : Element_Array;
      Proof : out Sumcheck_Proof;
      Ch    : out Challenges;
      BQ    : out Element_Array)
   with
     Always_Terminates => not ST.SA.F.Sampling_Rejects,
     Pre =>
       Wires'First = 0 and then Wires'Length = ST.SA.Total_Wires (C)
       and then Pads'First = 0 and then Pads'Length = Pad_Total (C)
       and then Proof.Last + 1 = ST.SV.Proof_Total (C)
       and then Ch.Last + 1 = ST.SV.Chal_Total (C)
       and then BQ'First = 0 and then BQ'Length = C.Last_Layer + 1,
     --  The bound quad of every layer, as the verifier computes it from
     --  the challenges (ADR 0071): Verifier_Core takes it from here.
     Post =>
       (Proof_Only =>
          (for all J in 0 .. C.Last_Layer =>
             Same (BQ (J), ST.SV.BQ_Ref (C, Ch, J))));

end Sumcheck_Prover;
