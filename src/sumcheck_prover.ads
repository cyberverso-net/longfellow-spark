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
--
--  Documentation: docs/guide/07-prover.md.
--
--  Proof status (per instance). Silver with the ownership checks on
--  the heap buffers. Gold, structural (ADR 0052): Round_Evals equals
--  the ghost transcription Ev0_Ref, Ev2_Ref of eval_round_poly in its
--  order of operations, through the logical equality Same (p (1) is
--  not emitted, so its sum is not transcribed).
--  The padded values are the evaluations minus the pads by the two
--  statements that compute them. Completeness (the verifier accepts the
--  honest proof) is tested, not proved.
--
--  Constant-time discipline (ADR 0051): constant time by construction.
--  Round_Evals loops over the terms of the layer, a public structure,
--  and branches on the parity of a wire index of the term, public;
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
      Ch    : out Challenges)
   with
     Always_Terminates => not ST.SA.F.Sampling_Rejects,
     Pre =>
       Wires'First = 0 and then Wires'Length = ST.SA.Total_Wires (C)
       and then Pads'First = 0 and then Pads'Length = Pad_Total (C)
       and then Proof.Last + 1 = ST.SV.Proof_Total (C)
       and then Ch.Last + 1 = ST.SV.Chal_Total (C);

end Sumcheck_Prover;
