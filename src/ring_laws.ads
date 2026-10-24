--  Ring_Laws: consequences of the ring laws, for the kernels of the
--  sumcheck in upstream's form (ADR 0070). Generic over a commutative
--  ring given by its operations and its laws; Sumcheck_Algebra
--  instantiates it with its hidden wrappers, so that the contracts of
--  the concrete field stay out of these proofs. Ghost lemmas stated
--  with Same; each is proved from the laws, and each field proves
--  those for its own operations.

pragma SPARK_Mode (On);

with Proof_Levels;

generic
   type Element is private;
   Zero, One : Element;
   with function "+" (A, B : Element) return Element;
   with function "-" (A, B : Element) return Element;
   with function "*" (A, B : Element) return Element;
   with function Neg (A : Element) return Element;
   with function Same (A, B : Element) return Boolean with Ghost;
   with procedure Lemma_Mul_Assoc (A, B, C : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Mul_Comm (A, B : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Mul_One (A : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Mul_Distrib (A, B, C : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Mul_Distrib_Sub (A, B, C : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Add_Assoc (A, B, C : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Add_Comm (A, B : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Add_Zero (A : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Add_Neg (A : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Sub_Def (A, B : Element)
     with Ghost => Proof_Only;
package Ring_Laws is

   --  (1 - c) t = t - c t: the low half of a bindeq step.
   procedure Lemma_One_Minus (C, T : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same ((One - C) * T, T - C * T);

   --  a + x (b - a) = (1 - x) a + x b: the dense bind.
   procedure Lemma_Bind_Pair (X, A0, A1 : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (A0 + X * (A1 - A0), (One - X) * A0 + X * A1);

   --  c (w r) = w (c r): a factor moves through a product.
   procedure Lemma_Scale (W, C, R : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (C * (W * R), W * (C * R));

   --  Consequences for the round evaluations of the prover (ADR 0070).
   procedure Lemma_Zero_Add (A : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (Zero + A, A);

   procedure Lemma_Neg_Unique (A, B : Element) with
     Ghost => Proof_Only, Global => null,
     Pre   => Same (A + B, Zero),
     Post  => Same (B, Neg (A));

   procedure Lemma_Mul_Zero (A : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (A * Zero, Zero);

   procedure Lemma_Mul_Neg (A, B : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (A * Neg (B), Neg (A * B));

   procedure Lemma_Neg_Add (A, B : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (Neg (A + B), Neg (A) + Neg (B));

   procedure Lemma_Swap4 (A, B, C, D : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same ((A + B) + (C + D), (A + C) + (B + D));

   procedure Lemma_Sub_Pair (A, B, C, D : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same ((A + B) - (C + D), (A - C) + (B - D));

   procedure Lemma_Mul_Distrib_R (A, B, C : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same ((A + B) * C, A * C + B * C);

   procedure Lemma_Add_Sub_Cancel (A, B : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (A + (B - A), B);

   procedure Lemma_Cancel_L (P, Y : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same ((P + Y) - P, Y);

   procedure Lemma_Cancel_R (Y, D : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same ((Y + D) - D, Y);

   --  The value at x of the quadratic with p (0) = a0, p (1) = s1 and
   --  leading coefficient a2: the round evaluations of the prover.
   function Comb (X, A0, S1, A2 : Element) return Element is
     ((A0 + X * ((S1 - A0) - A2)) + (X * X) * A2)
   with Ghost => Proof_Only, Global => null;

   procedure Lemma_Comb_Zero (X : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (Comb (X, Zero, Zero, Zero), Zero);

   --  Comb is additive in its three sums.
   procedure Lemma_Comb_Add (X, A, S, D, A2, S2, D2 : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (Comb (X, A + A2, S + S2, D + D2),
                    Comb (X, A, S, D) + Comb (X, A2, S2, D2));

   --  One pair: (q0 + x dq) (w0 + x dw) from q0 w0, q1 w1 and dq dw.
   procedure Lemma_Comb_Pair (X, Q0, Q1, W0, W1 : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same ((Q0 + X * (Q1 - Q0)) * (W0 + X * (W1 - W0)),
                    Comb (X, Q0 * W0, Q1 * W1, (Q1 - Q0) * (W1 - W0)));

end Ring_Laws;
