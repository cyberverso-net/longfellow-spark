pragma SPARK_Mode (On);

package body Ring_Laws is

   procedure Lemma_One_Minus (C, T : Element) is
   begin
      Lemma_Mul_Comm (One - C, T);
      Lemma_Mul_Distrib_Sub (T, One, C);
      Lemma_Mul_One (T);
      Lemma_Mul_Comm (T, C);
   end Lemma_One_Minus;

   procedure Lemma_Bind_Pair (X, A0, A1 : Element) is
      P : constant Element := X * A1 with Ghost => Proof_Only;
      Q : constant Element := X * A0 with Ghost => Proof_Only;
   begin
      --  Left: a0 + (p - q) = a0 + (p + -q) = a0 + (-q + p).
      Lemma_Mul_Distrib_Sub (X, A1, A0);
      Lemma_Sub_Def (P, Q);
      Lemma_Add_Comm (P, Neg (Q));
      --  Right: (1 - x) a0 = a0 - q = a0 + -q, then associativity.
      Lemma_One_Minus (X, A0);
      Lemma_Sub_Def (A0, Q);
      Lemma_Add_Assoc (A0, Neg (Q), P);
   end Lemma_Bind_Pair;

   procedure Lemma_Scale (W, C, R : Element) is
   begin
      Lemma_Mul_Assoc (C, W, R);
      Lemma_Mul_Comm (C, W);
      Lemma_Mul_Assoc (W, C, R);
   end Lemma_Scale;

   procedure Lemma_Zero_Add (A : Element) is
   begin
      Lemma_Add_Comm (Zero, A);
      Lemma_Add_Zero (A);
   end Lemma_Zero_Add;

   --  b = b + (a + -a) = (b + a) + -a = 0 + -a.
   procedure Lemma_Neg_Unique (A, B : Element) is
   begin
      Lemma_Add_Zero (B);
      Lemma_Add_Neg (A);
      Lemma_Add_Assoc (B, A, Neg (A));
      Lemma_Add_Comm (B, A);
      Lemma_Zero_Add (Neg (A));
   end Lemma_Neg_Unique;

   --  z = a 0 satisfies z + z = z, and then z = (z + z) + -z = 0.
   procedure Lemma_Mul_Zero (A : Element) is
      Z : constant Element := A * Zero with Ghost => Proof_Only;
   begin
      Lemma_Add_Zero (Zero);
      Lemma_Mul_Distrib (A, Zero, Zero);
      pragma Assert (Proof_Only => Same (Z + Z, Z));
      Lemma_Add_Neg (Z);
      Lemma_Add_Assoc (Z, Z, Neg (Z));
      Lemma_Add_Zero (Z);
   end Lemma_Mul_Zero;

   --  a b + a (-b) = a (b + -b) = a 0 = 0.
   procedure Lemma_Mul_Neg (A, B : Element) is
   begin
      Lemma_Mul_Distrib (A, B, Neg (B));
      Lemma_Add_Neg (B);
      Lemma_Mul_Zero (A);
      Lemma_Neg_Unique (A * B, A * Neg (B));
   end Lemma_Mul_Neg;

   --  (a + b) + (-a + -b) = (a + -a) + (b + -b) = 0.
   procedure Lemma_Neg_Add (A, B : Element) is
   begin
      Lemma_Swap4 (A, B, Neg (A), Neg (B));
      Lemma_Add_Neg (A);
      Lemma_Add_Neg (B);
      Lemma_Add_Zero (Zero);
      Lemma_Neg_Unique (A + B, Neg (A) + Neg (B));
   end Lemma_Neg_Add;

   procedure Lemma_Swap4 (A, B, C, D : Element) is
   begin
      Lemma_Add_Assoc (A, B, C + D);
      Lemma_Add_Assoc (B, C, D);
      Lemma_Add_Comm (B, C);
      Lemma_Add_Assoc (C, B, D);
      Lemma_Add_Assoc (A, C, B + D);
   end Lemma_Swap4;

   procedure Lemma_Sub_Pair (A, B, C, D : Element) is
   begin
      Lemma_Sub_Def (A + B, C + D);
      Lemma_Neg_Add (C, D);
      Lemma_Swap4 (A, B, Neg (C), Neg (D));
      Lemma_Sub_Def (A, C);
      Lemma_Sub_Def (B, D);
   end Lemma_Sub_Pair;

   procedure Lemma_Mul_Distrib_R (A, B, C : Element) is
   begin
      Lemma_Mul_Comm (A + B, C);
      Lemma_Mul_Distrib (C, A, B);
      Lemma_Mul_Comm (C, A);
      Lemma_Mul_Comm (C, B);
   end Lemma_Mul_Distrib_R;

   --  a + (b + -a) = a + (-a + b) = (a + -a) + b = 0 + b.
   procedure Lemma_Add_Sub_Cancel (A, B : Element) is
   begin
      Lemma_Sub_Def (B, A);
      Lemma_Add_Comm (B, Neg (A));
      Lemma_Add_Assoc (A, Neg (A), B);
      Lemma_Add_Neg (A);
      Lemma_Zero_Add (B);
   end Lemma_Add_Sub_Cancel;

   --  (p + y) + -p = (y + p) + -p = y + (p + -p) = y + 0.
   procedure Lemma_Cancel_L (P, Y : Element) is
   begin
      Lemma_Sub_Def (P + Y, P);
      Lemma_Add_Comm (P, Y);
      Lemma_Add_Assoc (Y, P, Neg (P));
      Lemma_Add_Neg (P);
      Lemma_Add_Zero (Y);
   end Lemma_Cancel_L;

   --  (y + d) + -d = y + (d + -d) = y + 0.
   procedure Lemma_Cancel_R (Y, D : Element) is
   begin
      Lemma_Sub_Def (Y + D, D);
      Lemma_Add_Assoc (Y, D, Neg (D));
      Lemma_Add_Neg (D);
      Lemma_Add_Zero (Y);
   end Lemma_Cancel_R;

   procedure Lemma_Comb_Zero (X : Element) is
   begin
      Lemma_Sub_Def (Zero, Zero);
      Lemma_Add_Neg (Zero);
      Lemma_Mul_Zero (X);
      Lemma_Mul_Zero (X * X);
      Lemma_Add_Zero (Zero);
   end Lemma_Comb_Zero;

   procedure Lemma_Comb_Add (X, A, S, D, A2, S2, D2 : Element) is
      E  : constant Element := (S - A) - D with Ghost => Proof_Only;
      E2 : constant Element := (S2 - A2) - D2 with Ghost => Proof_Only;
   begin
      Lemma_Sub_Pair (S, S2, A, A2);
      Lemma_Sub_Pair (S - A, S2 - A2, D, D2);
      Lemma_Mul_Distrib (X, E, E2);
      Lemma_Mul_Distrib (X * X, D, D2);
      Lemma_Swap4 (A, A2, X * E, X * E2);
      Lemma_Swap4 (A + X * E, A2 + X * E2, (X * X) * D, (X * X) * D2);
   end Lemma_Comb_Add;

   procedure Lemma_Comb_Pair (X, Q0, Q1, W0, W1 : Element) is
      DQ : constant Element := Q1 - Q0 with Ghost => Proof_Only;
      DW : constant Element := W1 - W0 with Ghost => Proof_Only;
      U  : constant Element := X * DQ with Ghost => Proof_Only;
      V  : constant Element := X * DW with Ghost => Proof_Only;
      P  : constant Element := Q0 * W0 with Ghost => Proof_Only;
      Ae : constant Element := DQ * W0 with Ghost => Proof_Only;
      Be : constant Element := Q0 * DW with Ghost => Proof_Only;
      Dd : constant Element := DQ * DW with Ghost => Proof_Only;
   begin
      --  The left side: (p + x ae) + (x be + x^2 dd).
      Lemma_Mul_Distrib (Q0 + U, W0, V);
      Lemma_Mul_Distrib_R (Q0, U, W0);
      Lemma_Mul_Distrib_R (Q0, U, V);
      Lemma_Mul_Assoc (X, DQ, W0);
      Lemma_Scale (X, Q0, DW);
      Lemma_Mul_Assoc (X, DQ, V);
      Lemma_Scale (X, DQ, DW);
      Lemma_Mul_Assoc (X, X, Dd);
      pragma Assert
        (Proof_Only =>
           Same ((Q0 + U) * (W0 + V),
                 (P + X * Ae) + (X * Be + (X * X) * Dd)));

      --  q1 w1 = (p + ae) + (be + dd), so (q1 w1 - p) - dd = ae + be.
      Lemma_Add_Sub_Cancel (Q0, Q1);
      Lemma_Add_Sub_Cancel (W0, W1);
      pragma Assert (Proof_Only => Same (Q1 * W1, (Q0 + DQ) * (W0 + DW)));
      Lemma_Mul_Distrib (Q0 + DQ, W0, DW);
      Lemma_Mul_Distrib_R (Q0, DQ, W0);
      Lemma_Mul_Distrib_R (Q0, DQ, DW);
      pragma Assert (Proof_Only => Same (Q1 * W1, (P + Ae) + (Be + Dd)));
      Lemma_Add_Assoc (P, Ae, Be + Dd);
      Lemma_Cancel_L (P, Ae + (Be + Dd));
      Lemma_Add_Assoc (Ae, Be, Dd);
      Lemma_Cancel_R (Ae + Be, Dd);
      pragma Assert (Proof_Only => Same ((Q1 * W1 - P) - Dd, Ae + Be));

      --  The right side, regrouped.
      Lemma_Mul_Distrib (X, Ae, Be);
      Lemma_Add_Assoc (P, X * Ae, X * Be);
      Lemma_Add_Assoc (P + X * Ae, X * Be, (X * X) * Dd);
   end Lemma_Comb_Pair;

   procedure Lemma_Split_Zero (F0, F1 : Element) is
   begin
      Lemma_Mul_Zero (F0);
      Lemma_Mul_Zero (F1);
      Lemma_Add_Zero (Zero);
   end Lemma_Split_Zero;

   procedure Lemma_Split_L (F0, F1, V0, V1, Y : Element) is
   begin
      Lemma_Mul_Distrib (F0, V0, Y);
      Lemma_Add_Assoc (F0 * V0, F0 * Y, F1 * V1);
      Lemma_Add_Comm (F0 * Y, F1 * V1);
      Lemma_Add_Assoc (F0 * V0, F1 * V1, F0 * Y);
   end Lemma_Split_L;

   procedure Lemma_Split_R (F0, F1, V0, V1, Y : Element) is
   begin
      Lemma_Mul_Distrib (F1, V1, Y);
      Lemma_Add_Assoc (F0 * V0, F1 * V1, F1 * Y);
   end Lemma_Split_R;

   procedure Lemma_Split_LR (F0, F1, V0, V1, Y0, Y1 : Element) is
   begin
      Lemma_Mul_Distrib (F0, V0, Y0);
      Lemma_Mul_Distrib (F1, V1, Y1);
      Lemma_Swap4 (F0 * V0, F0 * Y0, F1 * V1, F1 * Y1);
   end Lemma_Split_LR;

   procedure Lemma_Corner_Even (K, C : Element) is
   begin
      Lemma_One_Minus (C, K);
      Lemma_Mul_Comm (K, C);
   end Lemma_Corner_Even;

   procedure Lemma_Corner_Odd (K, C : Element) is
   begin
      Lemma_Mul_Comm (K, C);
   end Lemma_Corner_Odd;

   procedure Lemma_Corner_Two (K0, K1, C : Element) is
   begin
      Lemma_Mul_Comm (K1 - K0, C);
      Lemma_Bind_Pair (C, K0, K1);
   end Lemma_Corner_Two;

   procedure Lemma_Move_L (K, P0, Fc, P1 : Element) is
   begin
      Lemma_Mul_Assoc (K, P0, Fc);
      Lemma_Mul_Assoc (K * P0, Fc, P1);
      Lemma_Mul_Comm (Fc, P1);
      Lemma_Mul_Assoc (K * P0, P1, Fc);
      Lemma_Mul_Comm ((K * P0) * P1, Fc);
   end Lemma_Move_L;

   procedure Lemma_Move_R (K, P0, P1, Fc : Element) is
   begin
      Lemma_Mul_Assoc (K * P0, P1, Fc);
      Lemma_Mul_Comm ((K * P0) * P1, Fc);
   end Lemma_Move_R;

   procedure Lemma_One_Mul (B : Element) is
   begin
      Lemma_Mul_Comm (One, B);
      Lemma_Mul_One (B);
   end Lemma_One_Mul;

   procedure Lemma_One_Twice (K : Element) is
   begin
      Lemma_Mul_One (K);
   end Lemma_One_Twice;

   procedure Lemma_Zero_Mul_Twice (B, X : Element) is
   begin
      Lemma_Mul_Zero (B);
      Lemma_Mul_Comm (Zero, X);
      Lemma_Mul_Zero (X);
   end Lemma_Zero_Mul_Twice;

   procedure Lemma_Assoc_Add (S, R, K : Element) is
   begin
      Lemma_Add_Assoc (S, R, K);
   end Lemma_Assoc_Add;

   procedure Lemma_Zero_Add_Once (K : Element) is
   begin
      Lemma_Zero_Add (K);
   end Lemma_Zero_Add_Once;

   procedure Lemma_Add_Zero_Once (S : Element) is
   begin
      Lemma_Add_Zero (S);
   end Lemma_Add_Zero_Once;

   procedure Lemma_Mul_One_Once (P : Element) is
   begin
      Lemma_Mul_One (P);
   end Lemma_Mul_One_Once;

   procedure Lemma_Assoc_Mul (P, Fc, B : Element) is
   begin
      Lemma_Mul_Assoc (P, Fc, B);
   end Lemma_Assoc_Mul;

   procedure Lemma_Zero_Mul_R (X : Element) is
   begin
      Lemma_Mul_Zero (X);
   end Lemma_Zero_Mul_R;

end Ring_Laws;
