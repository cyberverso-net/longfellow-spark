pragma SPARK_Mode (On);

package body P256_Field is

   --  Outside SPARK on purpose: the provers see only the declaration
   --  of Eq and its Logical_Equal annotation.
   function Eq (A, B : Element) return Boolean with
     SPARK_Mode => Off
   is
   begin
      return A = B;
   end Eq;

   -------------------------------------------------------------------
   --  Lemmas on the model
   -------------------------------------------------------------------

   procedure Lemma_Partial_Bounds (L : Word_Array; N : Natural) with
     Ghost => Proof_Only, Global => null,
     Pre  => L'First = 0
       and then (N = 0 or else N - 1 <= L'Last)
       and then N <= Max_Words,
     Post => Partial (L, N) >= 0 and then Partial (L, N) < Weight (N),
     Subprogram_Variant => (Decreases => N);

   procedure Lemma_Partial_Bounds (L : Word_Array; N : Natural) is
   begin
      if N > 0 then
         Lemma_Partial_Bounds (L, N - 1);
         pragma Assert (Proof_Only => Conv (L (N - 1)) <= Two_64 - 1);
         pragma Assert
           (Proof_Only => Partial (L, N)
              <= (Weight (N - 1) - 1) + (Two_64 - 1) * Weight (N - 1));
      end if;
   end Lemma_Partial_Bounds;

   procedure Lemma_To_Int_Bounds (L : Word_Array) is
   begin
      Lemma_Partial_Bounds (L, L'Length);
   end Lemma_To_Int_Bounds;

   procedure Lemma_Split (X : Unsigned_128) is
      Q : constant Unsigned_128 := X / 2 ** 64;
      M : constant Unsigned_128 := X mod 2 ** 64;
   begin
      pragma Assert (Proof_Only => Q = Shift_Right (X, 64));
      pragma Assert (Proof_Only => M = (X and 16#FFFF_FFFF_FFFF_FFFF#));
      pragma Assert (Proof_Only => X = Q * 2 ** 64 + M);
      pragma Assert
        (Proof_Only =>
           Conv128 (X) = Conv128 (Q) * Two_64 + Conv128 (M));
      pragma Assert (Proof_Only => Conv128 (Q) = Conv (Hi (X)));
      pragma Assert (Proof_Only => Conv128 (M) = Conv (Lo (X)));
   end Lemma_Split;

   --  Explicit unfolding of the weights, so that the provers need not
   --  instantiate the recursive definitions themselves.
   procedure Lemma_Unfold with
     Ghost => Proof_Only, Global => null,
     Post => Weight (0) = 1
       and then Weight (1) = Two_64
       and then Weight (2) = Two_64 * Two_64
       and then Weight (3) = Two_64 * Two_64 * Two_64
       and then Weight (4) = Two_64 * Two_64 * Two_64 * Two_64
       and then Weight (5) = Two_64 * Two_64 * Two_64 * Two_64 * Two_64
       and then Weight (6)
         = Two_64 * Two_64 * Two_64 * Two_64 * Two_64 * Two_64
       and then Weight (7)
                = Two_64 * Two_64 * Two_64 * Two_64 * Two_64 * Two_64 * Two_64
       and then Weight (8)
                = Two_64 * Two_64 * Two_64 * Two_64 * Two_64 * Two_64 * Two_64
                  * Two_64
       and then Two_256 = Weight (4)
       and then Two_64 = Two_32 * Two_32
       and then Two_32 > 5 and then Two_64 > 5
       and then Conv (0) = 0 and then Conv (1) = 1;

   procedure Lemma_Unfold is
   begin
      pragma Assert
        (Proof_Only =>
           Two_32 = To_Big_Integer (65536) * To_Big_Integer (65536));
      pragma Assert (Proof_Only => Two_64 = Two_32 * Two_32);
      pragma Assert (Proof_Only => Weight (1) = Two_64 * Weight (0));
      pragma Assert (Proof_Only => Weight (2) = Two_64 * Weight (1));
      pragma Assert (Proof_Only => Weight (3) = Two_64 * Weight (2));
      pragma Assert (Proof_Only => Weight (4) = Two_64 * Weight (3));
      pragma Assert (Proof_Only => Weight (5) = Two_64 * Weight (4));
      pragma Assert (Proof_Only => Weight (6) = Two_64 * Weight (5));
      pragma Assert (Proof_Only => Weight (7) = Two_64 * Weight (6));
      pragma Assert (Proof_Only => Weight (8) = Two_64 * Weight (7));
   end Lemma_Unfold;

   --  Subtraction of 128-bit values that does not wrap.
   procedure Lemma_Sub128 (X, Y : Unsigned_128) with
     Ghost => Proof_Only, Global => null,
     Pre  => X >= Y,
     Post => Conv128 (X - Y) = Conv128 (X) - Conv128 (Y);

   procedure Lemma_Sub128 (X, Y : Unsigned_128) is
      D : constant Unsigned_128 := X - Y;
   begin
      pragma Assert (Proof_Only => D + Y = X);
      pragma Assert (Proof_Only => D <= X);
      pragma Assert
        (Proof_Only =>
           Conv128 (D + Y) = Conv128 (D) + Conv128 (Y));
   end Lemma_Sub128;

   --  Zero-extension preserves the value.
   procedure Lemma_Ext64 (H : Unsigned_64) with
     Ghost => Proof_Only, Global => null,
     Post => Conv128 (Unsigned_128 (H)) = Conv (H);

   procedure Lemma_Ext64 (H : Unsigned_64) is
      X : constant Unsigned_128 := Unsigned_128 (H);
   begin
      Lemma_Split (X);
      pragma Assert (Proof_Only => Lo (X) = H);
      pragma Assert (Proof_Only => Hi (X) = 0);
      pragma Assert (Proof_Only => Conv (0) = 0);
   end Lemma_Ext64;

   --  Addition of 128-bit values that does not wrap.
   procedure Lemma_Add128 (X, Y : Unsigned_128) with
     Ghost => Proof_Only, Global => null,
     Pre  => X + Y >= X,
     Post => Conv128 (X + Y) = Conv128 (X) + Conv128 (Y);

   procedure Lemma_Add128 (X, Y : Unsigned_128) is
      S : constant Unsigned_128 := X + Y;
   begin
      pragma Assert (Proof_Only => S - X = Y);
      pragma Assert (Proof_Only => S >= X);
      Lemma_Sub128 (S, X);
   end Lemma_Add128;

   --  The 128-bit product of two words neither wraps nor exceeds
   --  (2^64 - 1)^2.
   procedure Lemma_Mul_Split (X, Y : Unsigned_64) with
     Ghost => Proof_Only, Global => null,
     Post => Unsigned_128 (X) * Unsigned_128 (Y)
               <= 16#FFFF_FFFF_FFFF_FFFE_0000_0000_0000_0001#
       and then Conv128 (Unsigned_128 (X) * Unsigned_128 (Y))
                = Conv (X) * Conv (Y)
       and then Conv (X) * Conv (Y) <= (Two_64 - 1) * (Two_64 - 1);

   procedure Lemma_Mul_Split (X, Y : Unsigned_64) is
   begin
      pragma Assert
        (Proof_Only =>
           Conv (X) <= Two_64 - 1 and then Conv (Y) <= Two_64 - 1);
      pragma Assert
        (Proof_Only =>
           Conv (X) * Conv (Y) <= (Two_64 - 1) * (Two_64 - 1));
   end Lemma_Mul_Split;

   --  One word of addition with carry, against the prefix sums.
   procedure Lemma_Add_Step
     (A, B, R : Word_Array; K : Natural; C_In : Unsigned_64;
      W : Unsigned_128)
   with
     Ghost => Proof_Only, Global => null,
     Pre  => A'First = 0 and then B'First = 0 and then R'First = 0
       and then A'Length = B'Length and then R'Length = A'Length
       and then A'Length <= Max_Words and then K < A'Length
       and then C_In <= 1
       and then Partial (R, K) + Conv (C_In) * Weight (K)
                = Partial (A, K) + Partial (B, K)
       and then Conv128 (W) = Conv (A (K)) + Conv (B (K)) + Conv (C_In)
       and then R (K) = Lo (W),
     Post => Hi (W) <= 1
       and then Partial (R, K + 1) + Conv (Hi (W)) * Weight (K + 1)
                = Partial (A, K + 1) + Partial (B, K + 1);

   procedure Lemma_Add_Step
     (A, B, R : Word_Array; K : Natural; C_In : Unsigned_64;
      W : Unsigned_128)
   is
   begin
      pragma Unreferenced (C_In);
      Lemma_Split (W);
      pragma Assert (Proof_Only => Conv128 (W) < Two_64 + Two_64);
      pragma Assert (Proof_Only => Hi (W) <= 1);
      pragma Assert
        (Proof_Only =>
           Conv (R (K)) = Conv128 (W) - Conv (Hi (W)) * Two_64);
      pragma Assert (Proof_Only => Weight (K + 1) = Two_64 * Weight (K));
      pragma Assert
        (Proof_Only =>
           Partial (R, K + 1) = Partial (R, K) + Conv (R (K)) * Weight (K));
      pragma Assert
        (Proof_Only =>
           Partial (A, K + 1) = Partial (A, K) + Conv (A (K)) * Weight (K));
      pragma Assert
        (Proof_Only =>
           Partial (B, K + 1) = Partial (B, K) + Conv (B (K)) * Weight (K));
   end Lemma_Add_Step;

   --  One word of subtraction with borrow, against the prefix sums.
   --  B_Out + Hi (W) = 1: the high half of A_k + 2^64 - B_k - B_In is 1
   --  exactly when no borrow is produced.
   procedure Lemma_Sub_Step
     (A, B, R : Word_Array; K : Natural; B_In, B_Out : Unsigned_64;
      W : Unsigned_128)
   with
     Ghost => Proof_Only, Global => null,
     Pre  => A'First = 0 and then B'First = 0 and then R'First = 0
       and then A'Length = B'Length and then R'Length = A'Length
       and then A'Length <= Max_Words and then K < A'Length
       and then B_In <= 1
       and then Partial (R, K)
                = Partial (A, K) - Partial (B, K) + Conv (B_In) * Weight (K)
       and then Conv128 (W)
                = Conv (A (K)) + Two_64 - Conv (B (K)) - Conv (B_In)
       and then R (K) = Lo (W)
       and then Hi (W) <= 1
       and then B_Out = 1 - Hi (W),
     Post => B_Out <= 1
       and then Partial (R, K + 1)
                = Partial (A, K + 1) - Partial (B, K + 1)
                  + Conv (B_Out) * Weight (K + 1);

   procedure Lemma_Sub_Step
     (A, B, R : Word_Array; K : Natural; B_In, B_Out : Unsigned_64;
      W : Unsigned_128)
   is
   begin
      pragma Unreferenced (B_In);
      Lemma_Split (W);
      pragma Assert
        (Proof_Only => (Hi (W) = 0 and then B_Out = 1)
         or else (Hi (W) = 1 and then B_Out = 0));
      pragma Assert (Proof_Only => Conv (0) = 0 and then Conv (1) = 1);
      pragma Assert (Proof_Only => Conv (B_Out) + Conv (Hi (W)) = 1);
      pragma Assert
        (Proof_Only =>
           Conv (R (K)) = Conv128 (W) - Conv (Hi (W)) * Two_64);
      pragma Assert (Proof_Only => Weight (K + 1) = Two_64 * Weight (K));
      pragma Assert
        (Proof_Only =>
           Partial (R, K + 1) = Partial (R, K) + Conv (R (K)) * Weight (K));
      pragma Assert
        (Proof_Only =>
           Partial (A, K + 1) = Partial (A, K) + Conv (A (K)) * Weight (K));
      pragma Assert
        (Proof_Only =>
           Partial (B, K + 1) = Partial (B, K) + Conv (B (K)) * Weight (K));
   end Lemma_Sub_Step;

   -------------------------------------------------------------------
   --  Word primitives. Loops run over compile-time bounds; nothing in
   --  the control flow depends on the data.
   -------------------------------------------------------------------

   procedure Add_Words
     (A, B : Word_Array; R : out Word_Array; Carry : out Unsigned_64)
   is
      C : Unsigned_64 := 0;
      W : Unsigned_128;
   begin
      R := [others => 0];
      for I in 0 .. A'Length - 1 loop
         W := Unsigned_128 (A (I)) + Unsigned_128 (B (I)) + Unsigned_128 (C);
         pragma Assert
           (Proof_Only =>
              Conv128 (W) = Conv (A (I)) + Conv (B (I)) + Conv (C));
         R (I) := Lo (W);
         Lemma_Add_Step (A, B, R, I, C, W);
         C := Hi (W);
         pragma Loop_Invariant (Proof_Only => C <= 1);
         pragma Loop_Invariant
           (Proof_Only => Partial (R, I + 1) + Conv (C) * Weight (I + 1)
              = Partial (A, I + 1) + Partial (B, I + 1));
      end loop;
      Carry := C;
   end Add_Words;

   procedure Sub_Words
     (A, B : Word_Array; R : out Word_Array; Borrow : out Unsigned_64)
   is
      --  Each step computes A_i + 2^64 - B_i - Borrow_in, which lies in
      --  0 .. 2^65 - 1 and never wraps; its high half is 1 exactly when
      --  no borrow is produced.
      Bw : Unsigned_64 := 0;
      W  : Unsigned_128;
      Nb : Unsigned_64;
   begin
      R := [others => 0];
      pragma Assert (Proof_Only => Conv128 (2 ** 64) = Two_64);
      for I in 0 .. A'Length - 1 loop
         pragma Assert (Proof_Only => Bw <= 1);
         declare
            U : constant Unsigned_128 := Unsigned_128 (A (I)) + 2 ** 64;
            V : constant Unsigned_128 :=
              Unsigned_128 (B (I)) + Unsigned_128 (Bw);
         begin
            pragma Assert (Proof_Only => Conv128 (U) = Conv (A (I)) + Two_64);
            pragma Assert
              (Proof_Only =>
                 Conv128 (V) = Conv (B (I)) + Conv (Bw));
            pragma Assert (Proof_Only => U >= V);
            Lemma_Sub128 (U, V);
            W := U - V;
         end;
         pragma Assert
           (Proof_Only =>
              Conv128 (W) = Conv (A (I)) + Two_64 - Conv (B (I)) - Conv (Bw));
         pragma Assert (Proof_Only => Hi (W) <= 1);
         R (I) := Lo (W);
         Nb := 1 - Hi (W);
         Lemma_Sub_Step (A, B, R, I, Bw, Nb, W);
         Bw := Nb;
         pragma Loop_Invariant (Proof_Only => Bw <= 1);
         pragma Loop_Invariant
           (Proof_Only => Partial (R, I + 1)
              = Partial (A, I + 1) - Partial (B, I + 1)
                + Conv (Bw) * Weight (I + 1));
      end loop;
      Lemma_To_Int_Bounds (R);
      Lemma_To_Int_Bounds (A);
      Lemma_To_Int_Bounds (B);
      Borrow := Bw;
   end Sub_Words;

   function Add_Limbs (A, B : Limb_Array) return Limbs_With_Carry is
      R : Limb_Array;
      C : Unsigned_64;
   begin
      Add_Words (A, B, R, C);
      return (Limbs => R, Carry => C);
   end Add_Limbs;

   function Sub_Limbs (A, B : Limb_Array) return Limbs_With_Carry is
      R : Limb_Array;
      Bw : Unsigned_64;
   begin
      Sub_Words (A, B, R, Bw);
      return (Limbs => R, Carry => Bw);
   end Sub_Limbs;

   function Select_Limbs (A, B : Limb_Array; Mask : Unsigned_64)
     return Limb_Array
   is
      Keep : constant Unsigned_64 := not Mask;
   begin
      return
        [0 => (A (0) and Keep) or (B (0) and Mask),
         1 => (A (1) and Keep) or (B (1) and Mask),
         2 => (A (2) and Keep) or (B (2) and Mask),
         3 => (A (3) and Keep) or (B (3) and Mask)];
   end Select_Limbs;

   -------------------------------------------------------------------
   --  Addition and subtraction
   -------------------------------------------------------------------

   function Add (A, B : Element) return Element is
      S  : constant Limbs_With_Carry := Add_Limbs (A.Limbs, B.Limbs);
      D  : constant Limbs_With_Carry := Sub_Limbs (S.Limbs, P_Limbs);
      --  The sum is at least p iff it overflowed 2^256 or the
      --  subtraction did not borrow.
      Ge   : constant Unsigned_64 := S.Carry or (1 - D.Carry);
      Mask : constant Unsigned_64 := 0 - Ge;
      R    : constant Limb_Array := Select_Limbs (S.Limbs, D.Limbs, Mask);
   begin
      Lemma_To_Int_Bounds (S.Limbs);
      Lemma_To_Int_Bounds (D.Limbs);
      pragma Assert
        (Proof_Only =>
           To_Int (A.Limbs) < P and then To_Int (B.Limbs) < P);
      Lemma_To_Int_Bounds (A.Limbs);
      Lemma_To_Int_Bounds (B.Limbs);
      pragma Assert (Proof_Only => Ge <= 1);
      --  Sum below 2 p: if it overflowed, the low part is below p.
      pragma Assert (Proof_Only => (if S.Carry = 1 then D.Carry = 1));
      pragma Assert
        (Proof_Only => (if Ge = 1 then
           To_Int (R) = To_Int (A.Limbs) + To_Int (B.Limbs) - P
         else
           To_Int (R) = To_Int (A.Limbs) + To_Int (B.Limbs)));
      pragma Assert (Proof_Only => To_Int (R) >= 0 and then To_Int (R) < P);
      return (Limbs => R);
   end Add;

   function Sub (A, B : Element) return Element is
      D    : constant Limbs_With_Carry := Sub_Limbs (A.Limbs, B.Limbs);
      F    : constant Limbs_With_Carry := Add_Limbs (D.Limbs, P_Limbs);
      Mask : constant Unsigned_64 := 0 - D.Carry;
      R    : constant Limb_Array := Select_Limbs (D.Limbs, F.Limbs, Mask);
   begin
      Lemma_To_Int_Bounds (D.Limbs);
      Lemma_To_Int_Bounds (F.Limbs);
      pragma Assert
        (Proof_Only =>
           To_Int (A.Limbs) < P and then To_Int (B.Limbs) < P);
      Lemma_To_Int_Bounds (A.Limbs);
      Lemma_To_Int_Bounds (B.Limbs);
      --  If the difference borrowed, adding p back overflows 2^256
      --  exactly once and yields A - B + p.
      pragma Assert (Proof_Only => (if D.Carry = 1 then F.Carry = 1));
      pragma Assert
        (Proof_Only => (if D.Carry = 1 then
           To_Int (R) = To_Int (A.Limbs) - To_Int (B.Limbs) + P
         else
           To_Int (R) = To_Int (A.Limbs) - To_Int (B.Limbs)));
      pragma Assert (Proof_Only => To_Int (R) >= 0 and then To_Int (R) < P);
      return (Limbs => R);
   end Sub;

   -------------------------------------------------------------------
   --  Multiplication, stage 1: the 512-bit product (ADR 0013).
   -------------------------------------------------------------------

   --  64 x 64 -> 128 bit product, exact. The call site only sees the
   --  postcondition, which keeps 128-bit multiplication out of the
   --  callers' proofs.
   function Wide_Mul (X, Y : Unsigned_64) return Unsigned_128 with
     Global => null,
     Post   =>
       (Proof_Only =>
          Wide_Mul'Result <= 16#FFFF_FFFF_FFFF_FFFE_0000_0000_0000_0001#
  and then Conv128 (Wide_Mul'Result) = Conv (X) * Conv (Y)
  and then Conv128 (Wide_Mul'Result) <= (Two_64 - 1) * (Two_64 - 1));

   function Wide_Mul (X, Y : Unsigned_64) return Unsigned_128 is
      R : constant Unsigned_128 := Unsigned_128 (X) * Unsigned_128 (Y);
   begin
      Lemma_Mul_Split (X, Y);
      return R;
   end Wide_Mul;

   --  One word of a row product: the prefix identity extends from K to
   --  K + 1 words.
   procedure Lemma_Row_Step
     (X : Unsigned_64; B : Limb_Array; R : Five_Array; K : Natural;
      C_In : Unsigned_64; W : Unsigned_128)
   with
     Ghost => Proof_Only, Global => null,
     Pre  => K <= 3
       and then Partial (R, K) + Conv (C_In) * Weight (K)
                = Conv (X) * Partial (B, K)
       and then Conv128 (W) = Conv (X) * Conv (B (K)) + Conv (C_In)
       and then R (K) = Lo (W),
     Post => Partial (R, K + 1) + Conv (Hi (W)) * Weight (K + 1)
             = Conv (X) * Partial (B, K + 1);

   procedure Lemma_Row_Step
     (X : Unsigned_64; B : Limb_Array; R : Five_Array; K : Natural;
      C_In : Unsigned_64; W : Unsigned_128)
   is
   begin
      pragma Unreferenced (C_In);
      pragma Assert (Proof_Only => Conv (X) >= 0);
      Lemma_Split (W);
      pragma Assert
        (Proof_Only =>
           Conv (R (K)) = Conv128 (W) - Conv (Hi (W)) * Two_64);
      pragma Assert (Proof_Only => Weight (K + 1) = Two_64 * Weight (K));
      pragma Assert
        (Proof_Only =>
           Partial (R, K + 1) = Partial (R, K) + Conv (R (K)) * Weight (K));
      pragma Assert
        (Proof_Only =>
           Partial (B, K + 1) = Partial (B, K) + Conv (B (K)) * Weight (K));
   end Lemma_Row_Step;

   --  One row of the schoolbook product: X times the four limbs of B,
   --  as five words.
   function Mul_Row (X : Unsigned_64; B : Limb_Array) return Five_Array
   with
     Global => null,
     Inline,
     Post   => (Proof_Only => To_Int (Mul_Row'Result) = Conv (X) * To_Int (B));

   function Mul_Row (X : Unsigned_64; B : Limb_Array) return Five_Array is
      P0 : constant Unsigned_128 := Wide_Mul (X, B (0));
      P1 : constant Unsigned_128 := Wide_Mul (X, B (1));
      P2 : constant Unsigned_128 := Wide_Mul (X, B (2));
      P3 : constant Unsigned_128 := Wide_Mul (X, B (3));
      --  Each product is at most (2^64 - 1)^2, so adding a carry below
      --  2^64 never wraps.
      W0 : constant Unsigned_128 := P0;
      W1 : constant Unsigned_128 := P1 + Unsigned_128 (Hi (W0));
      W2 : constant Unsigned_128 := P2 + Unsigned_128 (Hi (W1));
      W3 : constant Unsigned_128 := P3 + Unsigned_128 (Hi (W2));
      R  : constant Five_Array :=
        [Lo (W0), Lo (W1), Lo (W2), Lo (W3), Hi (W3)];
   begin
      pragma Assert (Proof_Only => Conv (0) = 0);
      pragma Assert
        (Proof_Only =>
           Partial (R, 0) = 0 and then Partial (B, 0) = 0);
      pragma Assert
        (Proof_Only =>
           Conv128 (W0) = Conv (X) * Conv (B (0)) + Conv (0));
      Lemma_Row_Step (X, B, R, 0, 0, W0);
      pragma Assert (Proof_Only => P1 + Unsigned_128 (Hi (W0)) >= P1);
      Lemma_Add128 (P1, Unsigned_128 (Hi (W0)));
      Lemma_Ext64 (Hi (W0));
      pragma Assert
        (Proof_Only =>
           Conv128 (W1) = Conv (X) * Conv (B (1)) + Conv (Hi (W0)));
      Lemma_Row_Step (X, B, R, 1, Hi (W0), W1);
      pragma Assert (Proof_Only => P2 + Unsigned_128 (Hi (W1)) >= P2);
      Lemma_Add128 (P2, Unsigned_128 (Hi (W1)));
      Lemma_Ext64 (Hi (W1));
      pragma Assert
        (Proof_Only =>
           Conv128 (W2) = Conv (X) * Conv (B (2)) + Conv (Hi (W1)));
      Lemma_Row_Step (X, B, R, 2, Hi (W1), W2);
      pragma Assert (Proof_Only => P3 + Unsigned_128 (Hi (W2)) >= P3);
      Lemma_Add128 (P3, Unsigned_128 (Hi (W2)));
      Lemma_Ext64 (Hi (W2));
      pragma Assert
        (Proof_Only =>
           Conv128 (W3) = Conv (X) * Conv (B (3)) + Conv (Hi (W2)));
      Lemma_Row_Step (X, B, R, 3, Hi (W2), W3);
      pragma Assert
        (Proof_Only =>
           Partial (R, 5) = Partial (R, 4) + Conv (R (4)) * Weight (4));
      return R;
   end Mul_Row;

   --  Equal limbs denote equal values (stated element-wise, so that the
   --  proof does not rely on array extensionality).
   procedure Lemma_To_Int_Eq (A, B : Limb_Array) with
     Ghost => Proof_Only, Global => null,
     Pre  => (for all I in Limb_Index => A (I) = B (I)),
     Post => To_Int (A) = To_Int (B);

   procedure Lemma_To_Int_Eq (A, B : Limb_Array) is
   begin
      pragma Assert
        (Proof_Only => A (0) = B (0) and then A (1) = B (1)
         and then A (2) = B (2) and then A (3) = B (3));
      pragma Assert
        (Proof_Only => Partial (A, 4)
           = Conv (A (0)) * Weight (0) + Conv (A (1)) * Weight (1)
           + Conv (A (2)) * Weight (2) + Conv (A (3)) * Weight (3));
      pragma Assert
        (Proof_Only => Partial (B, 4)
           = Conv (B (0)) * Weight (0) + Conv (B (1)) * Weight (1)
           + Conv (B (2)) * Weight (2) + Conv (B (3)) * Weight (3));
   end Lemma_To_Int_Eq;

   --  If A * B < K * B with B > 0 then A < K.
   procedure Lemma_Div_Bound (A, B, K : Big_Integer) with
     Ghost => Proof_Only, Global => null,
     Pre  => B > 0 and then A >= 0 and then A * B < K * B,
     Post => A < K;

   procedure Lemma_Div_Bound (A, B, K : Big_Integer) is
   begin
      if A >= K then
         pragma Assert (Proof_Only => A * B >= K * B);
         pragma Assert (Proof_Only => False);
      end if;
   end Lemma_Div_Bound;

   --  A value that differs from X by a multiple of p and lies in
   --  0 .. p - 1 is X mod p.
   procedure Lemma_Mod_Multiple (X, R, M : Big_Integer) with
     Ghost => Proof_Only, Global => null,
     Pre  => P > 0 and then R = X + M * P and then R >= 0 and then R < P,
     Post => R = X mod P;

   procedure Lemma_Mod_Multiple (X, R, M : Big_Integer) is
   begin
      pragma Assert (Proof_Only => X = R - M * P);
      pragma Assert (Proof_Only => X mod P = (R - M * P) mod P);
      pragma Assert (Proof_Only => (R - M * P) mod P = R mod P);
      pragma Assert (Proof_Only => R mod P = R);
   end Lemma_Mod_Multiple;

   ----------------------------------------------------------------------
   --  The product is associative (ADR 0066), from
   --  the integer model: the laws of the remainder, and To_Int one to
   --  one on four limbs, digit by digit in base 2^64.
   ----------------------------------------------------------------------

   --  Two words above a digit: c + W x = d + W y with digits below W.
   procedure Lemma_Digit (C1, C2, X1, X2, W : Big_Integer) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => W > 0 and then C1 >= 0 and then C1 < W
               and then C2 >= 0 and then C2 < W
               and then C1 + W * X1 = C2 + W * X2,
     Post   => C1 = C2 and then X1 = X2
   is
      K : constant Big_Integer := X1 - X2;
   begin
      pragma Assert (W * K = C2 - C1);
      if K >= 1 then
         pragma Assert (W * K >= W);
      elsif K <= -1 then
         pragma Assert (W * K <= -W);
      end if;
      pragma Assert (K = 0);
   end Lemma_Digit;

   --  The remainder is the unique digit below M.
   procedure Lemma_Mod_Unique (A, T, Rm, M : Big_Integer) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => M > 0 and then A >= 0 and then Rm >= 0 and then Rm < M
               and then A = Rm + M * T,
     Post   => A mod M = Rm
   is
   begin
      pragma Assert (A = (A / M) * M + A mod M);
      pragma Assert (A = A mod M + M * (A / M));
      Lemma_Digit (A mod M, Rm, A / M, T, M);
   end Lemma_Mod_Unique;

   --  A remainder may be taken early in a product.
   procedure Lemma_Mod_Mul (X, C, M : Big_Integer) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => X >= 0 and then C >= 0 and then M > 0,
     Post   => ((X mod M) * C) mod M = (X * C) mod M
   is
      Q  : constant Big_Integer := X / M;
      Rm : constant Big_Integer := X mod M;
      Q2 : constant Big_Integer := (Rm * C) / M;
      R2 : constant Big_Integer := (Rm * C) mod M;
   begin
      pragma Assert (X = Q * M + Rm);
      pragma Assert (Rm * C = Q2 * M + R2);
      pragma Assert (X = Rm + M * Q);
      pragma Assert (Rm * C = R2 + M * Q2);
      pragma Assert (X * C = R2 + M * (Q * C + Q2));
      Lemma_Mod_Unique (X * C, Q * C + Q2, R2, M);
   end Lemma_Mod_Mul;

   procedure Lemma_Conv_Bounds (X : Unsigned_64) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Conv (X) >= 0 and then Conv (X) < Two_64
   is
   begin
      null;
   end Lemma_Conv_Bounds;

   procedure Lemma_Conv_Inj (X, Y : Unsigned_64) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Conv (X) = Conv (Y),
     Post   => X = Y
   is
   begin
      null;
   end Lemma_Conv_Inj;

   procedure Lemma_Weights with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Weight (0) = 1
               and then Weight (1) = Two_64
               and then Weight (2) = Two_64 * Two_64
               and then Weight (3) = Two_64 * Two_64 * Two_64
               and then Two_64 > 0
   is
   begin
      pragma Assert (Weight (1) = Two_64 * Weight (0));
      pragma Assert (Weight (2) = Two_64 * Weight (1));
      pragma Assert (Weight (3) = Two_64 * Weight (2));
   end Lemma_Weights;

   --  The value of four limbs in Horner form.
   procedure Lemma_Horner (L : Limb_Array) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => To_Int (L)
               = Conv (L (0))
                 + Two_64 * (Conv (L (1))
                             + Two_64 * (Conv (L (2))
                                         + Two_64 * Conv (L (3))))
   is
   begin
      Lemma_Weights;
      pragma Assert
        (To_Int (L) = Conv (L (0)) * Weight (0) + Conv (L (1)) * Weight (1)
                      + Conv (L (2)) * Weight (2) + Conv (L (3)) * Weight (3));
   end Lemma_Horner;

   procedure Lemma_Inj (A, B : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => To_Int (A.Limbs) = To_Int (B.Limbs),
     Post   => A = B
   is
      W  : constant Big_Integer := Two_64;
      A0 : constant Big_Integer := Conv (A.Limbs (0));
      A1 : constant Big_Integer := Conv (A.Limbs (1));
      A2 : constant Big_Integer := Conv (A.Limbs (2));
      A3 : constant Big_Integer := Conv (A.Limbs (3));
      B0 : constant Big_Integer := Conv (B.Limbs (0));
      B1 : constant Big_Integer := Conv (B.Limbs (1));
      B2 : constant Big_Integer := Conv (B.Limbs (2));
      B3 : constant Big_Integer := Conv (B.Limbs (3));
   begin
      Lemma_Weights;
      Lemma_Horner (A.Limbs);
      Lemma_Horner (B.Limbs);
      for I in Limb_Index loop
         Lemma_Conv_Bounds (A.Limbs (I));
         Lemma_Conv_Bounds (B.Limbs (I));
      end loop;
      Lemma_Digit (A0, B0, A1 + W * (A2 + W * A3), B1 + W * (B2 + W * B3), W);
      Lemma_Digit (A1, B1, A2 + W * A3, B2 + W * B3, W);
      Lemma_Digit (A2, B2, A3, B3, W);
      for I in Limb_Index loop
         Lemma_Conv_Inj (A.Limbs (I), B.Limbs (I));
      end loop;
      pragma Assert (A.Limbs = B.Limbs);
   end Lemma_Inj;

   -------------------------------------------------------------------
   --  Multiplication in Montgomery form (ADR 0069)
   -------------------------------------------------------------------

   procedure Lemma_R_Inv is
      W : constant Big_Integer := Two_64;
   begin
      pragma Assert (Proof_Only => Weight (1) = W * Weight (0));
      pragma Assert (Proof_Only => Weight (2) = W * Weight (1));
      pragma Assert (Proof_Only => Weight (3) = W * Weight (2));
      pragma Assert (Proof_Only => Weight (4) = W * Weight (3));
      pragma Assert (Proof_Only => W = 18446744073709551616);
      pragma Assert (Proof_Only => Two_256 = W * W * W * W);
      pragma Assert (Proof_Only => To_Int (RI_Limbs)
        = Conv (RI_Limbs (0)) + Conv (RI_Limbs (1)) * W
          + Conv (RI_Limbs (2)) * W * W + Conv (RI_Limbs (3)) * W * W * W);
      pragma Assert (Proof_Only => To_Int (K_Limbs)
        = Conv (K_Limbs (0)) + Conv (K_Limbs (1)) * W
          + Conv (K_Limbs (2)) * W * W + Conv (K_Limbs (3)) * W * W * W);
      pragma Assert (Proof_Only => P
        = Conv (P_Limbs (0)) + Conv (P_Limbs (1)) * W
          + Conv (P_Limbs (2)) * W * W + Conv (P_Limbs (3)) * W * W * W);
   end Lemma_R_Inv;

   -------------------------------------------------------------------
   --  Montgomery multiplication (ADR 0069)
   -------------------------------------------------------------------

   subtype Six_Array is Word_Array (0 .. 5);

   --  p as W P1 - 1 with W = 2^64, P1 = (p + 1) / 2^64; and p < 2^256.
   P1_Limbs : constant Limb_Array :=
     [16#0000000100000000#, 16#0000000000000000#,
      16#FFFFFFFF00000001#, 16#0000000000000000#];

   procedure Lemma_P1 with
     Ghost => Proof_Only, Global => null,
     Post => P = Two_64 * To_Int (P1_Limbs) - 1 and then P > 0
       and then P < Two_256 and then To_Int (P1_Limbs) >= 0;

   procedure Lemma_P1 is
      W : constant Big_Integer := Two_64;
   begin
      Lemma_Unfold;
      pragma Assert (Proof_Only => W = 18446744073709551616);
      pragma Assert (Proof_Only => To_Int (P1_Limbs)
        = Conv (P1_Limbs (0)) + Conv (P1_Limbs (1)) * W
          + Conv (P1_Limbs (2)) * W * W + Conv (P1_Limbs (3)) * W * W * W);
      pragma Assert (Proof_Only => P
        = Conv (P_Limbs (0)) + Conv (P_Limbs (1)) * W
          + Conv (P_Limbs (2)) * W * W + Conv (P_Limbs (3)) * W * W * W);
   end Lemma_P1;

   --  Six words: the low word and the five above it, one word down.
   function Down (S : Six_Array) return Six_Array is
     [S (1), S (2), S (3), S (4), S (5), 0]
   with Global => null;

   procedure Lemma_Down (S : Six_Array) with
     Ghost => Proof_Only, Global => null,
     Post => To_Int (S) = Conv (S (0)) + Two_64 * To_Int (Down (S));

   procedure Lemma_Down (S : Six_Array) is
      D : constant Six_Array := Down (S);
   begin
      Lemma_Unfold;
      pragma Assert (Proof_Only => To_Int (S)
        = Conv (S (0)) + Conv (S (1)) * Weight (1) + Conv (S (2)) * Weight (2)
          + Conv (S (3)) * Weight (3) + Conv (S (4)) * Weight (4)
          + Conv (S (5)) * Weight (5));
      pragma Assert (Proof_Only => To_Int (D)
        = Conv (D (0)) + Conv (D (1)) * Weight (1) + Conv (D (2)) * Weight (2)
          + Conv (D (3)) * Weight (3) + Conv (D (4)) * Weight (4)
          + Conv (D (5)) * Weight (5));
   end Lemma_Down;

   function Ext6 (V : Five_Array) return Six_Array is
     [V (0), V (1), V (2), V (3), V (4), 0]
   with Global => null;

   procedure Lemma_Ext6 (V : Five_Array) with
     Ghost => Proof_Only, Global => null,
     Post => To_Int (Ext6 (V)) = To_Int (V);

   procedure Lemma_Ext6 (V : Five_Array) is
      X : constant Six_Array := Ext6 (V);
   begin
      Lemma_Unfold;
      pragma Assert (Proof_Only => To_Int (X)
        = Conv (X (0)) + Conv (X (1)) * Weight (1) + Conv (X (2)) * Weight (2)
          + Conv (X (3)) * Weight (3) + Conv (X (4)) * Weight (4)
          + Conv (X (5)) * Weight (5));
      pragma Assert (Proof_Only => To_Int (V)
        = Conv (V (0)) + Conv (V (1)) * Weight (1) + Conv (V (2)) * Weight (2)
          + Conv (V (3)) * Weight (3) + Conv (V (4)) * Weight (4));
   end Lemma_Ext6;

   --  The shifted copies of R that add up to R p: V carries
   --  R (2^96 + 2^192 + 2^256), U carries R (1 + 2^224).
   function V_Of (R : Unsigned_64) return Six_Array is
     [0, Shift_Left (R, 32), Shift_Right (R, 32), R, R, 0]
   with Global => null;

   function U_Of (R : Unsigned_64) return Six_Array is
     [R, 0, 0, Shift_Left (R, 32), Shift_Right (R, 32), 0]
   with Global => null;

   procedure Lemma_VU (R : Unsigned_64) with
     Ghost => Proof_Only, Global => null,
     Post => To_Int (V_Of (R)) - To_Int (U_Of (R)) = Conv (R) * P
       and then To_Int (V_Of (R)) <= Conv (R) * (Two_64 * Two_256)
       and then To_Int (U_Of (R)) >= 0;

   procedure Lemma_VU (R : Unsigned_64) is
      V  : constant Six_Array := V_Of (R);
      U  : constant Six_Array := U_Of (R);
      Lo_R : constant Unsigned_64 := Shift_Left (R, 32);
      Hi_R : constant Unsigned_64 := Shift_Right (R, 32);
      X    : constant Unsigned_128 :=
        Unsigned_128 (R) * Unsigned_128 (Unsigned_64'(2 ** 32));
      W  : constant Big_Integer := Two_64;
      T  : constant Big_Integer := Two_32;
   begin
      Lemma_Unfold;
      --  R 2^32 as a 128-bit value: its halves are Lo and Hi.
      Lemma_Mul_Split (R, 2 ** 32);
      Lemma_Split (X);
      pragma Assert (Proof_Only => Lo (X) = Lo_R and then Hi (X) = Hi_R);
      pragma Assert (Proof_Only => Conv (2 ** 32) = T);
      pragma Assert
        (Proof_Only => Conv (Lo_R) + Conv (Hi_R) * W = Conv (R) * T);
      pragma Assert (Proof_Only => To_Int (V)
        = Conv (Lo_R) * W + Conv (Hi_R) * W * W + Conv (R) * W * W * W
          + Conv (R) * W * W * W * W);
      pragma Assert (Proof_Only => To_Int (U)
        = Conv (R) + Conv (Lo_R) * W * W * W + Conv (Hi_R) * W * W * W * W);
      pragma Assert (Proof_Only => W = 18446744073709551616);
      pragma Assert (Proof_Only => T = 4294967296);
      pragma Assert (Proof_Only => P
        = Conv (P_Limbs (0)) + Conv (P_Limbs (1)) * W
          + Conv (P_Limbs (2)) * W * W + Conv (P_Limbs (3)) * W * W * W);
      pragma Assert (Proof_Only => P
        = W * W * W * W - T * W * W * W + W * W * W + T * W - 1);
      pragma Assert (Proof_Only =>
        To_Int (V) = Conv (R) * (T * W + W * W * W + W * W * W * W));
      pragma Assert (Proof_Only =>
        To_Int (U) = Conv (R) * (1 + T * W * W * W));
      pragma Assert (Proof_Only => Conv (R) >= 0);
   end Lemma_VU;

   --  One round: T + X B, then R p added with R the low word, which
   --  clears it, then one word down. The value divided by 2^64 stays
   --  below 2 p.
   procedure Round
     (T : in out Six_Array; X : Unsigned_64; B : Limb_Array;
      R : out Unsigned_64)
   with
     Global => null,
     Inline,
     Pre    => (Proof_Only => To_Int (B) < P and then To_Int (T) < 2 * P),
     Post   => (Proof_Only => To_Int (T) < 2 * P
                and then To_Int (T) * Two_64
                         = To_Int (T'Old) + Conv (X) * To_Int (B)
                           + Conv (R) * P);

   procedure Round
     (T : in out Six_Array; X : Unsigned_64; B : Limb_Array;
      R : out Unsigned_64)
   is
      Row : constant Five_Array := Mul_Row (X, B);
      S, S2, S3 : Six_Array;
      C, C2, Bw : Unsigned_64;
      T0 : constant Six_Array := T with Ghost => Proof_Only;
   begin
      Lemma_Unfold;
      Lemma_P1;
      Lemma_To_Int_Bounds (T);
      Lemma_To_Int_Bounds (B);
      Lemma_Conv_Bounds (X);
      Lemma_Ext6 (Row);
      Add_Words (T, Ext6 (Row), S, C);
      pragma Assert (Proof_Only => Conv (X) * To_Int (B) <= (Two_64 - 1) * P);
      pragma Assert
        (Proof_Only => To_Int (T) + To_Int (Ext6 (Row)) < Weight (6));
      Lemma_To_Int_Bounds (S);
      pragma Assert (Proof_Only => C = 0);
      pragma Assert
        (Proof_Only => To_Int (S) = To_Int (T0) + Conv (X) * To_Int (B));
      R := S (0);
      Lemma_VU (R);
      Lemma_Conv_Bounds (R);
      Add_Words (S, V_Of (R), S2, C2);
      pragma Assert
        (Proof_Only => To_Int (S) + To_Int (V_Of (R)) < Weight (6));
      Lemma_To_Int_Bounds (S2);
      pragma Assert (Proof_Only => C2 = 0);
      Sub_Words (S2, U_Of (R), S3, Bw);
      pragma Assert (Proof_Only => To_Int (S2) - To_Int (U_Of (R))
                     = To_Int (S) + Conv (R) * P);
      pragma Assert (Proof_Only => Bw = 0);
      pragma Assert (Proof_Only => To_Int (S3) = To_Int (S) + Conv (R) * P);
      --  The low word of S3 is zero: S = R + W s', p = W P1 - 1.
      Lemma_Down (S);
      Lemma_Down (S3);
      Lemma_Conv_Bounds (S3 (0));
      pragma Assert (Proof_Only => Conv (S (0)) = Conv (R));
      pragma Assert (Proof_Only => To_Int (S3)
        = Conv (R) + Two_64 * To_Int (Down (S)) + Conv (R) * P);
      pragma Assert (Proof_Only =>
        Conv (R) * P = Conv (R) * (Two_64 * To_Int (P1_Limbs)) - Conv (R));
      pragma Assert (Proof_Only => To_Int (S3)
        = Two_64 * To_Int (Down (S))
          + Conv (R) * (Two_64 * To_Int (P1_Limbs)));
      pragma Assert (Proof_Only => To_Int (S3)
        = Two_64 * (To_Int (Down (S)) + Conv (R) * To_Int (P1_Limbs)));
      Lemma_Digit (Conv (S3 (0)), To_Big_Integer (0),
                   To_Int (Down (S3)),
                   To_Int (Down (S)) + Conv (R) * To_Int (P1_Limbs), Two_64);
      T := Down (S3);
      pragma Assert (Proof_Only => To_Int (T) * Two_64 = To_Int (S3));
      --  Bound: T W = T0 + X B + R p < 2 p + (W - 1) p + (W - 1) p.
      pragma Assert (Proof_Only => Conv (R) * P <= (Two_64 - 1) * P);
      pragma Assert (Proof_Only => To_Int (T) * Two_64 < (2 * P) * Two_64);
      Lemma_To_Int_Bounds (T);
      Lemma_Div_Bound (To_Int (T), Two_64, 2 * P);
   end Round;

   --  Six words as their low four and the two above.
   procedure Lemma_Six_Split (T : Six_Array; L : Limb_Array) with
     Ghost => Proof_Only, Global => null,
     Pre  => (for all I in Limb_Index => L (I) = T (I)),
     Post => To_Int (T)
             = To_Int (L) + Conv (T (4)) * Weight (4)
               + Conv (T (5)) * Weight (5);

   procedure Lemma_Six_Split (T : Six_Array; L : Limb_Array) is
   begin
      pragma Assert (Proof_Only => To_Int (T)
        = Conv (T (0)) * Weight (0) + Conv (T (1)) * Weight (1)
          + Conv (T (2)) * Weight (2) + Conv (T (3)) * Weight (3)
          + Conv (T (4)) * Weight (4) + Conv (T (5)) * Weight (5));
      pragma Assert (Proof_Only => To_Int (L)
        = Conv (L (0)) * Weight (0) + Conv (L (1)) * Weight (1)
          + Conv (L (2)) * Weight (2) + Conv (L (3)) * Weight (3));
   end Lemma_Six_Split;

   --  The last step of Mont_Mul: T 2^256 = A B + Q p and Res = T - G p
   --  in 0 .. p - 1 give Res = A B 2^-256 mod p.
   procedure Lemma_Mont_Final
     (A, B : Limb_Array; Tv, Q, G : Big_Integer; Res : Limb_Array)
   with
     Ghost => Proof_Only, Global => null,
     Pre  => Tv * Two_256 = To_Int (A) * To_Int (B) + Q * P
       and then To_Int (Res) = Tv - G * P
       and then To_Int (Res) >= 0 and then To_Int (Res) < P,
     Post => To_Int (Res) = (To_Int (A) * To_Int (B) * R_Inv) mod P;

   procedure Lemma_Mont_Final
     (A, B : Limb_Array; Tv, Q, G : Big_Integer; Res : Limb_Array)
   is
      X : constant Big_Integer := To_Int (A) * To_Int (B);
      K : constant Big_Integer := To_Int (K_Limbs);
   begin
      Lemma_R_Inv;
      Lemma_P1;
      pragma Assert (Tv = Tv * (Two_256 * R_Inv) - Tv * K * P);
      pragma Assert (Tv * (Two_256 * R_Inv) = (Tv * Two_256) * R_Inv);
      pragma Assert (Tv = X * R_Inv + (Q * R_Inv - Tv * K) * P);
      pragma Assert (To_Int (Res) = X * R_Inv + (Q * R_Inv - Tv * K - G) * P);
      Lemma_Mod_Multiple (X * R_Inv, To_Int (Res), Q * R_Inv - Tv * K - G);
   end Lemma_Mont_Final;

   --  The Montgomery product of upstream (fp_generic.rs montgomery_mul,
   --  p256_64.rs p256_reduction_step): A B 2^-256 mod p, B below p.
   function Mont_Mul (A, B : Limb_Array) return Limb_Array with
     Global => null,
     Pre    => (Proof_Only => To_Int (B) < P),
     Post   => (Proof_Only => To_Int (Mont_Mul'Result) < P
                and then To_Int (Mont_Mul'Result)
                         = (To_Int (A) * To_Int (B) * R_Inv) mod P);

   function Mont_Mul (A, B : Limb_Array) return Limb_Array is
      T    : Six_Array := [others => 0];
      R    : Unsigned_64;
      Q    : Big_Integer := To_Big_Integer (0) with Ghost => Proof_Only;
      L    : Limb_Array;
      D    : Limbs_With_Carry;
      Ge   : Unsigned_64;
      Mask : Unsigned_64;
      Res  : Limb_Array;
   begin
      Lemma_Unfold;
      Lemma_P1;
      pragma Assert (Proof_Only => To_Int (T) = 0);
      for I in Limb_Index loop
         pragma Loop_Invariant
           (Proof_Only => To_Int (T) < 2 * P and then Q >= 0
            and then To_Int (T) * Weight (I)
                     = Partial (A, I) * To_Int (B) + Q * P);
         Round (T, A (I), B, R);
         pragma Assert (Proof_Only =>
           Partial (A, I + 1) = Partial (A, I) + Conv (A (I)) * Weight (I));
         pragma Assert (Proof_Only => Weight (I + 1) = Two_64 * Weight (I));
         Lemma_Conv_Bounds (R);
         Q := Q + Conv (R) * Weight (I);
         pragma Assert (Proof_Only =>
           To_Int (T) * Weight (I + 1)
           = Partial (A, I + 1) * To_Int (B) + Q * P);
      end loop;
      pragma Assert (Proof_Only =>
        To_Int (T) * Two_256 = To_Int (A) * To_Int (B) + Q * P);
      --  T < 2 p < 2^257: word 5 is zero and word 4 at most one.
      L := [T (0), T (1), T (2), T (3)];
      Lemma_Six_Split (T, L);
      Lemma_To_Int_Bounds (L);
      Lemma_Conv_Bounds (T (4));
      Lemma_Conv_Bounds (T (5));
      pragma Assert (Proof_Only => Weight (5) = Two_256 * Two_64);
      pragma Assert (Proof_Only => 2 * P < 2 * Two_256);
      pragma Assert (Proof_Only => Conv (T (5)) * Weight (5) <= To_Int (T));
      pragma Assert (Proof_Only => Conv (T (5)) * Weight (5) < 1 * Weight (5));
      Lemma_Div_Bound (Conv (T (5)), Weight (5), To_Big_Integer (1));
      pragma Assert (Proof_Only => T (5) = 0);
      pragma Assert (Proof_Only => Conv (T (4)) * Two_256 <= To_Int (T));
      pragma Assert (Proof_Only => Conv (T (4)) * Two_256 < 2 * Two_256);
      Lemma_Div_Bound (Conv (T (4)), Two_256, To_Big_Integer (2));
      pragma Assert (Proof_Only => T (5) = 0 and then T (4) <= 1);
      D    := Sub_Limbs (L, P_Limbs);
      Ge   := T (4) or (1 - D.Carry);
      Mask := 0 - Ge;
      Res  := Select_Limbs (L, D.Limbs, Mask);
      Lemma_To_Int_Bounds (D.Limbs);
      pragma Assert (Proof_Only => (if T (4) = 1 then D.Carry = 1));
      pragma Assert
        (Proof_Only => To_Int (T) = To_Int (L) + Conv (T (4)) * Two_256);
      if Ge = 1 then
         pragma Assert (Proof_Only => Res = D.Limbs);
         Lemma_To_Int_Eq (Res, D.Limbs);
         if T (4) = 1 then
            pragma Assert (Proof_Only => To_Int (D.Limbs)
                           = To_Int (L) - P + Two_256);
         else
            pragma Assert (Proof_Only => D.Carry = 0);
            pragma Assert (Proof_Only => To_Int (D.Limbs) = To_Int (L) - P);
         end if;
         pragma Assert (Proof_Only => To_Int (Res) = To_Int (T) - P);
      else
         pragma Assert (Proof_Only => Res = L);
         Lemma_To_Int_Eq (Res, L);
         pragma Assert (Proof_Only => T (4) = 0);
         pragma Assert (Proof_Only => To_Int (Res) = To_Int (T));
      end if;
      pragma Assert
        (Proof_Only => (if Ge = 1 then To_Int (Res) = To_Int (T) - P
                        else To_Int (Res) = To_Int (T)));
      pragma Assert
        (Proof_Only => To_Int (Res) >= 0 and then To_Int (Res) < P);
      Lemma_Mont_Final
        (A, B, To_Int (T), Q,
         (if Ge = 1 then To_Big_Integer (1) else To_Big_Integer (0)), Res);
      return Res;
   end Mont_Mul;

   function Mul (A, B : Element) return Element is
      R : constant Limb_Array := Mont_Mul (A.Limbs, B.Limbs);
      E : constant Element := Norm ((Limbs => R));
   begin
      Lemma_To_Int_Eq (E.Limbs, R);
      return E;
   end Mul;

   -------------------------------------------------------------------
   --  Inversion (ADR 0016)
   -------------------------------------------------------------------

   --  E^(2^N): N successive squarings. Local helper.
   function Square_N (E : Element; N : Positive) return Element with
     Global => null;

   function Square_N (E : Element; N : Positive) return Element is
      R : Element := E;
   begin
      for I in 1 .. N loop
         R := Square (R);
      end loop;
      return R;
   end Square_N;

   function Inv (E : Element) return Element is
      --  X_k denotes E^(2^k - 1); the exponent p - 2 is then assembled
      --  32-bit word by word:
      --    ffffffff 00000001 00000000 00000000 00000000 ffffffff
      --    ffffffff fffffffd.
      X1  : constant Element := E;
      X2  : constant Element := Mul (Square_N (X1, 1), X1);
      X3  : constant Element := Mul (Square_N (X2, 1), X1);
      X6  : constant Element := Mul (Square_N (X3, 3), X3);
      X12 : constant Element := Mul (Square_N (X6, 6), X6);
      X15 : constant Element := Mul (Square_N (X12, 3), X3);
      X30 : constant Element := Mul (Square_N (X15, 15), X15);
      X32 : constant Element := Mul (Square_N (X30, 2), X2);
      R0  : constant Element := Mul (Square_N (X32, 32), X1);  --  00000001
      R1  : constant Element := Square_N (R0, 96);   --  three zero words
      R2  : constant Element := Mul (Square_N (R1, 32), X32);  --  ffffffff
      R3  : constant Element := Mul (Square_N (R2, 32), X32);  --  ffffffff
      R4  : constant Element := Mul (Square_N (R3, 30), X30);  --  30 ones
   begin
      return Mul (Square_N (R4, 2), X1);                        --  01
   end Inv;

   -------------------------------------------------------------------
   --  Encoding
   -------------------------------------------------------------------

   function Limb_Of_8 (B : Bytes_8) return Unsigned_64 is
     (Unsigned_64 (B (0))
      or Shift_Left (Unsigned_64 (B (1)), 8)
      or Shift_Left (Unsigned_64 (B (2)), 16)
      or Shift_Left (Unsigned_64 (B (3)), 24)
      or Shift_Left (Unsigned_64 (B (4)), 32)
      or Shift_Left (Unsigned_64 (B (5)), 40)
      or Shift_Left (Unsigned_64 (B (6)), 48)
      or Shift_Left (Unsigned_64 (B (7)), 56));

   function Byte_Of (L : Unsigned_64; K : Natural) return Unsigned_8 is
     (Unsigned_8 (Shift_Right (L, 8 * K) and 16#FF#))
   with Global => null, Pre => K <= 7;

   function Bytes_Of_Limb (L : Unsigned_64) return Bytes_8 is
     [Byte_Of (L, 0), Byte_Of (L, 1), Byte_Of (L, 2), Byte_Of (L, 3),
      Byte_Of (L, 4), Byte_Of (L, 5), Byte_Of (L, 6), Byte_Of (L, 7)]
   with Global => null, Post => Limb_Of_8 (Bytes_Of_Limb'Result) = L;

   function Limbs_Of_Bytes (B : Bytes_32) return Limb_Array is
     [Limb_Of_8 (B (0 .. 7)), Limb_Of_8 (B (8 .. 15)),
      Limb_Of_8 (B (16 .. 23)), Limb_Of_8 (B (24 .. 31))];

   function Bytes_Of_Limbs (L : Limb_Array) return Bytes_32 is
      R : Bytes_32 := [others => 0];
   begin
      R (0 .. 7)   := Bytes_Of_Limb (L (0));
      R (8 .. 15)  := Bytes_Of_Limb (L (1));
      R (16 .. 23) := Bytes_Of_Limb (L (2));
      R (24 .. 31) := Bytes_Of_Limb (L (3));
      return R;
   end Bytes_Of_Limbs;

   -------------------------------------------------------------------
   --  Into and out of the Montgomery form (ADR 0069)
   -------------------------------------------------------------------

   --  R2 = 2^512 mod p: Mont_Mul (L, R2) is L 2^256 mod p. K2 with
   --  R2 2^-256 = 2^256 + K2 p.
   R2_Limbs : constant Limb_Array :=
     [16#0000_0000_0000_0003#, 16#FFFF_FFFB_FFFF_FFFF#,
      16#FFFF_FFFF_FFFF_FFFE#, 16#0000_0004_FFFF_FFFD#];
   K2_Limbs : constant Limb_Array :=
     [16#FFFF_FFF7_0000_0000#, 16#FFFF_FFFD_0000_0005#,
      16#0000_000B_FFFF_FFFA#, 16#0000_0004_FFFF_FFF9#]
   with Ghost => Proof_Only;

   procedure Lemma_R2 with
     Ghost => Proof_Only, Global => null,
     Post => To_Int (R2_Limbs) < P and then R_Inv >= 0
       and then To_Int (R2_Limbs) * R_Inv = Two_256 + To_Int (K2_Limbs) * P;

   procedure Lemma_R2 is
      W : constant Big_Integer := Two_64;
   begin
      Lemma_Unfold;
      pragma Assert (W = 18446744073709551616);
      pragma Assert (Two_256 = W * W * W * W);
      pragma Assert (To_Int (R2_Limbs)
        = Conv (R2_Limbs (0)) + Conv (R2_Limbs (1)) * W
          + Conv (R2_Limbs (2)) * W * W + Conv (R2_Limbs (3)) * W * W * W);
      pragma Assert (To_Int (K2_Limbs)
        = Conv (K2_Limbs (0)) + Conv (K2_Limbs (1)) * W
          + Conv (K2_Limbs (2)) * W * W + Conv (K2_Limbs (3)) * W * W * W);
      pragma Assert (R_Inv
        = Conv (RI_Limbs (0)) + Conv (RI_Limbs (1)) * W
          + Conv (RI_Limbs (2)) * W * W + Conv (RI_Limbs (3)) * W * W * W);
      pragma Assert (P
        = Conv (P_Limbs (0)) + Conv (P_Limbs (1)) * W
          + Conv (P_Limbs (2)) * W * W + Conv (P_Limbs (3)) * W * W * W);
   end Lemma_R2;

   --  Mont_Mul by R2 is the Montgomery form: X R2 2^-256 = X 2^256
   --  mod p.
   procedure Lemma_To_Mont (X : Big_Integer) with
     Ghost => Proof_Only, Global => null,
     Pre  => X >= 0,
     Post => (X * To_Int (R2_Limbs) * R_Inv) mod P = (X * Two_256) mod P;

   procedure Lemma_To_Mont (X : Big_Integer) is
      R2 : constant Big_Integer := To_Int (R2_Limbs);
      K2 : constant Big_Integer := To_Int (K2_Limbs);
      V  : constant Big_Integer := X * R2 * R_Inv;
   begin
      Lemma_R2;
      Lemma_P1;
      Lemma_To_Int_Bounds (R2_Limbs);
      pragma Assert (V = X * (R2 * R_Inv));
      pragma Assert (V = X * Two_256 + X * K2 * P);
      pragma Assert (V >= 0);
      pragma Assert (V = (V / P) * P + V mod P);
      pragma Assert (V mod P = X * Two_256 + (X * K2 - V / P) * P);
      pragma Assert (V mod P >= 0 and then V mod P < P);
      Lemma_Mod_Multiple (X * Two_256, V mod P, X * K2 - V / P);
   end Lemma_To_Mont;

   function From_Canonical (L : Limb_Array) return Element is
      R : constant Limb_Array := Mont_Mul (L, R2_Limbs);
   begin
      Lemma_R2;
      Lemma_To_Int_Bounds (L);
      Lemma_To_Mont (To_Int (L));
      return (Limbs => R);
   end From_Canonical;

   function To_Canonical (E : Element) return Limb_Array is
      One_L : constant Limb_Array := [1, 0, 0, 0];
   begin
      Lemma_Unfold;
      pragma Assert (Proof_Only => To_Int (One_L)
        = Conv (One_L (0)) * Weight (0) + Conv (One_L (1)) * Weight (1)
          + Conv (One_L (2)) * Weight (2) + Conv (One_L (3)) * Weight (3));
      pragma Assert (Proof_Only => To_Int (One_L) = 1);
      return Mont_Mul (E.Limbs, One_L);
   end To_Canonical;

   procedure From_Bytes (B : Bytes_32; E : out Element; Ok : out Boolean)
   is
      L    : constant Limb_Array := Limbs_Of_Bytes (B);
      D    : constant Limbs_With_Carry := Sub_Limbs (L, P_Limbs);
      --  L when it is below p, otherwise zero (public data, but the
      --  selection is masked anyway); then into the Montgomery form.
      Mask : constant Unsigned_64 := 0 - D.Carry;
      S    : constant Limb_Array := Select_Limbs ([others => 0], L, Mask);
      R    : constant Limb_Array := Mont_Mul (S, R2_Limbs);
   begin
      Lemma_R2;
      Lemma_To_Int_Bounds (S);
      Lemma_To_Mont (To_Int (S));
      Ok := D.Carry = 1;
      E  := (Limbs => R);
      if Ok then
         Lemma_To_Int_Eq (S, L);
      else
         Lemma_Unfold;
         pragma Assert (Proof_Only => To_Int (S)
           = Conv (S (0)) * Weight (0) + Conv (S (1)) * Weight (1)
             + Conv (S (2)) * Weight (2) + Conv (S (3)) * Weight (3));
         pragma Assert (Proof_Only => To_Int (S) = 0);
         pragma Assert (Proof_Only => To_Int (E.Limbs) = 0);
         pragma Assert (Proof_Only => To_Int (Zero.Limbs)
           = Conv (Zero.Limbs (0)) * Weight (0)
             + Conv (Zero.Limbs (1)) * Weight (1)
             + Conv (Zero.Limbs (2)) * Weight (2)
             + Conv (Zero.Limbs (3)) * Weight (3));
         Lemma_Inj (E, Zero);
      end if;
   end From_Bytes;

   function Of_Natural (X : Natural) return Element is
      L : constant Limb_Array := [Unsigned_64 (X), 0, 0, 0];
   begin
      Lemma_Unfold;
      pragma Assert (Proof_Only => To_Int (L)
        = Conv (L (0)) * Weight (0) + Conv (L (1)) * Weight (1)
          + Conv (L (2)) * Weight (2) + Conv (L (3)) * Weight (3));
      pragma Assert (Proof_Only => Conv (L (0)) = To_Big_Integer (X));
      return From_Canonical (L);
   end Of_Natural;

   ----------------------------------------------------------------------
   --  The product is associative (ADR 0066), from the integer model:
   --  the factor 2^-256 comes twice on each side.
   ----------------------------------------------------------------------

   procedure Lemma_Mul_Assoc (A, B, C : Element) is
      X  : constant Big_Integer := To_Int (A.Limbs);
      Y  : constant Big_Integer := To_Int (B.Limbs);
      Z  : constant Big_Integer := To_Int (C.Limbs);
      M1 : constant Big_Integer := To_Int (Mul (A, B).Limbs);
      M2 : constant Big_Integer := To_Int (Mul (B, C).Limbs);
   begin
      Lemma_To_Int_Bounds (A.Limbs);
      Lemma_To_Int_Bounds (B.Limbs);
      Lemma_To_Int_Bounds (C.Limbs);
      Lemma_R2;
      pragma Assert (P > 0);
      pragma Assert (M1 = (X * Y * R_Inv) mod P);
      pragma Assert (M2 = (Y * Z * R_Inv) mod P);
      Lemma_Mod_Mul (X * Y * R_Inv, Z * R_Inv, P);
      Lemma_Mod_Mul (Y * Z * R_Inv, X * R_Inv, P);
      pragma Assert
        (To_Int (Mul (Mul (A, B), C).Limbs) = (M1 * Z * R_Inv) mod P);
      pragma Assert (M1 * Z * R_Inv = M1 * (Z * R_Inv));
      pragma Assert
        (To_Int (Mul (A, Mul (B, C)).Limbs) = (X * M2 * R_Inv) mod P);
      pragma Assert (X * M2 * R_Inv = M2 * (X * R_Inv));
      pragma Assert ((X * Y * R_Inv) * (Z * R_Inv)
                     = (Y * Z * R_Inv) * (X * R_Inv));
      Lemma_Inj (Mul (Mul (A, B), C), Mul (A, Mul (B, C)));
   end Lemma_Mul_Assoc;

end P256_Field;
