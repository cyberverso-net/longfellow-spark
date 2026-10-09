pragma SPARK_Mode (On);

package body P256_Field is

   -------------------------------------------------------------------
   --  Lemmas on the model
   -------------------------------------------------------------------

   procedure Lemma_Partial_Bounds (L : Word_Array; N : Natural) with
     Ghost, Global => null,
     Pre  => L'First = 0
       and then (N = 0 or else N - 1 <= L'Last)
       and then N <= Max_Words,
     Post => Partial (L, N) >= 0 and then Partial (L, N) < Weight (N),
     Subprogram_Variant => (Decreases => N);

   procedure Lemma_Partial_Bounds (L : Word_Array; N : Natural) is
   begin
      if N > 0 then
         Lemma_Partial_Bounds (L, N - 1);
         pragma Assert (Conv (L (N - 1)) <= Two_64 - 1);
         pragma Assert
           (Partial (L, N)
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
      pragma Assert (Q = Shift_Right (X, 64));
      pragma Assert (M = (X and 16#FFFF_FFFF_FFFF_FFFF#));
      pragma Assert (X = Q * 2 ** 64 + M);
      pragma Assert (Conv128 (X) = Conv128 (Q) * Two_64 + Conv128 (M));
      pragma Assert (Conv128 (Q) = Conv (Hi (X)));
      pragma Assert (Conv128 (M) = Conv (Lo (X)));
   end Lemma_Split;

   --  Explicit unfolding of the weights, so that the provers need not
   --  instantiate the recursive definitions themselves.
   procedure Lemma_Unfold with
     Ghost, Global => null,
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
        (Two_32 = To_Big_Integer (65536) * To_Big_Integer (65536));
      pragma Assert (Two_64 = Two_32 * Two_32);
      pragma Assert (Weight (1) = Two_64 * Weight (0));
      pragma Assert (Weight (2) = Two_64 * Weight (1));
      pragma Assert (Weight (3) = Two_64 * Weight (2));
      pragma Assert (Weight (4) = Two_64 * Weight (3));
      pragma Assert (Weight (5) = Two_64 * Weight (4));
      pragma Assert (Weight (6) = Two_64 * Weight (5));
      pragma Assert (Weight (7) = Two_64 * Weight (6));
      pragma Assert (Weight (8) = Two_64 * Weight (7));
   end Lemma_Unfold;

   --  Subtraction of 128-bit values that does not wrap.
   procedure Lemma_Sub128 (X, Y : Unsigned_128) with
     Ghost, Global => null,
     Pre  => X >= Y,
     Post => Conv128 (X - Y) = Conv128 (X) - Conv128 (Y);

   procedure Lemma_Sub128 (X, Y : Unsigned_128) is
      D : constant Unsigned_128 := X - Y;
   begin
      pragma Assert (D + Y = X);
      pragma Assert (D <= X);
      pragma Assert (Conv128 (D + Y) = Conv128 (D) + Conv128 (Y));
   end Lemma_Sub128;

   --  Zero-extension preserves the value.
   procedure Lemma_Ext64 (H : Unsigned_64) with
     Ghost, Global => null,
     Post => Conv128 (Unsigned_128 (H)) = Conv (H);

   procedure Lemma_Ext64 (H : Unsigned_64) is
      X : constant Unsigned_128 := Unsigned_128 (H);
   begin
      Lemma_Split (X);
      pragma Assert (Lo (X) = H);
      pragma Assert (Hi (X) = 0);
      pragma Assert (Conv (0) = 0);
   end Lemma_Ext64;

   --  Addition of 128-bit values that does not wrap.
   procedure Lemma_Add128 (X, Y : Unsigned_128) with
     Ghost, Global => null,
     Pre  => X + Y >= X,
     Post => Conv128 (X + Y) = Conv128 (X) + Conv128 (Y);

   procedure Lemma_Add128 (X, Y : Unsigned_128) is
      S : constant Unsigned_128 := X + Y;
   begin
      pragma Assert (S - X = Y);
      pragma Assert (S >= X);
      Lemma_Sub128 (S, X);
   end Lemma_Add128;

   --  The 128-bit product of two words neither wraps nor exceeds
   --  (2^64 - 1)^2.
   procedure Lemma_Mul_Split (X, Y : Unsigned_64) with
     Ghost, Global => null,
     Post => Unsigned_128 (X) * Unsigned_128 (Y)
               <= 16#FFFF_FFFF_FFFF_FFFE_0000_0000_0000_0001#
       and then Conv128 (Unsigned_128 (X) * Unsigned_128 (Y))
                = Conv (X) * Conv (Y)
       and then Conv (X) * Conv (Y) <= (Two_64 - 1) * (Two_64 - 1);

   procedure Lemma_Mul_Split (X, Y : Unsigned_64) is
   begin
      pragma Assert (Conv (X) <= Two_64 - 1 and then Conv (Y) <= Two_64 - 1);
      pragma Assert (Conv (X) * Conv (Y) <= (Two_64 - 1) * (Two_64 - 1));
   end Lemma_Mul_Split;

   --  Weights multiply: 2^(64 I) * 2^(64 J) = 2^(64 (I + J)).
   procedure Lemma_Weight_Add (I, J : Natural) with
     Ghost, Global => null,
     Pre  => I <= Max_Words and then J <= Max_Words - I,
     Post => Weight (I) * Weight (J) = Weight (I + J),
     Subprogram_Variant => (Decreases => J);

   procedure Lemma_Weight_Add (I, J : Natural) is
   begin
      if J > 0 then
         Lemma_Weight_Add (I, J - 1);
         pragma Assert (Weight (J) = Two_64 * Weight (J - 1));
         pragma Assert (Weight (I + J) = Two_64 * Weight (I + J - 1));
      end if;
   end Lemma_Weight_Add;

   --  One word of addition with carry, against the prefix sums.
   procedure Lemma_Add_Step
     (A, B, R : Word_Array; K : Natural; C_In : Unsigned_64;
      W : Unsigned_128)
   with
     Ghost, Global => null,
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
      pragma Assert (Conv128 (W) < Two_64 + Two_64);
      pragma Assert (Hi (W) <= 1);
      pragma Assert (Conv (R (K)) = Conv128 (W) - Conv (Hi (W)) * Two_64);
      pragma Assert (Weight (K + 1) = Two_64 * Weight (K));
      pragma Assert
        (Partial (R, K + 1) = Partial (R, K) + Conv (R (K)) * Weight (K));
      pragma Assert
        (Partial (A, K + 1) = Partial (A, K) + Conv (A (K)) * Weight (K));
      pragma Assert
        (Partial (B, K + 1) = Partial (B, K) + Conv (B (K)) * Weight (K));
   end Lemma_Add_Step;

   --  One word of subtraction with borrow, against the prefix sums.
   --  B_Out + Hi (W) = 1: the high half of A_k + 2^64 - B_k - B_In is 1
   --  exactly when no borrow is produced.
   procedure Lemma_Sub_Step
     (A, B, R : Word_Array; K : Natural; B_In, B_Out : Unsigned_64;
      W : Unsigned_128)
   with
     Ghost, Global => null,
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
        ((Hi (W) = 0 and then B_Out = 1)
         or else (Hi (W) = 1 and then B_Out = 0));
      pragma Assert (Conv (0) = 0 and then Conv (1) = 1);
      pragma Assert (Conv (B_Out) + Conv (Hi (W)) = 1);
      pragma Assert (Conv (R (K)) = Conv128 (W) - Conv (Hi (W)) * Two_64);
      pragma Assert (Weight (K + 1) = Two_64 * Weight (K));
      pragma Assert
        (Partial (R, K + 1) = Partial (R, K) + Conv (R (K)) * Weight (K));
      pragma Assert
        (Partial (A, K + 1) = Partial (A, K) + Conv (A (K)) * Weight (K));
      pragma Assert
        (Partial (B, K + 1) = Partial (B, K) + Conv (B (K)) * Weight (K));
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
         pragma Assert (Conv128 (W) = Conv (A (I)) + Conv (B (I)) + Conv (C));
         R (I) := Lo (W);
         Lemma_Add_Step (A, B, R, I, C, W);
         C := Hi (W);
         pragma Loop_Invariant (C <= 1);
         pragma Loop_Invariant
           (Partial (R, I + 1) + Conv (C) * Weight (I + 1)
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
      pragma Assert (Conv128 (2 ** 64) = Two_64);
      for I in 0 .. A'Length - 1 loop
         pragma Assert (Bw <= 1);
         declare
            U : constant Unsigned_128 := Unsigned_128 (A (I)) + 2 ** 64;
            V : constant Unsigned_128 :=
              Unsigned_128 (B (I)) + Unsigned_128 (Bw);
         begin
            pragma Assert (Conv128 (U) = Conv (A (I)) + Two_64);
            pragma Assert (Conv128 (V) = Conv (B (I)) + Conv (Bw));
            pragma Assert (U >= V);
            Lemma_Sub128 (U, V);
            W := U - V;
         end;
         pragma Assert
           (Conv128 (W) = Conv (A (I)) + Two_64 - Conv (B (I)) - Conv (Bw));
         pragma Assert (Hi (W) <= 1);
         R (I) := Lo (W);
         Nb := 1 - Hi (W);
         Lemma_Sub_Step (A, B, R, I, Bw, Nb, W);
         Bw := Nb;
         pragma Loop_Invariant (Bw <= 1);
         pragma Loop_Invariant
           (Partial (R, I + 1)
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
      pragma Assert (To_Int (A.Limbs) < P and then To_Int (B.Limbs) < P);
      Lemma_To_Int_Bounds (A.Limbs);
      Lemma_To_Int_Bounds (B.Limbs);
      pragma Assert (Ge <= 1);
      --  Sum below 2 p: if it overflowed, the low part is below p.
      pragma Assert (if S.Carry = 1 then D.Carry = 1);
      pragma Assert
        (if Ge = 1 then
           To_Int (R) = To_Int (A.Limbs) + To_Int (B.Limbs) - P
         else
           To_Int (R) = To_Int (A.Limbs) + To_Int (B.Limbs));
      pragma Assert (To_Int (R) >= 0 and then To_Int (R) < P);
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
      pragma Assert (To_Int (A.Limbs) < P and then To_Int (B.Limbs) < P);
      Lemma_To_Int_Bounds (A.Limbs);
      Lemma_To_Int_Bounds (B.Limbs);
      --  If the difference borrowed, adding p back overflows 2^256
      --  exactly once and yields A - B + p.
      pragma Assert (if D.Carry = 1 then F.Carry = 1);
      pragma Assert
        (if D.Carry = 1 then
           To_Int (R) = To_Int (A.Limbs) - To_Int (B.Limbs) + P
         else
           To_Int (R) = To_Int (A.Limbs) - To_Int (B.Limbs));
      pragma Assert (To_Int (R) >= 0 and then To_Int (R) < P);
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
     Post   => Wide_Mul'Result <= 16#FFFF_FFFF_FFFF_FFFE_0000_0000_0000_0001#
       and then Conv128 (Wide_Mul'Result) = Conv (X) * Conv (Y)
       and then Conv128 (Wide_Mul'Result) <= (Two_64 - 1) * (Two_64 - 1);

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
     Ghost, Global => null,
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
      pragma Assert (Conv (X) >= 0);
      Lemma_Split (W);
      pragma Assert (Conv (R (K)) = Conv128 (W) - Conv (Hi (W)) * Two_64);
      pragma Assert (Weight (K + 1) = Two_64 * Weight (K));
      pragma Assert
        (Partial (R, K + 1) = Partial (R, K) + Conv (R (K)) * Weight (K));
      pragma Assert
        (Partial (B, K + 1) = Partial (B, K) + Conv (B (K)) * Weight (K));
   end Lemma_Row_Step;

   --  One row of the schoolbook product: X times the four limbs of B,
   --  as five words.
   function Mul_Row (X : Unsigned_64; B : Limb_Array) return Five_Array
   with
     Global => null,
     Post   => To_Int (Mul_Row'Result) = Conv (X) * To_Int (B);

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
      pragma Assert (Conv (0) = 0);
      pragma Assert (Partial (R, 0) = 0 and then Partial (B, 0) = 0);
      pragma Assert (Conv128 (W0) = Conv (X) * Conv (B (0)) + Conv (0));
      Lemma_Row_Step (X, B, R, 0, 0, W0);
      pragma Assert (P1 + Unsigned_128 (Hi (W0)) >= P1);
      Lemma_Add128 (P1, Unsigned_128 (Hi (W0)));
      Lemma_Ext64 (Hi (W0));
      pragma Assert (Conv128 (W1) = Conv (X) * Conv (B (1)) + Conv (Hi (W0)));
      Lemma_Row_Step (X, B, R, 1, Hi (W0), W1);
      pragma Assert (P2 + Unsigned_128 (Hi (W1)) >= P2);
      Lemma_Add128 (P2, Unsigned_128 (Hi (W1)));
      Lemma_Ext64 (Hi (W1));
      pragma Assert (Conv128 (W2) = Conv (X) * Conv (B (2)) + Conv (Hi (W1)));
      Lemma_Row_Step (X, B, R, 2, Hi (W1), W2);
      pragma Assert (P3 + Unsigned_128 (Hi (W2)) >= P3);
      Lemma_Add128 (P3, Unsigned_128 (Hi (W2)));
      Lemma_Ext64 (Hi (W2));
      pragma Assert (Conv128 (W3) = Conv (X) * Conv (B (3)) + Conv (Hi (W2)));
      Lemma_Row_Step (X, B, R, 3, Hi (W2), W3);
      pragma Assert
        (Partial (R, 5) = Partial (R, 4) + Conv (R (4)) * Weight (4));
      return R;
   end Mul_Row;

   --  Five words placed at word offset Off within eight zero words
   --  denote the value shifted by 2^(64 Off); one lemma per offset.
   procedure Lemma_Shift_0 (X : Five_Array; R : Wide_Array) with
     Ghost, Global => null,
     Pre  => R (0) = X (0)
       and then R (1) = X (1)
       and then R (2) = X (2)
       and then R (3) = X (3)
       and then R (4) = X (4)
       and then R (5) = 0
       and then R (6) = 0
       and then R (7) = 0,
     Post => To_Int (R) = To_Int (X) * Weight (0);

   procedure Lemma_Shift_0 (X : Five_Array; R : Wide_Array) is
   begin
      Lemma_Unfold;
      pragma Assert
        (To_Int (X)
           = Conv (X (0)) * Weight (0) + Conv (X (1)) * Weight (1)
           + Conv (X (2)) * Weight (2) + Conv (X (3)) * Weight (3)
           + Conv (X (4)) * Weight (4));
      pragma Assert
        (To_Int (R)
           = Conv (R (0)) * Weight (0) + Conv (R (1)) * Weight (1)
           + Conv (R (2)) * Weight (2) + Conv (R (3)) * Weight (3)
           + Conv (R (4)) * Weight (4) + Conv (R (5)) * Weight (5)
           + Conv (R (6)) * Weight (6) + Conv (R (7)) * Weight (7));
      pragma Assert
        (To_Int (R)
          = Conv (X (0)) * Weight (0) + Conv (X (1)) * Weight (1)
          + Conv (X (2)) * Weight (2) + Conv (X (3)) * Weight (3)
          + Conv (X (4)) * Weight (4));
   end Lemma_Shift_0;

   procedure Lemma_Shift_1 (X : Five_Array; R : Wide_Array) with
     Ghost, Global => null,
     Pre  => R (0) = 0
       and then R (1) = X (0)
       and then R (2) = X (1)
       and then R (3) = X (2)
       and then R (4) = X (3)
       and then R (5) = X (4)
       and then R (6) = 0
       and then R (7) = 0,
     Post => To_Int (R) = To_Int (X) * Weight (1);

   procedure Lemma_Shift_1 (X : Five_Array; R : Wide_Array) is
   begin
      Lemma_Unfold;
      pragma Assert
        (To_Int (X)
           = Conv (X (0)) * Weight (0) + Conv (X (1)) * Weight (1)
           + Conv (X (2)) * Weight (2) + Conv (X (3)) * Weight (3)
           + Conv (X (4)) * Weight (4));
      pragma Assert
        (To_Int (R)
           = Conv (R (0)) * Weight (0) + Conv (R (1)) * Weight (1)
           + Conv (R (2)) * Weight (2) + Conv (R (3)) * Weight (3)
           + Conv (R (4)) * Weight (4) + Conv (R (5)) * Weight (5)
           + Conv (R (6)) * Weight (6) + Conv (R (7)) * Weight (7));
      pragma Assert
        (To_Int (R)
          = Conv (X (0)) * Weight (1) + Conv (X (1)) * Weight (2)
          + Conv (X (2)) * Weight (3) + Conv (X (3)) * Weight (4)
          + Conv (X (4)) * Weight (5));
   end Lemma_Shift_1;

   procedure Lemma_Shift_2 (X : Five_Array; R : Wide_Array) with
     Ghost, Global => null,
     Pre  => R (0) = 0
       and then R (1) = 0
       and then R (2) = X (0)
       and then R (3) = X (1)
       and then R (4) = X (2)
       and then R (5) = X (3)
       and then R (6) = X (4)
       and then R (7) = 0,
     Post => To_Int (R) = To_Int (X) * Weight (2);

   procedure Lemma_Shift_2 (X : Five_Array; R : Wide_Array) is
   begin
      Lemma_Unfold;
      pragma Assert
        (To_Int (X)
           = Conv (X (0)) * Weight (0) + Conv (X (1)) * Weight (1)
           + Conv (X (2)) * Weight (2) + Conv (X (3)) * Weight (3)
           + Conv (X (4)) * Weight (4));
      pragma Assert
        (To_Int (R)
           = Conv (R (0)) * Weight (0) + Conv (R (1)) * Weight (1)
           + Conv (R (2)) * Weight (2) + Conv (R (3)) * Weight (3)
           + Conv (R (4)) * Weight (4) + Conv (R (5)) * Weight (5)
           + Conv (R (6)) * Weight (6) + Conv (R (7)) * Weight (7));
      pragma Assert
        (To_Int (R)
          = Conv (X (0)) * Weight (2) + Conv (X (1)) * Weight (3)
          + Conv (X (2)) * Weight (4) + Conv (X (3)) * Weight (5)
          + Conv (X (4)) * Weight (6));
   end Lemma_Shift_2;

   procedure Lemma_Shift_3 (X : Five_Array; R : Wide_Array) with
     Ghost, Global => null,
     Pre  => R (0) = 0
       and then R (1) = 0
       and then R (2) = 0
       and then R (3) = X (0)
       and then R (4) = X (1)
       and then R (5) = X (2)
       and then R (6) = X (3)
       and then R (7) = X (4),
     Post => To_Int (R) = To_Int (X) * Weight (3);

   procedure Lemma_Shift_3 (X : Five_Array; R : Wide_Array) is
   begin
      Lemma_Unfold;
      pragma Assert
        (To_Int (X)
           = Conv (X (0)) * Weight (0) + Conv (X (1)) * Weight (1)
           + Conv (X (2)) * Weight (2) + Conv (X (3)) * Weight (3)
           + Conv (X (4)) * Weight (4));
      pragma Assert
        (To_Int (R)
           = Conv (R (0)) * Weight (0) + Conv (R (1)) * Weight (1)
           + Conv (R (2)) * Weight (2) + Conv (R (3)) * Weight (3)
           + Conv (R (4)) * Weight (4) + Conv (R (5)) * Weight (5)
           + Conv (R (6)) * Weight (6) + Conv (R (7)) * Weight (7));
      pragma Assert
        (To_Int (R)
          = Conv (X (0)) * Weight (3) + Conv (X (1)) * Weight (4)
          + Conv (X (2)) * Weight (5) + Conv (X (3)) * Weight (6)
          + Conv (X (4)) * Weight (7));
   end Lemma_Shift_3;

   --  The product of two 256-bit values is below 2^512.
   procedure Lemma_Product_Bound (A, B : Limb_Array) with
     Ghost, Global => null,
     Post => To_Int (A) * To_Int (B) >= 0
       and then To_Int (A) * To_Int (B) < Weight (8);

   procedure Lemma_Product_Bound (A, B : Limb_Array) is
   begin
      Lemma_Unfold;
      Lemma_To_Int_Bounds (A);
      Lemma_To_Int_Bounds (B);
      Lemma_Weight_Add (4, 4);
      pragma Assert (To_Int (A) <= Weight (4) - 1);
      pragma Assert (To_Int (B) <= Weight (4) - 1);
      pragma Assert
        (To_Int (A) * To_Int (B) <= (Weight (4) - 1) * (Weight (4) - 1));
      pragma Assert ((Weight (4) - 1) * (Weight (4) - 1) < Weight (8));
   end Lemma_Product_Bound;

   --  A * B as eight words, exact.
   function Product (A, B : Limb_Array) return Wide_Array with
     Global => null,
     Post   => To_Int (Product'Result) = To_Int (A) * To_Int (B);

   function Product (A, B : Limb_Array) return Wide_Array is
      M0 : constant Five_Array := Mul_Row (A (0), B);
      M1 : constant Five_Array := Mul_Row (A (1), B);
      M2 : constant Five_Array := Mul_Row (A (2), B);
      M3 : constant Five_Array := Mul_Row (A (3), B);
      R0 : constant Wide_Array :=
        [M0 (0), M0 (1), M0 (2), M0 (3), M0 (4), 0, 0, 0];
      R1 : constant Wide_Array :=
        [0, M1 (0), M1 (1), M1 (2), M1 (3), M1 (4), 0, 0];
      R2 : constant Wide_Array :=
        [0, 0, M2 (0), M2 (1), M2 (2), M2 (3), M2 (4), 0];
      R3 : constant Wide_Array :=
        [0, 0, 0, M3 (0), M3 (1), M3 (2), M3 (3), M3 (4)];
      S1, S2, S3 : Wide_Array;
      C1, C2, C3 : Unsigned_64;
   begin
      Lemma_Shift_0 (M0, R0);
      Lemma_Shift_1 (M1, R1);
      Lemma_Shift_2 (M2, R2);
      Lemma_Shift_3 (M3, R3);
      Add_Words (R0, R1, S1, C1);
      Add_Words (S1, R2, S2, C2);
      Add_Words (S2, R3, S3, C3);
      --  The product of two 256-bit values fits in 512 bits, so no
      --  carry leaves the top word.
      Lemma_Unfold;
      Lemma_To_Int_Bounds (A);
      Lemma_To_Int_Bounds (B);
      Lemma_To_Int_Bounds (R0);
      Lemma_To_Int_Bounds (R1);
      Lemma_To_Int_Bounds (R2);
      Lemma_To_Int_Bounds (R3);
      Lemma_To_Int_Bounds (S1);
      Lemma_To_Int_Bounds (S2);
      Lemma_To_Int_Bounds (S3);
      Lemma_Product_Bound (A, B);
      pragma Assert
        (To_Int (A)
           = Conv (A (0)) * Weight (0) + Conv (A (1)) * Weight (1)
           + Conv (A (2)) * Weight (2) + Conv (A (3)) * Weight (3));
      pragma Assert
        (To_Int (A) * To_Int (B)
           = Conv (A (0)) * To_Int (B) * Weight (0)
           + Conv (A (1)) * To_Int (B) * Weight (1)
           + Conv (A (2)) * To_Int (B) * Weight (2)
           + Conv (A (3)) * To_Int (B) * Weight (3));
      pragma Assert (To_Int (R0) = Conv (A (0)) * To_Int (B) * Weight (0));
      pragma Assert (To_Int (R1) = Conv (A (1)) * To_Int (B) * Weight (1));
      pragma Assert (To_Int (R2) = Conv (A (2)) * To_Int (B) * Weight (2));
      pragma Assert (To_Int (R3) = Conv (A (3)) * To_Int (B) * Weight (3));
      pragma Assert
        (To_Int (R0) + To_Int (R1) + To_Int (R2) + To_Int (R3)
           = To_Int (A) * To_Int (B));
      pragma Assert (To_Int (R0) + To_Int (R1) < Weight (8));
      pragma Assert (C1 = 0);
      pragma Assert (To_Int (S1) + To_Int (R2) < Weight (8));
      pragma Assert (C2 = 0);
      pragma Assert (To_Int (S2) + To_Int (R3) < Weight (8));
      pragma Assert (C3 = 0);
      return S3;
   end Product;

   -------------------------------------------------------------------
   --  Multiplication, stages 2 to 6: Solinas reduction (ADR 0013).
   --  The reduction identity is a polynomial identity in t = 2^32, so
   --  the proofs below speak in powers of t.
   -------------------------------------------------------------------

   --  t^K, t = 2^32, for K in 0 .. 16.
   function T32 (K : Natural) return Big_Integer is
     (if K = 0 then To_Big_Integer (1) else Two_32 * T32 (K - 1))
   with Ghost, Global => null,
        Pre => K <= 16,
        Subprogram_Variant => (Decreases => K);

   --  Explicit unfolding of t^K for K in 0 .. 16, and of the weights.
   procedure Lemma_Unfold_T32 with
     Ghost, Global => null,
     Post => T32 (0) = 1
       and then T32 (1)
                = Two_32
       and then T32 (2)
                = Two_32 * Two_32
       and then T32 (3)
                = Two_32 * Two_32 * Two_32
       and then T32 (4)
                = Two_32 * Two_32 * Two_32 * Two_32
       and then T32 (5)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32
       and then T32 (6)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
       and then T32 (7)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32
       and then T32 (8)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32
       and then T32 (9)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32
       and then T32 (10)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32
       and then T32 (11)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
       and then T32 (12)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
       and then T32 (13)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32
       and then T32 (14)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32
       and then T32 (15)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32
       and then T32 (16)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32
       and then Weight (0) = 1
       and then Weight (1)
                = Two_32 * Two_32
       and then Weight (2)
                = Two_32 * Two_32 * Two_32 * Two_32
       and then Weight (3)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
       and then Weight (4)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32
       and then Weight (5)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32
       and then Weight (6)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
       and then Weight (7)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32
       and then Weight (8)
                = Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32 * Two_32 * Two_32
                  * Two_32 * Two_32 * Two_32 * Two_32
       and then Two_256 = Weight (4)
       and then Two_64 = Two_32 * Two_32
       and then Two_32 > 5;

   procedure Lemma_Unfold_T32 is
   begin
      Lemma_Unfold;
      pragma Assert (T32 (1) = Two_32 * T32 (0));
      pragma Assert (T32 (2) = Two_32 * T32 (1));
      pragma Assert (T32 (3) = Two_32 * T32 (2));
      pragma Assert (T32 (4) = Two_32 * T32 (3));
      pragma Assert (T32 (5) = Two_32 * T32 (4));
      pragma Assert (T32 (6) = Two_32 * T32 (5));
      pragma Assert (T32 (7) = Two_32 * T32 (6));
      pragma Assert (T32 (8) = Two_32 * T32 (7));
      pragma Assert (T32 (9) = Two_32 * T32 (8));
      pragma Assert (T32 (10) = Two_32 * T32 (9));
      pragma Assert (T32 (11) = Two_32 * T32 (10));
      pragma Assert (T32 (12) = Two_32 * T32 (11));
      pragma Assert (T32 (13) = Two_32 * T32 (12));
      pragma Assert (T32 (14) = Two_32 * T32 (13));
      pragma Assert (T32 (15) = Two_32 * T32 (14));
      pragma Assert (T32 (16) = Two_32 * T32 (15));
      pragma Assert (Weight (1) = Two_64 * Weight (0));
      pragma Assert (Weight (1) = Two_32 * Two_32 * Weight (0));
      pragma Assert (Weight (2) = Two_64 * Weight (1));
      pragma Assert (Weight (2) = Two_32 * Two_32 * Weight (1));
      pragma Assert (Weight (3) = Two_64 * Weight (2));
      pragma Assert (Weight (3) = Two_32 * Two_32 * Weight (2));
      pragma Assert (Weight (4) = Two_64 * Weight (3));
      pragma Assert (Weight (4) = Two_32 * Two_32 * Weight (3));
      pragma Assert (Weight (5) = Two_64 * Weight (4));
      pragma Assert (Weight (5) = Two_32 * Two_32 * Weight (4));
      pragma Assert (Weight (6) = Two_64 * Weight (5));
      pragma Assert (Weight (6) = Two_32 * Two_32 * Weight (5));
      pragma Assert (Weight (7) = Two_64 * Weight (6));
      pragma Assert (Weight (7) = Two_32 * Two_32 * Weight (6));
      pragma Assert (Weight (8) = Two_64 * Weight (7));
      pragma Assert (Weight (8) = Two_32 * Two_32 * Weight (7));
   end Lemma_Unfold_T32;

   procedure Lemma_Weight_T32 (K : Natural) with
     Ghost, Global => null,
     Pre  => K <= Max_Words,
     Post => Weight (K) = T32 (2 * K),
     Subprogram_Variant => (Decreases => K);

   procedure Lemma_Weight_T32 (K : Natural) is
   begin
      pragma Assert (Two_64 = Two_32 * Two_32);
      if K > 0 then
         Lemma_Weight_T32 (K - 1);
         pragma Assert (T32 (2 * K) = Two_32 * T32 (2 * K - 1));
         pragma Assert (T32 (2 * K - 1) = Two_32 * T32 (2 * K - 2));
      end if;
   end Lemma_Weight_T32;

   --  p = t^8 - t^7 + t^6 + t^3 - 1.
   procedure Lemma_P_Poly with
     Ghost, Global => null,
     Post => P = T32 (8) - T32 (7) + T32 (6) + T32 (3) - 1
       and then Two_256 = T32 (8)
       and then P > 0;

   procedure Lemma_P_Poly is
   begin
      Lemma_Weight_T32 (0);
      Lemma_Weight_T32 (1);
      Lemma_Weight_T32 (2);
      Lemma_Weight_T32 (3);
      Lemma_Weight_T32 (4);
      pragma Assert (Conv (16#FFFF_FFFF_FFFF_FFFF#) = Two_64 - 1);
      pragma Assert (Conv (16#0000_0000_FFFF_FFFF#) = Two_32 - 1);
      pragma Assert
        (Conv (16#FFFF_FFFF_0000_0001#) = (Two_32 - 1) * Two_32 + 1);
      pragma Assert
        (P = (Two_64 - 1) + (Two_32 - 1) * Weight (1)
             + ((Two_32 - 1) * Two_32 + 1) * Weight (3));
   end Lemma_P_Poly;

   --  32-bit word J of the 512-bit product, J in 0 .. 15; slot 16 is
   --  the constant zero word used by the term table.
   subtype Slot is Natural range 0 .. 16;

   function Word (R : Wide_Array; J : Slot) return Unsigned_64 is
     (if J = 16 then 0
      elsif J mod 2 = 0 then R (J / 2) and 16#FFFF_FFFF#
      else Shift_Right (R (J / 2), 32))
   with Global => null,
        Post => Word'Result < 2 ** 32;
   --  The if-expression selects on the constant table index, never on
   --  data.

   function WVal (R : Wide_Array; J : Slot) return Big_Integer is
     (Conv (Word (R, J)))
   with Ghost, Global => null;

   procedure Lemma_WVal_Bounds (R : Wide_Array) with
     Ghost, Global => null,
     Post => (for all J in Slot => WVal (R, J) >= 0
       and then WVal (R, J) < Two_32)
       and then WVal (R, 16) = 0;

   procedure Lemma_WVal_Bounds (R : Wide_Array) is
   begin
      for J in Slot loop
         pragma Assert (Word (R, J) < 2 ** 32);
         pragma Assert (Conv (Word (R, J)) < Conv (2 ** 32));
         pragma Loop_Invariant
           (for all K in 0 .. J => WVal (R, K) >= 0
             and then WVal (R, K) < Two_32);
      end loop;
      pragma Assert (Conv (0) = 0);
   end Lemma_WVal_Bounds;

   --  A 64-bit word is its two 32-bit halves.
   procedure Lemma_Word_Split (R : Wide_Array; M : Natural) with
     Ghost, Global => null,
     Pre  => M <= 7,
     Post => Conv (R (M)) = WVal (R, 2 * M) + WVal (R, 2 * M + 1) * Two_32;

   procedure Lemma_Word_Split (R : Wide_Array; M : Natural) is
      X : constant Unsigned_64 := R (M);
   begin
      pragma Assert
        (X = (X and 16#FFFF_FFFF#) + Shift_Right (X, 32) * 2 ** 32);
      pragma Assert (Shift_Right (X, 32) = X / 2 ** 32);
      pragma Assert ((X and 16#FFFF_FFFF#) = X mod 2 ** 32);
      pragma Assert (Conv (2 ** 32) = Two_32);
      pragma Assert
        (Conv (X) = Conv (X mod 2 ** 32) + Conv (X / 2 ** 32) * Two_32);
   end Lemma_Word_Split;

   --  Value of the product in terms of its 32-bit words.
   function Word_Sum (R : Wide_Array) return Big_Integer is
     (WVal (R, 0) * T32 (0) + WVal (R, 1) * T32 (1)
      + WVal (R, 2) * T32 (2) + WVal (R, 3) * T32 (3)
      + WVal (R, 4) * T32 (4) + WVal (R, 5) * T32 (5)
      + WVal (R, 6) * T32 (6) + WVal (R, 7) * T32 (7)
      + WVal (R, 8) * T32 (8) + WVal (R, 9) * T32 (9)
      + WVal (R, 10) * T32 (10) + WVal (R, 11) * T32 (11)
      + WVal (R, 12) * T32 (12) + WVal (R, 13) * T32 (13)
      + WVal (R, 14) * T32 (14) + WVal (R, 15) * T32 (15))
   with Ghost, Global => null;

   procedure Lemma_Word_Sum (R : Wide_Array) with
     Ghost, Global => null,
     Post => To_Int (R) = Word_Sum (R);

   --  One 64-bit word of the product in 32-bit words.
   procedure Lemma_Word_Term (R : Wide_Array; K : Natural) with
     Ghost, Global => null,
     Pre  => K <= 7,
     Post => Conv (R (K)) * Weight (K)
             = WVal (R, 2 * K) * T32 (2 * K)
               + WVal (R, 2 * K + 1) * T32 (2 * K + 1);

   procedure Lemma_Word_Term (R : Wide_Array; K : Natural) is
   begin
      Lemma_Word_Split (R, K);
      Lemma_Weight_T32 (K);
      pragma Assert (T32 (2 * K + 1) = Two_32 * T32 (2 * K));
   end Lemma_Word_Term;

   procedure Lemma_Word_Sum (R : Wide_Array) is
   begin
      pragma Assert
        (To_Int (R)
           = Conv (R (0)) * Weight (0) + Conv (R (1)) * Weight (1)
           + Conv (R (2)) * Weight (2) + Conv (R (3)) * Weight (3)
           + Conv (R (4)) * Weight (4) + Conv (R (5)) * Weight (5)
           + Conv (R (6)) * Weight (6) + Conv (R (7)) * Weight (7));
      for K in 0 .. 7 loop
         Lemma_Word_Term (R, K);
         pragma Loop_Invariant
           (for all J in 0 .. K =>
              Conv (R (J)) * Weight (J)
              = WVal (R, 2 * J) * T32 (2 * J)
                + WVal (R, 2 * J + 1) * T32 (2 * J + 1));
      end loop;
   end Lemma_Word_Sum;

   --  A term of the reduction table: eight 32-bit word slots, least
   --  significant first (FIPS 186-4 D.2.3, see the chapter).
   type Slots is array (0 .. 7) of Slot;

   T_Slots  : constant Slots := [0, 1, 2, 3, 4, 5, 6, 7];
   S1_Slots : constant Slots := [16, 16, 16, 11, 12, 13, 14, 15];
   S2_Slots : constant Slots := [16, 16, 16, 12, 13, 14, 15, 16];
   S3_Slots : constant Slots := [8, 9, 10, 16, 16, 16, 14, 15];
   S4_Slots : constant Slots := [9, 10, 11, 13, 14, 15, 13, 8];
   D1_Slots : constant Slots := [11, 12, 13, 16, 16, 16, 8, 10];
   D2_Slots : constant Slots := [12, 13, 14, 15, 16, 16, 9, 11];
   D3_Slots : constant Slots := [13, 14, 15, 8, 9, 10, 16, 12];
   D4_Slots : constant Slots := [14, 15, 16, 9, 10, 11, 16, 13];

   function Term_Val (R : Wide_Array; S : Slots) return Big_Integer is
     (WVal (R, S (0)) * T32 (0) + WVal (R, S (1)) * T32 (1)
      + WVal (R, S (2)) * T32 (2) + WVal (R, S (3)) * T32 (3)
      + WVal (R, S (4)) * T32 (4) + WVal (R, S (5)) * T32 (5)
      + WVal (R, S (6)) * T32 (6) + WVal (R, S (7)) * T32 (7))
   with Ghost, Global => null;

   procedure Lemma_Term_Bound (R : Wide_Array; S : Slots) with
     Ghost, Global => null,
     Post => Term_Val (R, S) >= 0 and then Term_Val (R, S) < Two_256
       and then (if S (7) = 16 then Term_Val (R, S) < T32 (7));

   procedure Lemma_Term_Bound (R : Wide_Array; S : Slots) is
   begin
      Lemma_WVal_Bounds (R);
      Lemma_Unfold_T32;
      pragma Assert
        (T32 (1) = Two_32 * T32 (0) and then T32 (2) = Two_32 * T32 (1)
         and then T32 (3) = Two_32 * T32 (2)
         and then T32 (4) = Two_32 * T32 (3)
         and then T32 (5) = Two_32 * T32 (4)
         and then T32 (6) = Two_32 * T32 (5)
         and then T32 (7) = Two_32 * T32 (6)
         and then T32 (8) = Two_32 * T32 (7));
      pragma Assert
        (Term_Val (R, S)
           <= (Two_32 - 1) * T32 (0) + (Two_32 - 1) * T32 (1)
            + (Two_32 - 1) * T32 (2) + (Two_32 - 1) * T32 (3)
            + (Two_32 - 1) * T32 (4) + (Two_32 - 1) * T32 (5)
            + (Two_32 - 1) * T32 (6) + (Two_32 - 1) * T32 (7));
      pragma Assert
        ((Two_32 - 1) * T32 (0) + (Two_32 - 1) * T32 (1)
           + (Two_32 - 1) * T32 (2) + (Two_32 - 1) * T32 (3)
           + (Two_32 - 1) * T32 (4) + (Two_32 - 1) * T32 (5)
           + (Two_32 - 1) * T32 (6) + (Two_32 - 1) * T32 (7)
         = T32 (8) - 1);
      pragma Assert (Two_256 = T32 (8));
      if S (7) = 16 then
         pragma Assert (WVal (R, S (7)) = 0);
         pragma Assert
           (Term_Val (R, S)
              <= (Two_32 - 1) * T32 (0) + (Two_32 - 1) * T32 (1)
               + (Two_32 - 1) * T32 (2) + (Two_32 - 1) * T32 (3)
               + (Two_32 - 1) * T32 (4) + (Two_32 - 1) * T32 (5)
               + (Two_32 - 1) * T32 (6));
         pragma Assert
           ((Two_32 - 1) * T32 (0) + (Two_32 - 1) * T32 (1)
              + (Two_32 - 1) * T32 (2) + (Two_32 - 1) * T32 (3)
              + (Two_32 - 1) * T32 (4) + (Two_32 - 1) * T32 (5)
              + (Two_32 - 1) * T32 (6)
            = T32 (7) - 1);
      end if;
   end Lemma_Term_Bound;

   --  Executable term: limb I is slots 2 I and 2 I + 1.
   function Term (R : Wide_Array; S : Slots) return Limb_Array with
     Global => null,
     Post   => To_Int (Term'Result) = Term_Val (R, S);

   function Term (R : Wide_Array; S : Slots) return Limb_Array is
      L : constant Limb_Array :=
        [0 => Word (R, S (0)) or Shift_Left (Word (R, S (1)), 32),
         1 => Word (R, S (2)) or Shift_Left (Word (R, S (3)), 32),
         2 => Word (R, S (4)) or Shift_Left (Word (R, S (5)), 32),
         3 => Word (R, S (6)) or Shift_Left (Word (R, S (7)), 32)];
   begin
      for I in Limb_Index loop
         pragma Assert
           (L (I) = Word (R, S (2 * I)) + Word (R, S (2 * I + 1)) * 2 ** 32);
         pragma Assert (Conv (2 ** 32) = Two_32);
         pragma Assert
           (Conv (L (I))
              = WVal (R, S (2 * I)) + WVal (R, S (2 * I + 1)) * Two_32);
         Lemma_Weight_T32 (I);
         pragma Assert (T32 (2 * I + 1) = Two_32 * T32 (2 * I));
         pragma Loop_Invariant
           (for all K in 0 .. I =>
              Conv (L (K))
                = WVal (R, S (2 * K)) + WVal (R, S (2 * K + 1)) * Two_32);
         pragma Loop_Invariant (for all K in 0 .. I => Weight (K)
           = T32 (2 * K));
         pragma Loop_Invariant
           (for all K in 0 .. I => T32 (2 * K + 1) = Two_32 * T32 (2 * K));
      end loop;
      pragma Assert
        (To_Int (L)
           = Conv (L (0)) * Weight (0) + Conv (L (1)) * Weight (1)
           + Conv (L (2)) * Weight (2) + Conv (L (3)) * Weight (3));
      return L;
   end Term;

   --  The positive and negative sums of the table, the quotient, and
   --  the exact reduction identity X = (S - N) + Q p, a polynomial
   --  identity in t (checked numerically by the vector generator).
   function S_Val (R : Wide_Array) return Big_Integer is
     (Term_Val (R, T_Slots)
      + 2 * Term_Val (R, S1_Slots) + 2 * Term_Val (R, S2_Slots)
      + Term_Val (R, S3_Slots) + Term_Val (R, S4_Slots))
   with Ghost, Global => null;

   function N_Val (R : Wide_Array) return Big_Integer is
     (Term_Val (R, D1_Slots) + Term_Val (R, D2_Slots)
      + Term_Val (R, D3_Slots) + Term_Val (R, D4_Slots))
   with Ghost, Global => null;

   function Q_Val (R : Wide_Array) return Big_Integer is
     (WVal (R, 8) * T32 (0)
      + WVal (R, 9) * (T32 (1) + T32 (0))
      + WVal (R, 10) * (T32 (2) + T32 (1))
      + WVal (R, 11) * (T32 (3) + T32 (2) - T32 (0))
      + WVal (R, 12) * (T32 (4) + T32 (3) - T32 (1) - T32 (0))
      + WVal (R, 13) * (T32 (5) + T32 (4) - T32 (2) - T32 (1) - T32 (0))
      + WVal (R, 14)
        * (T32 (6) + T32 (5) - T32 (3) - T32 (2) - T32 (1) - T32 (0))
      + WVal (R, 15)
        * (T32 (7) + T32 (6) - T32 (4) - T32 (3) - T32 (2) - T32 (1)))
   with Ghost, Global => null;

   --  Representative of t^J modulo p read off the table (the column
   --  of word J), and the exact quotient, for J in 8 .. 15.
   function Rep (J : Natural) return Big_Integer is
     (case J is
        when 8  => T32 (7) - T32 (6) - T32 (3) + T32 (0),
        when 9  => -T32 (6) - T32 (4) - T32 (3) + T32 (1) + T32 (0),
        when 10 => -T32 (7) - T32 (5) - T32 (4) + T32 (2) + T32 (1),
        when 11 => -T32 (7) - T32 (5) + 2 * T32 (3) + T32 (2) - T32 (0),
        when 12 => -T32 (7) + 2 * T32 (4) + 2 * T32 (3) - T32 (1) - T32 (0),
        when 13 => -T32 (7) + T32 (6) + 2 * T32 (5) + 2 * T32 (4) + T32 (3)
                   - T32 (2) - T32 (1) - T32 (0),
        when 14 => 3 * T32 (6) + 2 * T32 (5) + T32 (4) - T32 (2) - T32 (1)
                   - T32 (0),
        when others => 3 * T32 (7) + 2 * T32 (6) + T32 (5) - T32 (3)
                       - T32 (2) - T32 (1))
   with Ghost, Global => null, Pre => J in 8 .. 15;

   function Quot (J : Natural) return Big_Integer is
     (case J is
        when 8  => T32 (0),
        when 9  => T32 (1) + T32 (0),
        when 10 => T32 (2) + T32 (1),
        when 11 => T32 (3) + T32 (2) - T32 (0),
        when 12 => T32 (4) + T32 (3) - T32 (1) - T32 (0),
        when 13 => T32 (5) + T32 (4) - T32 (2) - T32 (1) - T32 (0),
        when 14 => T32 (6) + T32 (5) - T32 (3) - T32 (2) - T32 (1) - T32 (0),
        when others => T32 (7) + T32 (6) - T32 (4) - T32 (3) - T32 (2)
                       - T32 (1))
   with Ghost, Global => null, Pre => J in 8 .. 15;

   --  t^J = Rep (J) + Quot (J) p: a polynomial identity in t.
   procedure Lemma_Power_Reduction (J : Natural) with
     Ghost, Global => null,
     Pre  => J in 8 .. 15
       and then P = T32 (8) - T32 (7) + T32 (6) + T32 (3) - 1,
     Post => T32 (J) = Rep (J) + Quot (J) * P;

   procedure Lemma_Power_Reduction (J : Natural) is
   begin
      Lemma_Unfold_T32;
      if J = 8 then
         pragma Assert (T32 (8) = Rep (8) + Quot (8) * P);
      elsif J = 9 then
         pragma Assert (T32 (9) = Rep (9) + Quot (9) * P);
      elsif J = 10 then
         pragma Assert (T32 (10) = Rep (10) + Quot (10) * P);
      elsif J = 11 then
         pragma Assert (T32 (11) = Rep (11) + Quot (11) * P);
      elsif J = 12 then
         pragma Assert (T32 (12) = Rep (12) + Quot (12) * P);
      elsif J = 13 then
         pragma Assert (T32 (13) = Rep (13) + Quot (13) * P);
      elsif J = 14 then
         pragma Assert (T32 (14) = Rep (14) + Quot (14) * P);
      else
         pragma Assert (T32 (15) = Rep (15) + Quot (15) * P);
      end if;
   end Lemma_Power_Reduction;

   --  Regrouping the table by word: S - N = low words + sum of
   --  WVal (J) Rep (J), and Q = sum of WVal (J) Quot (J).
   procedure Lemma_Regroup (R : Wide_Array) with
     Ghost, Global => null,
     Pre  => WVal (R, 16) = 0,
     Post => S_Val (R) - N_Val (R)
             = WVal (R, 0) * T32 (0) + WVal (R, 1) * T32 (1)
               + WVal (R, 2) * T32 (2) + WVal (R, 3) * T32 (3)
               + WVal (R, 4) * T32 (4) + WVal (R, 5) * T32 (5)
               + WVal (R, 6) * T32 (6) + WVal (R, 7) * T32 (7)
               + WVal (R, 8) * Rep (8) + WVal (R, 9) * Rep (9)
               + WVal (R, 10) * Rep (10) + WVal (R, 11) * Rep (11)
               + WVal (R, 12) * Rep (12) + WVal (R, 13) * Rep (13)
               + WVal (R, 14) * Rep (14) + WVal (R, 15) * Rep (15)
       and then Q_Val (R)
             = WVal (R, 8) * Quot (8) + WVal (R, 9) * Quot (9)
               + WVal (R, 10) * Quot (10) + WVal (R, 11) * Quot (11)
               + WVal (R, 12) * Quot (12) + WVal (R, 13) * Quot (13)
               + WVal (R, 14) * Quot (14) + WVal (R, 15) * Quot (15);

   procedure Lemma_Regroup (R : Wide_Array) is null;

   --  The exact identity, assembled from the word identities.
   procedure Lemma_Solinas_Identity (R : Wide_Array) with
     Ghost, Global => null,
     Pre  => To_Int (R) = Word_Sum (R)
       and then WVal (R, 16) = 0
       and then P = T32 (8) - T32 (7) + T32 (6) + T32 (3) - 1,
     Post => To_Int (R) = (S_Val (R) - N_Val (R)) + Q_Val (R) * P;

   procedure Lemma_Solinas_Identity (R : Wide_Array) is
   begin
      Lemma_Regroup (R);
      for J in 8 .. 15 loop
         Lemma_Power_Reduction (J);
         pragma Loop_Invariant
           (for all K in 8 .. J => T32 (K) = Rep (K) + Quot (K) * P);
      end loop;
      pragma Assert
        (for all K in 8 .. 15 =>
           WVal (R, K) * T32 (K)
           = WVal (R, K) * Rep (K) + WVal (R, K) * Quot (K) * P);
      pragma Assert
        (Word_Sum (R)
           = WVal (R, 0) * T32 (0) + WVal (R, 1) * T32 (1)
           + WVal (R, 2) * T32 (2) + WVal (R, 3) * T32 (3)
           + WVal (R, 4) * T32 (4) + WVal (R, 5) * T32 (5)
           + WVal (R, 6) * T32 (6) + WVal (R, 7) * T32 (7)
           + (WVal (R, 8) * Rep (8) + WVal (R, 8) * Quot (8) * P)
           + (WVal (R, 9) * Rep (9) + WVal (R, 9) * Quot (9) * P)
           + (WVal (R, 10) * Rep (10) + WVal (R, 10) * Quot (10) * P)
           + (WVal (R, 11) * Rep (11) + WVal (R, 11) * Quot (11) * P)
           + (WVal (R, 12) * Rep (12) + WVal (R, 12) * Quot (12) * P)
           + (WVal (R, 13) * Rep (13) + WVal (R, 13) * Quot (13) * P)
           + (WVal (R, 14) * Rep (14) + WVal (R, 14) * Quot (14) * P)
           + (WVal (R, 15) * Rep (15) + WVal (R, 15) * Quot (15) * P));
   end Lemma_Solinas_Identity;

   procedure Lemma_Solinas (R : Wide_Array) with
     Ghost, Global => null,
     Post => To_Int (R) = (S_Val (R) - N_Val (R)) + Q_Val (R) * P
       and then S_Val (R) >= 0
       and then S_Val (R) < 5 * Two_256 + 2 * T32 (7)
       and then N_Val (R) >= 0
       and then N_Val (R) <= 4 * (Two_256 - 1)
       and then N_Val (R) <= 5 * P
       and then S_Val (R) + 5 * P < 10 * Two_256;

   procedure Lemma_Solinas (R : Wide_Array) is
   begin
      Lemma_Word_Sum (R);
      Lemma_WVal_Bounds (R);
      Lemma_P_Poly;
      Lemma_Solinas_Identity (R);
      Lemma_Unfold_T32;
      Lemma_Term_Bound (R, T_Slots);
      Lemma_Term_Bound (R, S1_Slots);
      Lemma_Term_Bound (R, S2_Slots);
      Lemma_Term_Bound (R, S3_Slots);
      Lemma_Term_Bound (R, S4_Slots);
      Lemma_Term_Bound (R, D1_Slots);
      Lemma_Term_Bound (R, D2_Slots);
      Lemma_Term_Bound (R, D3_Slots);
      Lemma_Term_Bound (R, D4_Slots);
      pragma Assert (Term_Val (R, S2_Slots) < T32 (7));
      pragma Assert (S_Val (R) < 5 * Two_256 + 2 * T32 (7));
      --  5 p - 4 (2^256 - 1) > 0 and 5 p + 2 t^7 < 5 2^256.
      pragma Assert (5 * P >= 4 * (Two_256 - 1));
      pragma Assert (5 * P + 2 * T32 (7) < 5 * Two_256);
   end Lemma_Solinas;

   --  Five-word accumulation of a term.
   procedure Add_Term
     (Acc : in out Five_Array; R : Wide_Array; S : Slots)
   with
     Global => null,
     Pre  => To_Int (Acc) + Term_Val (R, S) < Weight (5),
     Post => To_Int (Acc) = To_Int (Acc'Old) + Term_Val (R, S);

   procedure Add_Term
     (Acc : in out Five_Array; R : Wide_Array; S : Slots)
   is
      T   : constant Limb_Array := Term (R, S);
      X   : constant Five_Array := [T (0), T (1), T (2), T (3), 0];
      Sum : Five_Array;
      C   : Unsigned_64;
   begin
      pragma Assert (Conv (0) = 0);
      pragma Assert (Partial (X, 4) = Partial (T, 4));
      pragma Assert (To_Int (X) = Partial (X, 4) + Conv (X (4)) * Weight (4));
      pragma Assert (To_Int (X) = To_Int (T));
      Add_Words (Acc, X, Sum, C);
      Lemma_To_Int_Bounds (Sum);
      pragma Assert (C = 0);
      Acc := Sum;
   end Add_Term;

   Five_P : constant Five_Array :=
     [16#FFFF_FFFF_FFFF_FFFB#, 16#0000_0004_FFFF_FFFF#, 0,
      16#FFFF_FFFB_0000_0005#, 16#0000_0000_0000_0004#];

   --  2^256 mod p = 2^224 - 2^192 - 2^96 + 1.
   C_Limbs : constant Limb_Array :=
     [16#0000_0000_0000_0001#, 16#FFFF_FFFF_0000_0000#,
      16#FFFF_FFFF_FFFF_FFFF#, 16#0000_0000_FFFF_FFFE#];

   procedure Lemma_Constants with
     Ghost, Global => null,
     Post => To_Int (Five_P) = 5 * P
       and then To_Int (C_Limbs) = Two_256 - P;

   procedure Lemma_Constants is
   begin
      Lemma_P_Poly;
      Lemma_Weight_T32 (1);
      Lemma_Weight_T32 (2);
      Lemma_Weight_T32 (3);
      Lemma_Weight_T32 (4);
      pragma Assert (Conv (16#FFFF_FFFF_FFFF_FFFB#) = Two_64 - 5);
      pragma Assert (Conv (16#0000_0004_FFFF_FFFF#) = 5 * Two_32 - 1);
      pragma Assert
        (Conv (16#FFFF_FFFB_0000_0005#) = (Two_32 - 5) * Two_32 + 5);
      pragma Assert (Conv (16#0000_0000_0000_0004#) = 4);
      pragma Assert
        (To_Int (Five_P)
           = (Two_64 - 5) + (5 * Two_32 - 1) * Weight (1)
             + ((Two_32 - 5) * Two_32 + 5) * Weight (3) + 4 * Weight (4));
      pragma Assert (Conv (16#0000_0000_0000_0001#) = 1);
      pragma Assert (Conv (16#FFFF_FFFF_0000_0000#) = (Two_32 - 1) * Two_32);
      pragma Assert (Conv (16#FFFF_FFFF_FFFF_FFFF#) = Two_64 - 1);
      pragma Assert (Conv (16#0000_0000_FFFF_FFFE#) = Two_32 - 2);
      pragma Assert
        (To_Int (C_Limbs)
           = 1 + (Two_32 - 1) * Two_32 * Weight (1)
             + (Two_64 - 1) * Weight (2) + (Two_32 - 2) * Weight (3));
   end Lemma_Constants;

   --  Equal limbs denote equal values (stated element-wise, so that the
   --  proof does not rely on array extensionality).
   procedure Lemma_To_Int_Eq (A, B : Limb_Array) with
     Ghost, Global => null,
     Pre  => (for all I in Limb_Index => A (I) = B (I)),
     Post => To_Int (A) = To_Int (B);

   procedure Lemma_To_Int_Eq (A, B : Limb_Array) is
   begin
      pragma Assert
        (A (0) = B (0) and then A (1) = B (1)
         and then A (2) = B (2) and then A (3) = B (3));
      pragma Assert
        (Partial (A, 4)
           = Conv (A (0)) * Weight (0) + Conv (A (1)) * Weight (1)
           + Conv (A (2)) * Weight (2) + Conv (A (3)) * Weight (3));
      pragma Assert
        (Partial (B, 4)
           = Conv (B (0)) * Weight (0) + Conv (B (1)) * Weight (1)
           + Conv (B (2)) * Weight (2) + Conv (B (3)) * Weight (3));
   end Lemma_To_Int_Eq;

   --  The low four words of a five-word value, and a four-word value
   --  extended by a zero word.
   function Low (V : Five_Array) return Limb_Array is
     [V (0), V (1), V (2), V (3)]
   with Global => null;

   function Ext (L : Limb_Array) return Five_Array is
     [L (0), L (1), L (2), L (3), 0]
   with Global => null;

   procedure Lemma_Low (V : Five_Array) with
     Ghost, Global => null,
     Post => To_Int (V) = To_Int (Low (V)) + Conv (V (4)) * Two_256
       and then To_Int (Low (V)) >= 0
       and then To_Int (Low (V)) < Two_256;

   procedure Lemma_Low (V : Five_Array) is
      L : constant Limb_Array := Low (V);
   begin
      Lemma_Unfold;
      Lemma_To_Int_Bounds (L);
      pragma Assert
        (L (0) = V (0) and then L (1) = V (1)
         and then L (2) = V (2) and then L (3) = V (3));
      pragma Assert
        (Partial (V, 4)
           = Conv (V (0)) * Weight (0) + Conv (V (1)) * Weight (1)
           + Conv (V (2)) * Weight (2) + Conv (V (3)) * Weight (3));
      pragma Assert
        (Partial (L, 4)
           = Conv (L (0)) * Weight (0) + Conv (L (1)) * Weight (1)
           + Conv (L (2)) * Weight (2) + Conv (L (3)) * Weight (3));
      pragma Assert (Partial (V, 5)
        = Partial (V, 4) + Conv (V (4)) * Weight (4));
   end Lemma_Low;

   procedure Lemma_Ext (L : Limb_Array) with
     Ghost, Global => null,
     Post => To_Int (Ext (L)) = To_Int (L);

   procedure Lemma_Ext (L : Limb_Array) is
      V : constant Five_Array := Ext (L);
   begin
      Lemma_Unfold;
      pragma Assert
        (V (0) = L (0) and then V (1) = L (1)
         and then V (2) = L (2) and then V (3) = L (3) and then V (4) = 0);
      pragma Assert
        (Partial (V, 4)
           = Conv (V (0)) * Weight (0) + Conv (V (1)) * Weight (1)
           + Conv (V (2)) * Weight (2) + Conv (V (3)) * Weight (3));
      pragma Assert
        (Partial (L, 4)
           = Conv (L (0)) * Weight (0) + Conv (L (1)) * Weight (1)
           + Conv (L (2)) * Weight (2) + Conv (L (3)) * Weight (3));
      pragma Assert (Partial (V, 5)
        = Partial (V, 4) + Conv (V (4)) * Weight (4));
   end Lemma_Ext;

   --  If A * B < K * B with B > 0 then A < K.
   procedure Lemma_Div_Bound (A, B, K : Big_Integer) with
     Ghost, Global => null,
     Pre  => B > 0 and then A >= 0 and then A * B < K * B,
     Post => A < K;

   procedure Lemma_Div_Bound (A, B, K : Big_Integer) is
   begin
      if A >= K then
         pragma Assert (A * B >= K * B);
         pragma Assert (False);
      end if;
   end Lemma_Div_Bound;

   --  A value that differs from X by a multiple of p and lies in
   --  0 .. p - 1 is X mod p.
   procedure Lemma_Mod_Multiple (X, R, M : Big_Integer) with
     Ghost, Global => null,
     Pre  => P > 0 and then R = X + M * P and then R >= 0 and then R < P,
     Post => R = X mod P;

   procedure Lemma_Mod_Multiple (X, R, M : Big_Integer) is
   begin
      pragma Assert (X = R - M * P);
      pragma Assert (X mod P = (R - M * P) mod P);
      pragma Assert ((R - M * P) mod P = R mod P);
      pragma Assert (R mod P = R);
   end Lemma_Mod_Multiple;

   --  Stage 3: the positive sum S = T + 2 S1 + 2 S2 + S3 + S4.
   function Sum_S (X : Wide_Array) return Five_Array with
     Global => null,
     Post   => To_Int (Sum_S'Result) = S_Val (X);

   function Sum_S (X : Wide_Array) return Five_Array is
      S : Five_Array := [others => 0];
   begin
      Lemma_Unfold;
      Lemma_Solinas (X);
      Lemma_Term_Bound (X, T_Slots);
      Lemma_Term_Bound (X, S1_Slots);
      Lemma_Term_Bound (X, S2_Slots);
      Lemma_Term_Bound (X, S3_Slots);
      Lemma_Term_Bound (X, S4_Slots);
      pragma Assert (To_Int (S) = 0);
      Add_Term (S, X, T_Slots);
      Add_Term (S, X, S1_Slots);
      Add_Term (S, X, S1_Slots);
      Add_Term (S, X, S2_Slots);
      Add_Term (S, X, S2_Slots);
      Add_Term (S, X, S3_Slots);
      Add_Term (S, X, S4_Slots);
      return S;
   end Sum_S;

   --  Stage 3: the negative sum N = D1 + D2 + D3 + D4.
   function Sum_N (X : Wide_Array) return Five_Array with
     Global => null,
     Post   => To_Int (Sum_N'Result) = N_Val (X);

   function Sum_N (X : Wide_Array) return Five_Array is
      N : Five_Array := [others => 0];
   begin
      Lemma_Unfold;
      Lemma_Term_Bound (X, D1_Slots);
      Lemma_Term_Bound (X, D2_Slots);
      Lemma_Term_Bound (X, D3_Slots);
      Lemma_Term_Bound (X, D4_Slots);
      pragma Assert (To_Int (N) = 0);
      Add_Term (N, X, D1_Slots);
      Add_Term (N, X, D2_Slots);
      Add_Term (N, X, D3_Slots);
      Add_Term (N, X, D4_Slots);
      return N;
   end Sum_N;

   --  Stage 4: V = S + 5 p - N, exact and below 10 2^256.
   function Stage_V (S, N : Five_Array) return Five_Array with
     Global => null,
     Pre    => To_Int (S) >= 0
       and then To_Int (S) + 5 * P < 10 * Two_256
       and then To_Int (N) >= 0
       and then To_Int (N) <= 5 * P,
     Post   => To_Int (Stage_V'Result) = To_Int (S) - To_Int (N) + 5 * P
       and then To_Int (Stage_V'Result) < 10 * Two_256;

   function Stage_V (S, N : Five_Array) return Five_Array is
      Tmp, V : Five_Array;
      C, Bw  : Unsigned_64;
   begin
      Lemma_Unfold;
      Lemma_Constants;
      Lemma_P_Poly;
      pragma Assert (10 * Two_256 < Weight (5));
      Add_Words (S, Five_P, Tmp, C);
      Lemma_To_Int_Bounds (Tmp);
      pragma Assert (C = 0);
      pragma Assert (To_Int (Tmp) = To_Int (S) + 5 * P);
      Sub_Words (Tmp, N, V, Bw);
      pragma Assert (Bw = 0);
      return V;
   end Stage_V;

   --  Stage 5: W = V_lo + V_hi (2^256 - p), which equals V - V_hi p and
   --  is below 2 p.
   function Stage_W (V : Five_Array) return Five_Array with
     Global => null,
     Pre    => To_Int (V) < 10 * Two_256,
     Post   => To_Int (Stage_W'Result) = To_Int (V) - Conv (V (4)) * P
       and then To_Int (Stage_W'Result) >= 0
       and then To_Int (Stage_W'Result) < 2 * P;

   function Stage_W (V : Five_Array) return Five_Array is
      V_Lo : constant Limb_Array := Low (V);
      Fold : Five_Array;
      W    : Five_Array;
      C    : Unsigned_64;
   begin
      Lemma_Unfold;
      Lemma_Constants;
      Lemma_P_Poly;
      Lemma_Low (V);
      pragma Assert (Conv (V (4)) * Two_256 < 10 * Two_256);
      Lemma_Div_Bound (Conv (V (4)), Two_256, 10);
      pragma Assert (Conv (V (4)) <= 9);
      Fold := Mul_Row (V (4), C_Limbs);
      pragma Assert (To_Int (Fold) = Conv (V (4)) * (Two_256 - P));
      pragma Assert (To_Int (Fold) <= 9 * (Two_256 - P));
      Lemma_Ext (V_Lo);
      Add_Words (Ext (V_Lo), Fold, W, C);
      Lemma_To_Int_Bounds (W);
      pragma Assert (Two_256 + 9 * (Two_256 - P) < Weight (5));
      pragma Assert (C = 0);
      pragma Assert (To_Int (W) = To_Int (V_Lo) + To_Int (Fold));
      pragma Assert (Two_256 + 9 * (Two_256 - P) < 2 * P);
      return W;
   end Stage_W;

   --  Stage 6: one conditional subtraction of p, in constant time.
   function Stage_Final (W : Five_Array) return Limb_Array with
     Global => null,
     Pre    => To_Int (W) >= 0 and then To_Int (W) < 2 * P,
     Post   => To_Int (Stage_Final'Result) >= 0
       and then To_Int (Stage_Final'Result) < P
       and then (if To_Int (W) < P then To_Int (Stage_Final'Result)
         = To_Int (W)
                 else To_Int (Stage_Final'Result) = To_Int (W) - P);

   function Stage_Final (W : Five_Array) return Limb_Array is
      Diff : Five_Array;
      Bw   : Unsigned_64;
      Mask : Unsigned_64;
   begin
      Lemma_Unfold;
      Lemma_P_Poly;
      Lemma_Ext (P_Limbs);
      Sub_Words (W, Ext (P_Limbs), Diff, Bw);
      pragma Assert (To_Int (Ext (P_Limbs)) = P);
      --  Bw = 1 iff W < p. Keep W then, else W - p; in both cases the
      --  value is below p, so the top word is zero.
      Mask := 0 - (1 - Bw);
      Lemma_Low (W);
      Lemma_Low (Diff);
      pragma Assert (if Bw = 0 then To_Int (Diff) = To_Int (W) - P);
      pragma Assert (if Bw = 0 then To_Int (Diff) < P else To_Int (W) < P);
      pragma Assert (P < Two_256);
      if Bw = 0 then
         pragma Assert (Conv (Diff (4)) * Two_256 < 1 * Two_256);
         Lemma_Div_Bound (Conv (Diff (4)), Two_256, 1);
         pragma Assert (Conv (Diff (4)) = 0);
         pragma Assert (To_Int (Diff) = To_Int (Low (Diff)));
      else
         pragma Assert (Conv (W (4)) * Two_256 < 1 * Two_256);
         Lemma_Div_Bound (Conv (W (4)), Two_256, 1);
         pragma Assert (Conv (W (4)) = 0);
         pragma Assert (To_Int (W) = To_Int (Low (W)));
      end if;
      declare
         R : constant Limb_Array := Select_Limbs (Low (W), Low (Diff), Mask);
      begin
         Lemma_To_Int_Bounds (R);
         if Bw = 0 then
            pragma Assert (Mask = Unsigned_64'Last);
            pragma Assert (R = Low (Diff));
            pragma Assert (for all I in Limb_Index => R (I) = Low (Diff) (I));
            Lemma_To_Int_Eq (R, Low (Diff));
            pragma Assert (To_Int (R) = To_Int (Diff));
            pragma Assert (To_Int (R) = To_Int (W) - P);
         else
            pragma Assert (Mask = 0);
            pragma Assert (R = Low (W));
            pragma Assert (for all I in Limb_Index => R (I) = Low (W) (I));
            Lemma_To_Int_Eq (R, Low (W));
            pragma Assert (To_Int (R) = To_Int (W));
         end if;
         pragma Assert (To_Int (R) >= 0 and then To_Int (R) < P);
         return R;
      end;
   end Stage_Final;

   --  Reduce an eight-word product to a canonical element.
   function Reduce (X : Wide_Array) return Limb_Array with
     Global => null,
     Post   => To_Int (Reduce'Result) = To_Int (X) mod P;

   function Reduce (X : Wide_Array) return Limb_Array is
      S, N, V, W : Five_Array;
      R : Limb_Array;
      M : Big_Integer with Ghost;
   begin
      Lemma_Solinas (X);
      Lemma_P_Poly;
      S := Sum_S (X);
      N := Sum_N (X);
      V := Stage_V (S, N);
      W := Stage_W (V);
      R := Stage_Final (W);
      --  V = X + (5 - Q) p, W = V - V_hi p, R = W or W - p.
      M := 5 - Q_Val (X) - Conv (V (4));
      pragma Assert (To_Int (W) = To_Int (X) + M * P);
      M := (if To_Int (W) < P then M else M - 1);
      pragma Assert (To_Int (R) = To_Int (X) + M * P);
      Lemma_Mod_Multiple (To_Int (X), To_Int (R), M);
      return R;
   end Reduce;

   function Mul (A, B : Element) return Element is
      X : constant Wide_Array := Product (A.Limbs, B.Limbs);
      R : constant Limb_Array := Reduce (X);
   begin
      return (Limbs => R);
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

   procedure From_Bytes (B : Bytes_32; E : out Element; Ok : out Boolean)
   is
      L    : constant Limb_Array := Limbs_Of_Bytes (B);
      D    : constant Limbs_With_Carry := Sub_Limbs (L, P_Limbs);
      --  Keep L when it is below p, otherwise zero (public data, but
      --  the selection is masked anyway).
      Mask : constant Unsigned_64 := 0 - D.Carry;
   begin
      Ok := D.Carry = 1;
      E  := (Limbs => Select_Limbs ([others => 0], L, Mask));
   end From_Bytes;

end P256_Field;
