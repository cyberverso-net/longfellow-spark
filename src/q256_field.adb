pragma SPARK_Mode (On);

package body Q256_Field is

   --  Equal limbs, equal integers (body below).
   procedure Lemma_To_Int_Eq (A, B : Limb_Array) with
     Ghost => Proof_Only, Global => null,
     Pre  => (for all I in Limb_Index => A (I) = B (I)),
     Post => To_Int (A) = To_Int (B);

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
      Qu : constant Unsigned_128 := X / 2 ** 64;
      M : constant Unsigned_128 := X mod 2 ** 64;
   begin
      pragma Assert (Proof_Only => Qu = Shift_Right (X, 64));
      pragma Assert (Proof_Only => M = (X and 16#FFFF_FFFF_FFFF_FFFF#));
      pragma Assert (Proof_Only => X = Qu * 2 ** 64 + M);
      pragma Assert
        (Proof_Only =>
           Conv128 (X) = Conv128 (Qu) * Two_64 + Conv128 (M));
      pragma Assert (Proof_Only => Conv128 (Qu) = Conv (Hi (X)));
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

   --  The arithmetic on the limbs alone, so that the predicates of the
   --  elements stay out of its proof (ADR 0070).
   function Add_Mod (X, Y : Limb_Array) return Limb_Array with
     Global => null,
     Pre    => (Proof_Only => To_Int (X) < Q and then To_Int (Y) < Q),
     Post   => (Proof_Only => To_Int (Add_Mod'Result)
                              = (To_Int (X) + To_Int (Y)) mod Q
                              and then To_Int (Add_Mod'Result) < Q);

   --  The proof of Add_Mod, in a lemma on its limbs. Written in the body,
   --  its Big_Integer assertions left finalisation code in the compiled
   --  function, though the assertions themselves are not compiled.
   procedure Lemma_Add_Mod
     (X, Y : Limb_Array; S, D : Limbs_With_Carry; Ge : Unsigned_64;
      R : Limb_Array)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => To_Int (X) < Q and then To_Int (Y) < Q
       and then S = Add_Limbs (X, Y)
       and then D = Sub_Limbs (S.Limbs, Q_Limbs)
       and then Ge = (S.Carry or (1 - D.Carry))
       and then R = (if Ge = 0 then S.Limbs else D.Limbs),
     Post   => To_Int (R) = (To_Int (X) + To_Int (Y)) mod Q
       and then To_Int (R) < Q;

   procedure Lemma_Add_Mod
     (X, Y : Limb_Array; S, D : Limbs_With_Carry; Ge : Unsigned_64;
      R : Limb_Array)
   is
   begin
      Lemma_To_Int_Bounds (S.Limbs);
      Lemma_To_Int_Bounds (D.Limbs);
      Lemma_To_Int_Bounds (X);
      Lemma_To_Int_Bounds (Y);
      pragma Assert (Ge <= 1);
      --  The two primitives, restated: the sum with its carry, the
      --  difference with its borrow.
      pragma Assert
        (To_Int (S.Limbs) + Conv (S.Carry) * Two_256
         = To_Int (X) + To_Int (Y));
      pragma Assert
        (To_Int (D.Limbs)
         = To_Int (S.Limbs) - Q + Conv (D.Carry) * Two_256);
      --  Sum below 2 q: if it overflowed, the low part is below q.
      pragma Assert (if S.Carry = 1 then D.Carry = 1);
      --  Ge is 0 exactly when nothing overflowed and the sum is below q.
      pragma Assert (if Ge = 0 then S.Carry = 0 and then D.Carry = 1);
      pragma Assert (if Ge = 0 then R = S.Limbs);
      pragma Assert
        (if S.Carry = 0 then To_Int (S.Limbs) = To_Int (X) + To_Int (Y));
      pragma Assert
        (if Ge = 1 then
           To_Int (R) = To_Int (X) + To_Int (Y) - Q
         else
           To_Int (R) = To_Int (X) + To_Int (Y));
      pragma Assert (To_Int (R) >= 0 and then To_Int (R) < Q);
   end Lemma_Add_Mod;

   function Add_Mod (X, Y : Limb_Array) return Limb_Array is
      S  : constant Limbs_With_Carry := Add_Limbs (X, Y);
      D  : constant Limbs_With_Carry := Sub_Limbs (S.Limbs, Q_Limbs);
      --  The sum is at least q iff it overflowed 2^256 or the
      --  subtraction did not borrow.
      Ge   : constant Unsigned_64 := S.Carry or (1 - D.Carry);
      Mask : constant Unsigned_64 := 0 - Ge;
      R    : constant Limb_Array := Select_Limbs (S.Limbs, D.Limbs, Mask);
   begin
      Lemma_Add_Mod (X, Y, S, D, Ge, R);
      return R;
   end Add_Mod;

   function Sub_Mod (X, Y : Limb_Array) return Limb_Array with
     Global => null,
     Pre    => (Proof_Only => To_Int (X) < Q and then To_Int (Y) < Q),
     Post   => (Proof_Only => To_Int (Sub_Mod'Result)
                              = (To_Int (X) - To_Int (Y)) mod Q
                              and then To_Int (Sub_Mod'Result) < Q);

   --  The proof of Sub_Mod, in a lemma on its limbs, as for Add_Mod.
   procedure Lemma_Sub_Mod
     (X, Y : Limb_Array; D, F : Limbs_With_Carry; R : Limb_Array)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => To_Int (X) < Q and then To_Int (Y) < Q
       and then D = Sub_Limbs (X, Y)
       and then F = Add_Limbs (D.Limbs, Q_Limbs)
       and then R = (if D.Carry = 0 then D.Limbs else F.Limbs),
     Post   => To_Int (R) = (To_Int (X) - To_Int (Y)) mod Q
       and then To_Int (R) < Q;

   procedure Lemma_Sub_Mod
     (X, Y : Limb_Array; D, F : Limbs_With_Carry; R : Limb_Array)
   is
   begin
      Lemma_To_Int_Bounds (D.Limbs);
      Lemma_To_Int_Bounds (F.Limbs);
      Lemma_To_Int_Bounds (X);
      Lemma_To_Int_Bounds (Y);
      --  If the difference borrowed, adding q back overflows 2^256
      --  exactly once and yields X - Y + q. The two primitives,
      --  restated, then the overflow: the low part of F is below 2^256
      --  while X - Y + q is positive.
      pragma Assert
        (To_Int (D.Limbs)
         = To_Int (X) - To_Int (Y) + Conv (D.Carry) * Two_256);
      pragma Assert
        (To_Int (F.Limbs) + Conv (F.Carry) * Two_256
         = To_Int (D.Limbs) + Q);
      pragma Assert (To_Int (X) - To_Int (Y) + Q > 0);
      pragma Assert
        (if D.Carry = 1 then To_Int (D.Limbs) + Q > Two_256);
      pragma Assert (To_Int (F.Limbs) < Two_256);
      pragma Assert (if D.Carry = 1 then F.Carry /= 0);
      pragma Assert (if D.Carry = 1 then F.Carry = 1);
      pragma Assert
        (if D.Carry = 1 then
           To_Int (R) = To_Int (X) - To_Int (Y) + Q
         else
           To_Int (R) = To_Int (X) - To_Int (Y));
      pragma Assert (To_Int (R) >= 0 and then To_Int (R) < Q);
   end Lemma_Sub_Mod;

   function Sub_Mod (X, Y : Limb_Array) return Limb_Array is
      D    : constant Limbs_With_Carry := Sub_Limbs (X, Y);
      F    : constant Limbs_With_Carry := Add_Limbs (D.Limbs, Q_Limbs);
      Mask : constant Unsigned_64 := 0 - D.Carry;
      R    : constant Limb_Array := Select_Limbs (D.Limbs, F.Limbs, Mask);
   begin
      Lemma_Sub_Mod (X, Y, D, F, R);
      return R;
   end Sub_Mod;

   --  The element of canonical limbs R.
   function Of_Limbs (R : Limb_Array) return Element with
     Global => null,
     Pre    => (Proof_Only => To_Int (R) < Q),
     Post   => (Proof_Only => To_Int (Limbs (Of_Limbs'Result)) = To_Int (R));

   function Of_Limbs (R : Limb_Array) return Element is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Canonical_Limbs);
      A : constant Limb_Array := [R (0), R (1), R (2), R (3)]
      with Ghost => Proof_Only;
   begin
      Lemma_To_Int_Eq (A, R);
      pragma Assert (Proof_Only => Is_Canonical (A));
      declare
         E : constant Element :=
           (L0 => R (0), L1 => R (1), L2 => R (2), L3 => R (3));
      begin
         Lemma_To_Int_Eq (Limbs (E), R);
         return E;
      end;
   end Of_Limbs;

   --  The predicate of an element, as the bound of its integer.
   procedure Lemma_Canonical (A : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => To_Int (Limbs (A)) < Q
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Canonical_Limbs);
      L : constant Limb_Array := [A.L0, A.L1, A.L2, A.L3];
   begin
      pragma Assert (Is_Canonical (L));
      Lemma_To_Int_Eq (L, Limbs (A));
   end Lemma_Canonical;

   function Add (A, B : Element) return Element is
   begin
      Lemma_Canonical (A);
      Lemma_Canonical (B);
      return Of_Limbs (Add_Mod (Limbs (A), Limbs (B)));
   end Add;

   function Sub (A, B : Element) return Element is
   begin
      Lemma_Canonical (A);
      Lemma_Canonical (B);
      return Of_Limbs (Sub_Mod (Limbs (A), Limbs (B)));
   end Sub;

   -------------------------------------------------------------------
   --  Multiplication, stage 1: the 512-bit product (ADR 0013).
   -------------------------------------------------------------------

   --  Equal limbs denote equal values (stated element-wise, so that the
   --  proof does not rely on array extensionality).
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

   --  A value that differs from X by a multiple of q and lies in
   --  0 .. q - 1 is X mod q.
   procedure Lemma_Mod_Multiple (X, R, M : Big_Integer) with
     Ghost => Proof_Only, Global => null,
     Pre  => Q > 0 and then R = X + M * Q and then R >= 0 and then R < Q,
     Post => R = X mod Q;

   procedure Lemma_Mod_Multiple (X, R, M : Big_Integer) is
   begin
      pragma Assert (Proof_Only => X = R - M * Q);
      pragma Assert (Proof_Only => X mod Q = (R - M * Q) mod Q);
      pragma Assert (Proof_Only => (R - M * Q) mod Q = R mod Q);
      pragma Assert (Proof_Only => R mod Q = R);
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
      Qu : constant Big_Integer := X / M;
      Rm : constant Big_Integer := X mod M;
      Q2 : constant Big_Integer := (Rm * C) / M;
      R2 : constant Big_Integer := (Rm * C) mod M;
   begin
      pragma Assert (X = Qu * M + Rm);
      pragma Assert (Rm * C = Q2 * M + R2);
      pragma Assert (X = Rm + M * Qu);
      pragma Assert (Rm * C = R2 + M * Q2);
      pragma Assert (X * C = R2 + M * (Qu * C + Q2));
      Lemma_Mod_Unique (X * C, Qu * C + Q2, R2, M);
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
     Pre    => To_Int (Limbs (A)) = To_Int (Limbs (B)),
     Post   => A = B
   is
      W  : constant Big_Integer := Two_64;
      A0 : constant Big_Integer := Conv (Limbs (A) (0));
      A1 : constant Big_Integer := Conv (Limbs (A) (1));
      A2 : constant Big_Integer := Conv (Limbs (A) (2));
      A3 : constant Big_Integer := Conv (Limbs (A) (3));
      B0 : constant Big_Integer := Conv (Limbs (B) (0));
      B1 : constant Big_Integer := Conv (Limbs (B) (1));
      B2 : constant Big_Integer := Conv (Limbs (B) (2));
      B3 : constant Big_Integer := Conv (Limbs (B) (3));
   begin
      Lemma_Weights;
      Lemma_Horner (Limbs (A));
      Lemma_Horner (Limbs (B));
      for I in Limb_Index loop
         Lemma_Conv_Bounds (Limbs (A) (I));
         Lemma_Conv_Bounds (Limbs (B) (I));
      end loop;
      Lemma_Digit (A0, B0, A1 + W * (A2 + W * A3), B1 + W * (B2 + W * B3), W);
      Lemma_Digit (A1, B1, A2 + W * A3, B2 + W * B3, W);
      Lemma_Digit (A2, B2, A3, B3, W);
      for I in Limb_Index loop
         Lemma_Conv_Inj (Limbs (A) (I), Limbs (B) (I));
      end loop;
      pragma Assert (Limbs (A) = Limbs (B));
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
      pragma Assert (Proof_Only => Q
        = Conv (Q_Limbs (0)) + Conv (Q_Limbs (1)) * W
          + Conv (Q_Limbs (2)) * W * W + Conv (Q_Limbs (3)) * W * W * W);
   end Lemma_R_Inv;

   -------------------------------------------------------------------
   --  Montgomery multiplication (ADR 0069)
   -------------------------------------------------------------------

   subtype Six_Array is Word_Array (0 .. 5);

   --  The Montgomery constant q' = -q^-1 mod 2^64: q' q_0 = K_Q 2^64
   --  + 2^64 - 1, so that adding q' t_0 times q to a value with low
   --  word t_0 clears that word. Where p is one below a multiple of
   --  2^64 and P256_Field adds p times the low word itself, q is not.
   Q_Prime : constant Unsigned_64 := 16#CCD1_C8AA_EE00_BC4F#;
   K_Q     : constant Unsigned_64 := 16#C2FF_C74D_CCAF_771F#
   with Ghost => Proof_Only;

   --  The three upper limbs of q, one word down: q = q_0 + 2^64 Q_Hi.
   Q_Hi_Limbs : constant Limb_Array :=
     [16#BCE6_FAAD_A717_9E84#, 16#FFFF_FFFF_FFFF_FFFF#,
      16#FFFF_FFFF_0000_0000#, 0]
   with Ghost => Proof_Only;

   procedure Lemma_Q_Facts with
     Ghost => Proof_Only, Global => null,
     Post => Q > 0 and then Q < Two_256
       and then Q = Conv (Q_Limbs (0)) + Two_64 * To_Int (Q_Hi_Limbs)
       and then Conv (Q_Prime) * Conv (Q_Limbs (0))
                = Conv (K_Q) * Two_64 + Two_64 - 1;

   procedure Lemma_Q_Facts is
      W : constant Big_Integer := Two_64;
   begin
      Lemma_Unfold;
      pragma Assert (Proof_Only => W = 18446744073709551616);
      pragma Assert (Proof_Only => Q
        = Conv (Q_Limbs (0)) + Conv (Q_Limbs (1)) * W
          + Conv (Q_Limbs (2)) * W * W + Conv (Q_Limbs (3)) * W * W * W);
      pragma Assert (Proof_Only => To_Int (Q_Hi_Limbs)
        = Conv (Q_Hi_Limbs (0)) + Conv (Q_Hi_Limbs (1)) * W
          + Conv (Q_Hi_Limbs (2)) * W * W + Conv (Q_Hi_Limbs (3)) * W * W * W);
      pragma Assert (Proof_Only => Conv (Q_Prime) = 14758798090332847183);
      pragma Assert (Proof_Only => Conv (Q_Limbs (0)) = 17562291160714782033);
      pragma Assert (Proof_Only => Conv (K_Q) = 14051168499379697439);
   end Lemma_Q_Facts;

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

   --  A + X Y + C as a 128-bit value, which never wraps:
   --  (2^64 - 1) + (2^64 - 1)^2 + (2^64 - 1) = 2^128 - 1.
   procedure Lemma_Mac (A, X, Y, C : Unsigned_64) with
     Ghost => Proof_Only, Global => null,
     Post => Conv128 (Unsigned_128 (A) + Unsigned_128 (X) * Unsigned_128 (Y)
                      + Unsigned_128 (C))
             = Conv (A) + Conv (X) * Conv (Y) + Conv (C);

   procedure Lemma_Mac (A, X, Y, C : Unsigned_64) is
      Pr : constant Unsigned_128 := Unsigned_128 (X) * Unsigned_128 (Y);
      S1 : constant Unsigned_128 := Unsigned_128 (A) + Pr;
   begin
      Lemma_Mul_Split (X, Y);
      pragma Assert (S1 >= Unsigned_128 (A));
      Lemma_Add128 (Unsigned_128 (A), Pr);
      Lemma_Ext64 (A);
      pragma Assert (S1 + Unsigned_128 (C) >= S1);
      Lemma_Add128 (S1, Unsigned_128 (C));
      Lemma_Ext64 (C);
   end Lemma_Mac;

   --  One word of T + X B: the prefix identity extends from K to K + 1.
   procedure Lemma_Mac_Step
     (T : Limb_Array; X : Unsigned_64; B : Limb_Array; S : Limb_Array;
      K : Natural; C_In : Unsigned_64; W : Unsigned_128)
   with
     Ghost => Proof_Only, Global => null,
     Pre  => K <= 3
       and then Partial (S, K) + Conv (C_In) * Weight (K)
                = Partial (T, K) + Conv (X) * Partial (B, K)
       and then Conv128 (W) = Conv (T (K)) + Conv (X) * Conv (B (K))
                              + Conv (C_In)
       and then S (K) = Lo (W),
     Post => Partial (S, K + 1) + Conv (Hi (W)) * Weight (K + 1)
             = Partial (T, K + 1) + Conv (X) * Partial (B, K + 1);

   procedure Lemma_Mac_Step
     (T : Limb_Array; X : Unsigned_64; B : Limb_Array; S : Limb_Array;
      K : Natural; C_In : Unsigned_64; W : Unsigned_128)
   is
   begin
      pragma Unreferenced (C_In);
      pragma Assert (Conv (X) >= 0);
      Lemma_Split (W);
      pragma Assert (Conv (S (K)) = Conv128 (W) - Conv (Hi (W)) * Two_64);
      pragma Assert (Weight (K + 1) = Two_64 * Weight (K));
      pragma Assert
        (Partial (S, K + 1) = Partial (S, K) + Conv (S (K)) * Weight (K));
      pragma Assert
        (Partial (T, K + 1) = Partial (T, K) + Conv (T (K)) * Weight (K));
      pragma Assert
        (Partial (B, K + 1) = Partial (B, K) + Conv (B (K)) * Weight (K));
   end Lemma_Mac_Step;

   --  The value of two words.
   procedure Lemma_Two (L : Word_Array) with
     Ghost => Proof_Only, Global => null,
     Pre  => L'First = 0 and then L'Length = 2,
     Post => To_Int (L) = Conv (L (0)) + Conv (L (1)) * Two_64;

   procedure Lemma_Two (L : Word_Array) is
   begin
      Lemma_Unfold;
      pragma Assert (Partial (L, 0) = 0);
      pragma Assert (Partial (L, 1) = Conv (L (0)));
      pragma Assert (Partial (L, 2) = Conv (L (0)) + Conv (L (1)) * Two_64);
   end Lemma_Two;

   --  The last step of Mac_Row: the four low words, the carry added to
   --  the two words above, and the carry out of those, which the bound
   --  makes zero.
   procedure Lemma_Mac_Close
     (T : Six_Array; Tl : Limb_Array; X : Unsigned_64; B : Limb_Array;
      Lw : Limb_Array; C : Unsigned_64; Hi_In, Cw, Hi_Out : Word_Array;
      Cy : Unsigned_64; S : Six_Array)
   with
     Ghost => Proof_Only, Global => null,
     Pre  => Hi_In'First = 0 and then Hi_In'Length = 2
       and then Cw'First = 0 and then Cw'Length = 2
       and then Hi_Out'First = 0 and then Hi_Out'Length = 2
       and then (for all I in Limb_Index => Tl (I) = T (I))
       and then Hi_In (0) = T (4) and then Hi_In (1) = T (5)
       and then Cw (0) = C and then Cw (1) = 0
       and then (for all I in Limb_Index => S (I) = Lw (I))
       and then S (4) = Hi_Out (0) and then S (5) = Hi_Out (1)
       and then Partial (Lw, 4) + Conv (C) * Weight (4)
                = Partial (Tl, 4) + Conv (X) * Partial (B, 4)
       and then Cy <= 1
       and then To_Int (Hi_Out) + Conv (Cy) * Weight (2)
                = To_Int (Hi_In) + To_Int (Cw)
       and then To_Int (T) + Conv (X) * To_Int (B) < Weight (6),
     Post => To_Int (S) = To_Int (T) + Conv (X) * To_Int (B);

   procedure Lemma_Mac_Close
     (T : Six_Array; Tl : Limb_Array; X : Unsigned_64; B : Limb_Array;
      Lw : Limb_Array; C : Unsigned_64; Hi_In, Cw, Hi_Out : Word_Array;
      Cy : Unsigned_64; S : Six_Array)
   is
      W : constant Big_Integer := Two_64;
   begin
      Lemma_Unfold;
      Lemma_Six_Split (T, Tl);
      Lemma_Six_Split (S, Lw);
      Lemma_Two (Hi_In);
      Lemma_Two (Cw);
      Lemma_Two (Hi_Out);
      Lemma_To_Int_Bounds (S);
      Lemma_Conv_Bounds (Cy);
      pragma Assert (Conv (0) = 0);
      pragma Assert (To_Int (Cw) = Conv (C));
      pragma Assert (To_Int (B) = Partial (B, 4));
      pragma Assert (To_Int (Tl) = Partial (Tl, 4));
      pragma Assert (To_Int (Lw) = Partial (Lw, 4));
      pragma Assert
        (Conv (S (4)) + Conv (S (5)) * W
         = Conv (T (4)) + Conv (T (5)) * W + Conv (C) - Conv (Cy) * (W * W));
      pragma Assert
        (To_Int (S)
         = To_Int (Lw) + (Conv (S (4)) + Conv (S (5)) * W) * Weight (4));
      pragma Assert
        (To_Int (T)
         = To_Int (Tl) + (Conv (T (4)) + Conv (T (5)) * W) * Weight (4));
      --  In three steps: the weights, the two words above, the sum.
      pragma Assert ((W * W) * Weight (4) = Weight (6));
      declare
         Hs : constant Big_Integer := Conv (S (4)) + Conv (S (5)) * W;
         Ht : constant Big_Integer := Conv (T (4)) + Conv (T (5)) * W;
         Hr : constant Big_Integer := Ht + Conv (C) - Conv (Cy) * (W * W);
      begin
         pragma Assert (Hs = Hr);
         pragma Assert (Hs * Weight (4) = Hr * Weight (4));
         pragma Assert
           (Hr * Weight (4)
            = Ht * Weight (4) + Conv (C) * Weight (4)
              - Conv (Cy) * ((W * W) * Weight (4)));
         pragma Assert
           (Hs * Weight (4)
            = Ht * Weight (4) + Conv (C) * Weight (4)
              - Conv (Cy) * Weight (6));
      end;
      pragma Assert
        ((Conv (S (4)) + Conv (S (5)) * W) * Weight (4)
         = (Conv (T (4)) + Conv (T (5)) * W) * Weight (4)
           + Conv (C) * Weight (4) - Conv (Cy) * Weight (6));
      pragma Assert
        (To_Int (S)
         = (To_Int (Lw) + Conv (C) * Weight (4))
           + (Conv (T (4)) + Conv (T (5)) * W) * Weight (4)
           - Conv (Cy) * Weight (6));
      pragma Assert
        (To_Int (Lw) + Conv (C) * Weight (4)
         = To_Int (Tl) + Conv (X) * To_Int (B));
      pragma Assert
        (To_Int (S) = To_Int (T) + Conv (X) * To_Int (B)
                      - Conv (Cy) * Weight (6));
      pragma Assert (Conv (Cy) * Weight (6) < Weight (6));
      pragma Assert (Cy = 0);
   end Lemma_Mac_Close;

   --  S = T + X B on six words, as upstream's CIOS step (ADR 0077): four
   --  128-bit multiply-accumulates on the low words, in place, then the
   --  carry added to the two words above. The sum stays below 2^384.
   procedure Mac_Row
     (T : Six_Array; X : Unsigned_64; B : Limb_Array; S : out Six_Array)
   with
     Global => null,
     Inline,
     Pre    => (Proof_Only => To_Int (T) + Conv (X) * To_Int (B) < Weight (6)),
     Post   => (Proof_Only => To_Int (S) = To_Int (T) + Conv (X) * To_Int (B));

   procedure Mac_Row
     (T : Six_Array; X : Unsigned_64; B : Limb_Array; S : out Six_Array)
   is
      Tl : constant Limb_Array := [T (0), T (1), T (2), T (3)]
      with Ghost => Proof_Only;
      Lw : Limb_Array := [others => 0];
      C  : Unsigned_64 := 0;
      W  : Unsigned_128;
      Cy : Unsigned_64;
   begin
      for J in Limb_Index loop
         W := Unsigned_128 (T (J)) + Unsigned_128 (X) * Unsigned_128 (B (J))
              + Unsigned_128 (C);
         Lemma_Mac (T (J), X, B (J), C);
         Lw (J) := Lo (W);
         Lemma_Mac_Step (Tl, X, B, Lw, J, C, W);
         C := Hi (W);
         pragma Loop_Invariant
           (Proof_Only => Partial (Lw, J + 1) + Conv (C) * Weight (J + 1)
                          = Partial (Tl, J + 1)
                            + Conv (X) * Partial (B, J + 1));
      end loop;
      declare
         Hi_In  : constant Word_Array (0 .. 1) := [T (4), T (5)];
         Cw     : constant Word_Array (0 .. 1) := [C, 0];
         Hi_Out : Word_Array (0 .. 1);
      begin
         Add_Words (Hi_In, Cw, Hi_Out, Cy);
         S := [Lw (0), Lw (1), Lw (2), Lw (3), Hi_Out (0), Hi_Out (1)];
         Lemma_Mac_Close (T, Tl, X, B, Lw, C, Hi_In, Cw, Hi_Out, Cy, S);
      end;
   end Mac_Row;

   --  One round: T + X B, then M q added with M = q' times the low word
   --  of the sum, which clears that word, then one word down. The value
   --  divided by 2^64 stays below 2 q.
   procedure Round
     (T : in out Six_Array; X : Unsigned_64; B : Limb_Array;
      R : out Unsigned_64)
   with
     Global => null,
     Inline,
     Pre    => (Proof_Only => To_Int (B) < Q and then To_Int (T) < 2 * Q),
     Post   => (Proof_Only => To_Int (T) < 2 * Q
                and then To_Int (T) * Two_64
                         = To_Int (T'Old) + Conv (X) * To_Int (B)
                           + Conv (R) * Q);

   --  The low word of S + M q is zero when M = q' S_0 mod 2^64: with
   --  q' q_0 = K_Q W + W - 1 and M = q' S_0 - H W (H the high half of
   --  the product), S_0 + M q_0 = W (S_0 (K_Q + 1) - H q_0).
   --  On the words, not on Big_Integer actuals: the terms are formed
   --  here, in ghost code, not in Round (ADR 0076).
   procedure Lemma_Low_Word_Clears
     (S, S3 : Six_Array; M, H : Unsigned_64)
   with
     Ghost => Proof_Only, Global => null,
     Pre  => Conv (M) = Conv (S (0)) * Conv (Q_Prime) - Conv (H) * Two_64
       and then To_Int (S3) = To_Int (S) + Conv (M) * Q,
     Post => S3 (0) = 0
       and then To_Int (S3) = Two_64 * To_Int (Down (S3));

   procedure Lemma_Low_Word_Clears
     (S, S3 : Six_Array; M, H : Unsigned_64)
   is
      W   : constant Big_Integer := Two_64;
      Q0  : constant Big_Integer := Conv (Q_Limbs (0));
      QH  : constant Big_Integer := To_Int (Q_Hi_Limbs);
      Sd  : constant Big_Integer := To_Int (Down (S));
      Hi3 : constant Big_Integer := To_Int (Down (S3));
      --  S_0 + M q_0 as a multiple of W.
      Low : constant Big_Integer :=
        Conv (S (0)) * (Conv (K_Q) + 1) - Conv (H) * Q0;
   begin
      Lemma_Unfold;
      Lemma_Q_Facts;
      Lemma_Down (S);
      Lemma_Down (S3);
      Lemma_Conv_Bounds (S3 (0));
      pragma Assert (To_Int (S3) = Conv (S (0)) + W * Sd + Conv (M) * Q);
      pragma Assert (Conv (M) * Q = Conv (M) * Q0 + W * (Conv (M) * QH));
      pragma Assert (Conv (M) * Q0
        = Conv (S (0)) * (Conv (Q_Prime) * Q0) - Conv (H) * W * Q0);
      pragma Assert (Conv (Q_Prime) * Q0 = Conv (K_Q) * W + W - 1);
      pragma Assert (Conv (S (0)) + Conv (M) * Q0 = W * Low);
      pragma Assert (To_Int (S3) = W * (Low + Sd + Conv (M) * QH));
      Lemma_Digit (Conv (S3 (0)), To_Big_Integer (0), Hi3,
                   Low + Sd + Conv (M) * QH, W);
      pragma Assert (Conv (S3 (0)) = 0);
      pragma Assert (S3 (0) = 0);
   end Lemma_Low_Word_Clears;

   --  The bound of the round on the words (ADR 0076: the Big_Integer
   --  terms are formed here, not in Round).
   procedure Lemma_Round_Bound (T : Six_Array) with
     Ghost => Proof_Only, Global => null,
     Pre  => To_Int (T) * Two_64 < (2 * Q) * Two_64,
     Post => To_Int (T) < 2 * Q;

   procedure Lemma_Round_Bound (T : Six_Array) is
   begin
      Lemma_To_Int_Bounds (T);
      Lemma_Div_Bound (To_Int (T), Two_64, 2 * Q);
   end Lemma_Round_Bound;

   procedure Round
     (T : in out Six_Array; X : Unsigned_64; B : Limb_Array;
      R : out Unsigned_64)
   is
      S, S3 : Six_Array;
      T0 : constant Six_Array := T with Ghost => Proof_Only;
      Pm : Unsigned_128;
      M, H : Unsigned_64;
   begin
      Lemma_Unfold;
      Lemma_Q_Facts;
      Lemma_To_Int_Bounds (T);
      Lemma_To_Int_Bounds (B);
      Lemma_Conv_Bounds (X);
      pragma Assert (Proof_Only => Conv (X) * To_Int (B) <= (Two_64 - 1) * Q);
      pragma Assert
        (Proof_Only => To_Int (T) + Conv (X) * To_Int (B) < Weight (6));
      Mac_Row (T, X, B, S);
      Lemma_To_Int_Bounds (S);
      pragma Assert
        (Proof_Only => To_Int (S) = To_Int (T0) + Conv (X) * To_Int (B));
      --  M = q' S_0 mod 2^64, the low half of the product.
      Pm := Unsigned_128 (S (0)) * Unsigned_128 (Q_Prime);
      Lemma_Mul_Split (S (0), Q_Prime);
      Lemma_Split (Pm);
      M := Lo (Pm);
      H := Hi (Pm);
      pragma Assert
        (Proof_Only =>
           Conv (M) = Conv (S (0)) * Conv (Q_Prime) - Conv (H) * Two_64);
      Lemma_Conv_Bounds (M);
      pragma Assert (Proof_Only => To_Int (Q_Limbs) = Q);
      pragma Assert (Proof_Only => Conv (M) * Q <= (Two_64 - 1) * Q);
      pragma Assert
        (Proof_Only => To_Int (S) + Conv (M) * To_Int (Q_Limbs) < Weight (6));
      Mac_Row (S, M, Q_Limbs, S3);
      pragma Assert (Proof_Only => To_Int (S3) = To_Int (S) + Conv (M) * Q);
      Lemma_Low_Word_Clears (S, S3, M, H);
      T := Down (S3);
      R := M;
      pragma Assert (Proof_Only => To_Int (T) * Two_64 = To_Int (S3));
      --  Bound: T W = T0 + X B + M q < 2 q + (W - 1) q + (W - 1) q.
      pragma Assert (Proof_Only => To_Int (T) * Two_64 < (2 * Q) * Two_64);
      Lemma_Round_Bound (T);
   end Round;

   --  The last step of Mont_Mul: T 2^256 = A B + Qt q and Res = T - G q
   --  in 0 .. q - 1 give Res = A B 2^-256 mod q.
   procedure Lemma_Mont_Final
     (A, B : Limb_Array; Tv, Qt, G : Big_Integer; Res : Limb_Array)
   with
     Ghost => Proof_Only, Global => null,
     Pre  => Tv * Two_256 = To_Int (A) * To_Int (B) + Qt * Q
       and then To_Int (Res) = Tv - G * Q
       and then To_Int (Res) >= 0 and then To_Int (Res) < Q,
     Post => To_Int (Res) = (To_Int (A) * To_Int (B) * R_Inv) mod Q;

   procedure Lemma_Mont_Final
     (A, B : Limb_Array; Tv, Qt, G : Big_Integer; Res : Limb_Array)
   is
      X : constant Big_Integer := To_Int (A) * To_Int (B);
      K : constant Big_Integer := To_Int (K_Limbs);
   begin
      Lemma_R_Inv;
      Lemma_Q_Facts;
      pragma Assert (Tv = Tv * (Two_256 * R_Inv) - Tv * K * Q);
      pragma Assert (Tv * (Two_256 * R_Inv) = (Tv * Two_256) * R_Inv);
      pragma Assert (Tv = X * R_Inv + (Qt * R_Inv - Tv * K) * Q);
      pragma Assert (To_Int (Res) = X * R_Inv + (Qt * R_Inv - Tv * K - G) * Q);
      Lemma_Mod_Multiple (X * R_Inv, To_Int (Res), Qt * R_Inv - Tv * K - G);
   end Lemma_Mont_Final;

   --  The Montgomery product of upstream (fp_generic.rs montgomery_mul,
   --  the generic reduction step): A B 2^-256 mod q, B below q.
   function Mont_Mul (A, B : Limb_Array) return Limb_Array with
     Global => null,
     Pre    => (Proof_Only => To_Int (B) < Q),
     Post   => (Proof_Only => To_Int (Mont_Mul'Result) < Q
                and then To_Int (Mont_Mul'Result)
                         = (To_Int (A) * To_Int (B) * R_Inv) mod Q);

   --  The last step of Mont_Mul, on its words: the Big_Integer terms
   --  that Lemma_Mont_Final takes are formed here, not in Mont_Mul,
   --  whose compiled code would keep their finalisation.
   procedure Lemma_Mont_Close
     (A, B : Limb_Array; T : Six_Array; Qt : Big_Integer; Ge : Unsigned_64;
      Res : Limb_Array)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => To_Int (T) * Two_256 = To_Int (A) * To_Int (B) + Qt * Q
       and then (if Ge = 1 then To_Int (Res) = To_Int (T) - Q
                 else To_Int (Res) = To_Int (T))
       and then To_Int (Res) >= 0 and then To_Int (Res) < Q,
     Post   => To_Int (Res) = (To_Int (A) * To_Int (B) * R_Inv) mod Q
       and then To_Int (Res) < Q;

   procedure Lemma_Mont_Close
     (A, B : Limb_Array; T : Six_Array; Qt : Big_Integer; Ge : Unsigned_64;
      Res : Limb_Array)
   is
   begin
      Lemma_Mont_Final
        (A, B, To_Int (T), Qt,
         (if Ge = 1 then To_Big_Integer (1) else To_Big_Integer (0)), Res);
   end Lemma_Mont_Close;

   --  T below 2 q, hence below 2^257: word 5 is zero and word 4 at
   --  most one (ADR 0076: on the words).
   procedure Lemma_Top_Words (T : Six_Array) with
     Ghost => Proof_Only, Global => null,
     Pre  => To_Int (T) < 2 * Q,
     Post => T (5) = 0 and then T (4) <= 1;

   procedure Lemma_Top_Words (T : Six_Array) is
      L : constant Limb_Array := [T (0), T (1), T (2), T (3)];
   begin
      Lemma_Unfold;
      Lemma_Q_Facts;
      Lemma_Six_Split (T, L);
      Lemma_To_Int_Bounds (L);
      Lemma_Conv_Bounds (T (4));
      Lemma_Conv_Bounds (T (5));
      pragma Assert (Weight (5) = Two_256 * Two_64);
      pragma Assert (2 * Q < 2 * Two_256);
      pragma Assert (Conv (T (5)) * Weight (5) <= To_Int (T));
      pragma Assert (Conv (T (5)) * Weight (5) < 1 * Weight (5));
      Lemma_Div_Bound (Conv (T (5)), Weight (5), To_Big_Integer (1));
      pragma Assert (T (5) = 0);
      pragma Assert (Conv (T (4)) * Two_256 <= To_Int (T));
      pragma Assert (Conv (T (4)) * Two_256 < 2 * Two_256);
      Lemma_Div_Bound (Conv (T (4)), Two_256, To_Big_Integer (2));
   end Lemma_Top_Words;

   function Mont_Mul (A, B : Limb_Array) return Limb_Array is
      T    : Six_Array := [others => 0];
      R    : Unsigned_64;
      Qt   : Big_Integer := To_Big_Integer (0) with Ghost => Proof_Only;
      L    : Limb_Array;
      D    : Limbs_With_Carry;
      Ge   : Unsigned_64;
      Mask : Unsigned_64;
      Res  : Limb_Array;
   begin
      Lemma_Unfold;
      Lemma_Q_Facts;
      pragma Assert (Proof_Only => To_Int (T) = 0);
      for I in Limb_Index loop
         --  Three invariants, not one conjunction: a conjunction of
         --  Big_Integer terms leaves finalisation code in the loop.
         pragma Loop_Invariant (Proof_Only => To_Int (T) < 2 * Q);
         pragma Loop_Invariant (Proof_Only => Qt >= 0);
         pragma Loop_Invariant
           (Proof_Only => To_Int (T) * Weight (I)
                          = Partial (A, I) * To_Int (B) + Qt * Q);
         Round (T, A (I), B, R);
         pragma Assert (Proof_Only =>
           Partial (A, I + 1) = Partial (A, I) + Conv (A (I)) * Weight (I));
         pragma Assert (Proof_Only => Weight (I + 1) = Two_64 * Weight (I));
         Lemma_Conv_Bounds (R);
         Qt := Qt + Conv (R) * Weight (I);
         pragma Assert (Proof_Only =>
           To_Int (T) * Weight (I + 1)
           = Partial (A, I + 1) * To_Int (B) + Qt * Q);
      end loop;
      pragma Assert (Proof_Only =>
        To_Int (T) * Two_256 = To_Int (A) * To_Int (B) + Qt * Q);
      --  T < 2 q < 2^257: word 5 is zero and word 4 at most one.
      L := [T (0), T (1), T (2), T (3)];
      Lemma_Six_Split (T, L);
      Lemma_To_Int_Bounds (L);
      Lemma_Top_Words (T);
      pragma Assert (Proof_Only => T (5) = 0 and then T (4) <= 1);
      D    := Sub_Limbs (L, Q_Limbs);
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
                           = To_Int (L) - Q + Two_256);
         else
            pragma Assert (Proof_Only => D.Carry = 0);
            pragma Assert (Proof_Only => To_Int (D.Limbs) = To_Int (L) - Q);
         end if;
         pragma Assert (Proof_Only => To_Int (Res) = To_Int (T) - Q);
      else
         pragma Assert (Proof_Only => Res = L);
         Lemma_To_Int_Eq (Res, L);
         pragma Assert (Proof_Only => T (4) = 0);
         pragma Assert (Proof_Only => To_Int (Res) = To_Int (T));
      end if;
      Lemma_Mont_Close (A, B, T, Qt, Ge, Res);
      return Res;
   end Mont_Mul;

   function Mul (A, B : Element) return Element is
   begin
      Lemma_Canonical (A);
      Lemma_Canonical (B);
      return Of_Limbs (Mont_Mul (Limbs (A), Limbs (B)));
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

   --  The 64 nibbles of q - 2, most significant first: the public
   --  exponent of the fixed window chain (checked by the vector
   --  generator, gen_q256_vectors.py).
   type Nibble is range 0 .. 15;
   type Nibble_Array is array (0 .. 63) of Nibble;
   Exponent : constant Nibble_Array :=
     [16#F#, 16#F#, 16#F#, 16#F#, 16#F#, 16#F#, 16#F#, 16#F#,
      0, 0, 0, 0, 0, 0, 0, 0,
      16#F#, 16#F#, 16#F#, 16#F#, 16#F#, 16#F#, 16#F#, 16#F#,
      16#F#, 16#F#, 16#F#, 16#F#, 16#F#, 16#F#, 16#F#, 16#F#,
      16#B#, 16#C#, 16#E#, 6, 16#F#, 16#A#, 16#A#, 16#D#,
      16#A#, 7, 1, 7, 9, 16#E#, 8, 4,
      16#F#, 3, 16#B#, 9, 16#C#, 16#A#, 16#C#, 2,
      16#F#, 16#C#, 6, 3, 2, 5, 4, 16#F#];

   type Power_Table is array (Nibble) of Element;

   function Inv (E : Element) return Element is
      --  T (K) = E^K; T (0) = One keeps the flow fixed on a zero nibble.
      --  The whole table starts as One, so that flow analysis sees it
      --  initialised before the loop reads T (K - 1).
      T : Power_Table := [others => One];
      R : Element;
   begin
      T (1) := E;
      for K in Nibble range 2 .. 15 loop
         T (K) := Mul (T (K - 1), E);
      end loop;
      R := T (Exponent (0));
      for I in 1 .. 63 loop
         R := Square_N (R, 4);
         R := Mul (R, T (Exponent (I)));
      end loop;
      return R;
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

   --  R2 = 2^512 mod q: Mont_Mul (L, R2) is L 2^256 mod q. K2 with
   --  R2 2^-256 = 2^256 + K2 q.
   R2_Limbs : constant Limb_Array :=
     [16#8324_4C95_BE79_EEA2#, 16#4699_799C_49BD_6FA6#,
      16#2845_B239_2B6B_EC59#, 16#66E1_2D94_F3D9_5620#];
   K2_Limbs : constant Limb_Array :=
     [16#CE77_C306_C4F2_3CF2#, 16#7C28_A324_CCA7_670F#,
      16#35A3_09B3_7D79_869D#, 16#26E8_311F_5FBD_C629#]
   with Ghost => Proof_Only;

   procedure Lemma_R2 with
     Ghost => Proof_Only, Global => null,
     Post => To_Int (R2_Limbs) < Q and then R_Inv >= 0
       and then To_Int (R2_Limbs) * R_Inv = Two_256 + To_Int (K2_Limbs) * Q;

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
      pragma Assert (Q
        = Conv (Q_Limbs (0)) + Conv (Q_Limbs (1)) * W
          + Conv (Q_Limbs (2)) * W * W + Conv (Q_Limbs (3)) * W * W * W);
   end Lemma_R2;

   --  Mont_Mul by R2 is the Montgomery form: X R2 2^-256 = X 2^256
   --  mod q.
   procedure Lemma_To_Mont (X : Big_Integer) with
     Ghost => Proof_Only, Global => null,
     Pre  => X >= 0,
     Post => (X * To_Int (R2_Limbs) * R_Inv) mod Q = (X * Two_256) mod Q;

   procedure Lemma_To_Mont (X : Big_Integer) is
      R2 : constant Big_Integer := To_Int (R2_Limbs);
      K2 : constant Big_Integer := To_Int (K2_Limbs);
      V  : constant Big_Integer := X * R2 * R_Inv;
   begin
      Lemma_R2;
      Lemma_Q_Facts;
      Lemma_To_Int_Bounds (R2_Limbs);
      pragma Assert (V = X * (R2 * R_Inv));
      pragma Assert (V = X * Two_256 + X * K2 * Q);
      pragma Assert (V >= 0);
      pragma Assert (V = (V / Q) * Q + V mod Q);
      pragma Assert (V mod Q = X * Two_256 + (X * K2 - V / Q) * Q);
      pragma Assert (V mod Q >= 0 and then V mod Q < Q);
      Lemma_Mod_Multiple (X * Two_256, V mod Q, X * K2 - V / Q);
   end Lemma_To_Mont;

   --  Lemma_To_Mont on the words of L (ADR 0076).
   procedure Lemma_To_Mont_Limbs (L : Limb_Array) with
     Ghost => Proof_Only, Global => null,
     Post => (To_Int (L) * To_Int (R2_Limbs) * R_Inv) mod Q
             = (To_Int (L) * Two_256) mod Q;

   procedure Lemma_To_Mont_Limbs (L : Limb_Array) is
   begin
      Lemma_To_Int_Bounds (L);
      Lemma_To_Mont (To_Int (L));
   end Lemma_To_Mont_Limbs;

   function From_Canonical (L : Limb_Array) return Element is
      R : constant Limb_Array := Mont_Mul (L, R2_Limbs);
   begin
      Lemma_R2;
      Lemma_To_Mont_Limbs (L);
      return Of_Limbs (R);
   end From_Canonical;

   function To_Canonical (E : Element) return Limb_Array is
      One_L : constant Limb_Array := [1, 0, 0, 0];
   begin
      Lemma_Unfold;
      pragma Assert (Proof_Only => To_Int (One_L)
        = Conv (One_L (0)) * Weight (0) + Conv (One_L (1)) * Weight (1)
          + Conv (One_L (2)) * Weight (2) + Conv (One_L (3)) * Weight (3));
      pragma Assert (Proof_Only => To_Int (One_L) = 1);
      return Mont_Mul (Limbs (E), One_L);
   end To_Canonical;

   procedure From_Bytes (B : Bytes_32; E : out Element; Ok : out Boolean)
   is
      L    : constant Limb_Array := Limbs_Of_Bytes (B);
      D    : constant Limbs_With_Carry := Sub_Limbs (L, Q_Limbs);
      --  L when it is below q, otherwise zero (public data, but the
      --  selection is masked anyway); then into the Montgomery form.
      Mask : constant Unsigned_64 := 0 - D.Carry;
      S    : constant Limb_Array := Select_Limbs ([others => 0], L, Mask);
      R    : constant Limb_Array := Mont_Mul (S, R2_Limbs);
   begin
      Lemma_R2;
      Lemma_To_Mont_Limbs (S);
      Ok := D.Carry = 1;
      E  := Of_Limbs (R);
      if Ok then
         Lemma_To_Int_Eq (S, L);
      else
         Lemma_Unfold;
         pragma Assert (Proof_Only => To_Int (S)
           = Conv (S (0)) * Weight (0) + Conv (S (1)) * Weight (1)
             + Conv (S (2)) * Weight (2) + Conv (S (3)) * Weight (3));
         pragma Assert (Proof_Only => To_Int (S) = 0);
         pragma Assert (Proof_Only => To_Int (Limbs (E)) = 0);
         pragma Assert (Proof_Only => To_Int (Limbs (Zero))
           = Conv (Limbs (Zero) (0)) * Weight (0)
             + Conv (Limbs (Zero) (1)) * Weight (1)
             + Conv (Limbs (Zero) (2)) * Weight (2)
             + Conv (Limbs (Zero) (3)) * Weight (3));
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
      X  : constant Big_Integer := To_Int (Limbs (A));
      Y  : constant Big_Integer := To_Int (Limbs (B));
      Z  : constant Big_Integer := To_Int (Limbs (C));
      M1 : constant Big_Integer := To_Int (Limbs (Mul (A, B)));
      M2 : constant Big_Integer := To_Int (Limbs (Mul (B, C)));
   begin
      Lemma_To_Int_Bounds (Limbs (A));
      Lemma_To_Int_Bounds (Limbs (B));
      Lemma_To_Int_Bounds (Limbs (C));
      Lemma_R2;
      pragma Assert (Q > 0);
      pragma Assert (M1 = (X * Y * R_Inv) mod Q);
      pragma Assert (M2 = (Y * Z * R_Inv) mod Q);
      Lemma_Mod_Mul (X * Y * R_Inv, Z * R_Inv, Q);
      Lemma_Mod_Mul (Y * Z * R_Inv, X * R_Inv, Q);
      pragma Assert
        (To_Int (Limbs (Mul (Mul (A, B), C))) = (M1 * Z * R_Inv) mod Q);
      pragma Assert (M1 * Z * R_Inv = M1 * (Z * R_Inv));
      pragma Assert
        (To_Int (Limbs (Mul (A, Mul (B, C)))) = (X * M2 * R_Inv) mod Q);
      pragma Assert (X * M2 * R_Inv = M2 * (X * R_Inv));
      pragma Assert ((X * Y * R_Inv) * (Z * R_Inv)
                     = (Y * Z * R_Inv) * (X * R_Inv));
      Lemma_Inj (Mul (Mul (A, B), C), Mul (A, Mul (B, C)));
   end Lemma_Mul_Assoc;

   ----------------------------------------------------------------------
   --  The other ring laws (ADR 0070). Every stored integer is below Q
   --  (the predicate), so a sum of two is below 2 Q and a difference
   --  above -Q: one correction by Q gives the remainder.
   ----------------------------------------------------------------------

   procedure Lemma_Mod_Small (V : Big_Integer) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Q > 0 and then V >= -Q and then V < 2 * Q,
     Post   => V mod Q = (if V < 0 then V + Q elsif V < Q then V else V - Q)
   is
   begin
      if V < 0 then
         Lemma_Mod_Multiple (V, V + Q, 1);
      elsif V < Q then
         Lemma_Mod_Multiple (V, V, 0);
      else
         Lemma_Mod_Multiple (V, V - Q, -1);
      end if;
   end Lemma_Mod_Small;

   --  A remainder may be taken early in a sum.
   procedure Lemma_Mod_Add (X, Y : Big_Integer) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Q > 0 and then X >= 0 and then Y >= 0,
     Post   => (X mod Q + Y mod Q) mod Q = (X + Y) mod Q
   is
      S : constant Big_Integer := X mod Q + Y mod Q;
   begin
      pragma Assert (X = X mod Q + Q * (X / Q));
      pragma Assert (Y = Y mod Q + Q * (Y / Q));
      pragma Assert (S = S mod Q + Q * (S / Q));
      pragma Assert
        (X + Y = S mod Q + Q * (S / Q + X / Q + Y / Q));
      Lemma_Mod_Unique (X + Y, S / Q + X / Q + Y / Q, S mod Q, Q);
   end Lemma_Mod_Add;

   procedure Lemma_Bounds (A : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => To_Int (Limbs (A)) >= 0 and then To_Int (Limbs (A)) < Q
               and then Q > 0
   is
   begin
      Lemma_Canonical (A);
      Lemma_To_Int_Bounds (Limbs (A));
      Lemma_Q_Facts;
   end Lemma_Bounds;

   procedure Lemma_Zero_One with
     Ghost  => Proof_Only,
     Global => null,
     Post   => To_Int (Limbs (Zero)) = 0
               and then To_Int (Limbs (One)) = Two_256 - Q
   is
      W : constant Big_Integer := Two_64;
   begin
      Lemma_Unfold;
      pragma Assert (W = 18446744073709551616);
      pragma Assert (Two_256 = W * W * W * W);
      pragma Assert (To_Int (Limbs (Zero))
        = Conv (Limbs (Zero) (0)) + Conv (Limbs (Zero) (1)) * W
          + Conv (Limbs (Zero) (2)) * W * W
          + Conv (Limbs (Zero) (3)) * W * W * W);
      pragma Assert (To_Int (Limbs (One))
        = Conv (Limbs (One) (0)) + Conv (Limbs (One) (1)) * W
          + Conv (Limbs (One) (2)) * W * W
          + Conv (Limbs (One) (3)) * W * W * W);
      pragma Assert (Q
        = Conv (Q_Limbs (0)) + Conv (Q_Limbs (1)) * W
          + Conv (Q_Limbs (2)) * W * W + Conv (Q_Limbs (3)) * W * W * W);
   end Lemma_Zero_One;

   procedure Lemma_Mul_Comm (A, B : Element) is
      X : constant Big_Integer := To_Int (Limbs (A));
      Y : constant Big_Integer := To_Int (Limbs (B));
   begin
      pragma Assert (X * Y * R_Inv = Y * X * R_Inv);
      Lemma_Inj (Mul (A, B), Mul (B, A));
   end Lemma_Mul_Comm;

   procedure Lemma_Mul_One (A : Element) is
      X : constant Big_Integer := To_Int (Limbs (A));
      K : constant Big_Integer := To_Int (K_Limbs);
      V : constant Big_Integer := X * To_Int (Limbs (One)) * R_Inv;
   begin
      Lemma_Bounds (A);
      Lemma_Zero_One;
      Lemma_R_Inv;
      Lemma_R2;
      pragma Assert (V = X * (Two_256 * R_Inv) - X * R_Inv * Q);
      pragma Assert (V = X + (X * K - X * R_Inv) * Q);
      pragma Assert (V >= 0);
      Lemma_Mod_Unique (V, X * K - X * R_Inv, X, Q);
      Lemma_Inj (Mul (A, One), A);
   end Lemma_Mul_One;

   --  The core of distributivity, on the stored integers: X times the
   --  reduced sum is the reduced sum of the two products.
   procedure Lemma_Distrib_Int (X, Y, Z : Big_Integer) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Q > 0 and then X >= 0 and then Y >= 0 and then Z >= 0
               and then R_Inv >= 0,
     Post   => (X * ((Y + Z) mod Q) * R_Inv) mod Q
               = ((X * Y * R_Inv) mod Q + (X * Z * R_Inv) mod Q) mod Q
   is
   begin
      Lemma_Mod_Mul (Y + Z, X * R_Inv, Q);
      pragma Assert (X * ((Y + Z) mod Q) * R_Inv
                     = ((Y + Z) mod Q) * (X * R_Inv));
      pragma Assert ((Y + Z) * (X * R_Inv) = X * Y * R_Inv + X * Z * R_Inv);
      pragma Assert (X * Y * R_Inv >= 0 and then X * Z * R_Inv >= 0);
      Lemma_Mod_Add (X * Y * R_Inv, X * Z * R_Inv);
   end Lemma_Distrib_Int;

   procedure Lemma_Mul_Distrib (A, B, C : Element) is
      X : constant Big_Integer := To_Int (Limbs (A));
      Y : constant Big_Integer := To_Int (Limbs (B));
      Z : constant Big_Integer := To_Int (Limbs (C));
   begin
      Lemma_Bounds (A);
      Lemma_Bounds (B);
      Lemma_Bounds (C);
      Lemma_R2;
      Lemma_Distrib_Int (X, Y, Z);
      Lemma_Inj (Mul (A, Add (B, C)), Add (Mul (A, B), Mul (A, C)));
   end Lemma_Mul_Distrib;

   procedure Lemma_Mul_Distrib_Sub (A, B, C : Element) is
      X  : constant Big_Integer := To_Int (Limbs (A));
      Y  : constant Big_Integer := To_Int (Limbs (B));
      Z  : constant Big_Integer := To_Int (Limbs (C));
      D  : constant Big_Integer := (Y - Z) mod Q;
      MD : constant Big_Integer := (X * D * R_Inv) mod Q;
      MZ : constant Big_Integer := (X * Z * R_Inv) mod Q;
   begin
      Lemma_Bounds (A);
      Lemma_Bounds (B);
      Lemma_Bounds (C);
      Lemma_R2;
      Lemma_Mod_Small (Y - Z);
      pragma Assert (D >= 0 and then D < Q);
      Lemma_Mod_Small (D + Z);
      pragma Assert ((D + Z) mod Q = Y);
      Lemma_Distrib_Int (X, D, Z);
      pragma Assert (To_Int (Limbs (Mul (A, B))) = (MD + MZ) mod Q);
      Lemma_Mod_Small (MD + MZ);
      Lemma_Mod_Small ((MD + MZ) mod Q - MZ);
      Lemma_Inj (Mul (A, Sub (B, C)), Sub (Mul (A, B), Mul (A, C)));
   end Lemma_Mul_Distrib_Sub;

   procedure Lemma_Add_Assoc (A, B, C : Element) is
      X : constant Big_Integer := To_Int (Limbs (A));
      Y : constant Big_Integer := To_Int (Limbs (B));
      Z : constant Big_Integer := To_Int (Limbs (C));
   begin
      Lemma_Bounds (A);
      Lemma_Bounds (B);
      Lemma_Bounds (C);
      Lemma_Mod_Small (X + Y);
      Lemma_Mod_Small (Y + Z);
      Lemma_Mod_Small ((X + Y) mod Q + Z);
      Lemma_Mod_Small (X + (Y + Z) mod Q);
      Lemma_Inj (Add (Add (A, B), C), Add (A, Add (B, C)));
   end Lemma_Add_Assoc;

   procedure Lemma_Add_Comm (A, B : Element) is
   begin
      pragma Assert (To_Int (Limbs (A)) + To_Int (Limbs (B))
                     = To_Int (Limbs (B)) + To_Int (Limbs (A)));
      Lemma_Inj (Add (A, B), Add (B, A));
   end Lemma_Add_Comm;

   procedure Lemma_Add_Zero (A : Element) is
   begin
      Lemma_Bounds (A);
      Lemma_Zero_One;
      Lemma_Mod_Small (To_Int (Limbs (A)));
      Lemma_Inj (Add (A, Zero), A);
   end Lemma_Add_Zero;

   procedure Lemma_Add_Neg (A : Element) is
      X : constant Big_Integer := To_Int (Limbs (A));
   begin
      Lemma_Bounds (A);
      Lemma_Zero_One;
      Lemma_Mod_Small (-X);
      Lemma_Mod_Small (X + (-X) mod Q);
      Lemma_Inj (Add (A, Neg (A)), Zero);
   end Lemma_Add_Neg;

   procedure Lemma_Sub_Def (A, B : Element) is
      X : constant Big_Integer := To_Int (Limbs (A));
      Y : constant Big_Integer := To_Int (Limbs (B));
   begin
      Lemma_Bounds (A);
      Lemma_Bounds (B);
      Lemma_Mod_Small (X - Y);
      Lemma_Mod_Small (-Y);
      Lemma_Mod_Small (X + (-Y) mod Q);
      Lemma_Inj (Sub (A, B), Add (A, Neg (B)));
   end Lemma_Sub_Def;

end Q256_Field;
