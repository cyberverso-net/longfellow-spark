pragma SPARK_Mode (On);

with Clmul64;

package body GF2_128 is

   function Add (A, B : Element) return Element is
      R : Limb_Array := (others => 0);
   begin
      for I in Limb_Index loop
         R (I) := A.Limbs (I) xor B.Limbs (I);
         pragma Loop_Invariant
           (for all J in Limb_Index'First .. I =>
              R (J) = (A.Limbs (J) xor B.Limbs (J)));
      end loop;
      return (Limbs => R);
   end Add;

   function Sub (A, B : Element) return Element is
   begin
      return Add (A, B);
   end Sub;

   function Neg (A : Element) return Element is
   begin
      return A;
   end Neg;

   function Xtime (E : Element) return Element is
      --  Outgoing coefficient of x^127: 0 or 1.
      Carry : constant Unsigned_64 := Shift_Right (E.Limbs (1), 63);
      --  All-zeros or all-ones; constant-time selector.
      Mask  : constant Unsigned_64 := 0 - Carry;
   begin
      return
        (Limbs =>
           (0 => Shift_Left (E.Limbs (0), 1) xor (Mask and Reduction_Low),
            1 => Shift_Left (E.Limbs (1), 1)
                   or Shift_Right (E.Limbs (0), 63)));
   end Xtime;

   function Mul_Serial (A, B : Element) return Element is
      R : Element := Zero;
      M : Unsigned_64;
   begin
      for K in Bit_Count range 1 .. 128 loop
         R := Xtime (R);
         --  Constant-time conditional xor of A, selected by bit 128 - K
         --  of B: M is all-ones iff that bit is set.
         M := 0 - (Shift_Right (B.Limbs (Limb_Index ((128 - K) / 64)),
                                (128 - K) mod 64)
                     and 1);
         R.Limbs (0) := R.Limbs (0) xor (M and A.Limbs (0));
         R.Limbs (1) := R.Limbs (1) xor (M and A.Limbs (1));
         pragma Loop_Invariant (Proof_Only => R = Mul_Ref (A, B, K));
      end loop;
      return R;
   end Mul_Serial;

   -------------------------------------------------------------------
   --  The carry-less multiplication of upstream (Phase D, M2, ADR 0065):
   --  three 64 by 64 carry-less products (Karatsuba), then the two folds
   --  of gf2_128_reduce. The proof that it is Mul_Ref goes through the
   --  256-bit product: its reduction Red agrees with Xtime step by step,
   --  both sides are linear in B, and they agree on each single bit.
   -------------------------------------------------------------------

   subtype U64 is Unsigned_64;

   function Elem (L, H : U64) return Element is
     ((Limbs => [0 => L, 1 => H]))
   with Global => null;

   --  gf2_128_reduce: A + B x^64 modulo Q, the high limb of B folded
   --  once (x^128 = x^7 + x^2 + x + 1).
   function Reduce (A, B : Element) return Element is
     (Elem (A.Limbs (0) xor B.Limbs (1) xor Shift_Left (B.Limbs (1), 1)
              xor Shift_Left (B.Limbs (1), 2) xor Shift_Left (B.Limbs (1), 7),
            A.Limbs (1) xor B.Limbs (0) xor Shift_Right (B.Limbs (1), 63)
              xor Shift_Right (B.Limbs (1), 62)
              xor Shift_Right (B.Limbs (1), 57)))
   with Global => null;

   --  A 256-bit polynomial, four words from the lowest.
   type W4 is record
      W0, W1, W2, W3 : U64;
   end record
   with Ghost => Proof_Only;

   function X4 (A, B : W4) return W4 is
     ((A.W0 xor B.W0, A.W1 xor B.W1, A.W2 xor B.W2, A.W3 xor B.W3))
   with Ghost => Proof_Only, Global => null;

   --  The reduction of a 256-bit polynomial by the two folds.
   function Red (W : W4) return Element is
     (Reduce (Elem (W.W0, W.W1), Reduce (Elem (0, W.W2), Elem (0, W.W3))))
   with Ghost => Proof_Only, Global => null;

   function Shl1 (W : W4) return W4 is
     ((W0 => Shift_Left (W.W0, 1),
       W1 => Shift_Left (W.W1, 1) or Shift_Right (W.W0, 63),
       W2 => Shift_Left (W.W2, 1) or Shift_Right (W.W1, 63),
       W3 => Shift_Left (W.W3, 1) or Shift_Right (W.W2, 63)))
   with Ghost => Proof_Only, Global => null;

   procedure Lemma_Red_Lin (A, B : W4) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Red (X4 (A, B)) = Add (Red (A), Red (B))
   is
   begin
      null;
   end Lemma_Red_Lin;

   --  Multiplying by x before or after the reduction.
   procedure Lemma_Red_Shl1 (W : W4) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Shift_Right (W.W3, 63) = 0,
     Post   => Red (Shl1 (W)) = Xtime (Red (W))
   is
   begin
      null;
   end Lemma_Red_Shl1;

   --  The two folds of gf2_128_mul on the Karatsuba terms T0, T1 (the
   --  middle term, corrected) and T2 are the reduction of their sum.
   procedure Lemma_Upstream_Red (T0, T1, T2 : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Reduce (T0, Reduce (T1, T2))
               = Red ((W0 => T0.Limbs (0),
                       W1 => T0.Limbs (1) xor T1.Limbs (0),
                       W2 => T1.Limbs (1) xor T2.Limbs (0),
                       W3 => T2.Limbs (1)))
   is
   begin
      null;
   end Lemma_Upstream_Red;

   --  The 128-bit carry-less product of two limbs.
   function C (X, Y : U64) return Element is
     (Elem (Clmul64.Lo_Ref (X, Y, 64), Clmul64.Hi_Ref (X, Y, 64)))
   with Ghost => Proof_Only, Global => null;

   --  The 256-bit product of A by B, laid out as gf2_128_mul does.
   function Kara (A, B : Element) return W4 is
     (declare
        T0 : constant Element := C (A.Limbs (0), B.Limbs (0));
        T2 : constant Element := C (A.Limbs (1), B.Limbs (1));
        TM : constant Element :=
          C (A.Limbs (0) xor A.Limbs (1), B.Limbs (0) xor B.Limbs (1));
        T1 : constant Element :=
          Elem (TM.Limbs (0) xor T0.Limbs (0) xor T2.Limbs (0),
                TM.Limbs (1) xor T0.Limbs (1) xor T2.Limbs (1));
      begin
        (W0 => T0.Limbs (0),
         W1 => T0.Limbs (1) xor T1.Limbs (0),
         W2 => T1.Limbs (1) xor T2.Limbs (0),
         W3 => T2.Limbs (1)))
   with Ghost => Proof_Only, Global => null;

   procedure Lemma_C_Lin_X (X1, X2, Y : U64) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => C (X1 xor X2, Y) = Add (C (X1, Y), C (X2, Y))
   is
   begin
      Clmul64.Lemma_Lo_Lin_X (X1, X2, Y, 64);
      Clmul64.Lemma_Hi_Lin_X (X1, X2, Y, 64);
   end Lemma_C_Lin_X;

   procedure Lemma_C_Lin_Y (X, Y1, Y2 : U64) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => C (X, Y1 xor Y2) = Add (C (X, Y1), C (X, Y2))
   is
   begin
      Clmul64.Lemma_Lo_Lin_Y (X, Y1, Y2, 64);
      Clmul64.Lemma_Hi_Lin_Y (X, Y1, Y2, 64);
   end Lemma_C_Lin_Y;

   procedure Lemma_Kara_Lin (A, B1, B2 : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Kara (A, Add (B1, B2)) = X4 (Kara (A, B1), Kara (A, B2))
   is
   begin
      Lemma_C_Lin_Y (A.Limbs (0), B1.Limbs (0), B2.Limbs (0));
      Lemma_C_Lin_Y (A.Limbs (1), B1.Limbs (1), B2.Limbs (1));
      pragma Assert
        ((Add (B1, B2).Limbs (0) xor Add (B1, B2).Limbs (1))
         = ((B1.Limbs (0) xor B1.Limbs (1))
            xor (B2.Limbs (0) xor B2.Limbs (1))));
      Lemma_C_Lin_Y (A.Limbs (0) xor A.Limbs (1),
                     B1.Limbs (0) xor B1.Limbs (1),
                     B2.Limbs (0) xor B2.Limbs (1));
   end Lemma_Kara_Lin;

   procedure Lemma_Mul_Ref_Lin (A, B1, B2 : Element; N : Bit_Count) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (A, Add (B1, B2), N)
               = Add (Mul_Ref (A, B1, N), Mul_Ref (A, B2, N)),
     Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Mul_Ref_Lin (A, B1, B2, N - 1);
         pragma Assert
           (Xtime (Mul_Ref (A, Add (B1, B2), N - 1))
            = Xtime (Add (Mul_Ref (A, B1, N - 1), Mul_Ref (A, B2, N - 1))));
         pragma Assert
           (Xtime (Add (Mul_Ref (A, B1, N - 1), Mul_Ref (A, B2, N - 1)))
            = Add (Xtime (Mul_Ref (A, B1, N - 1)),
                   Xtime (Mul_Ref (A, B2, N - 1))));
         pragma Assert
           (Bit (Add (B1, B2), 128 - N)
            = (Bit (B1, 128 - N) /= Bit (B2, 128 - N)));
      end if;
   end Lemma_Mul_Ref_Lin;

   procedure Lemma_Mul_Ref_Zero (A : Element; N : Bit_Count) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (A, Zero, N) = Zero,
     Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Mul_Ref_Zero (A, N - 1);
      end if;
   end Lemma_Mul_Ref_Zero;

   --  The element whose only set bit is J.
   function E_Bit (J : Bit_Index_128) return Element is
     (if J < 64 then Elem (Shift_Left (1, J), 0)
      else Elem (0, Shift_Left (1, J - 64)))
   with Ghost => Proof_Only, Global => null;

   --  A times x^J.
   function Xpow (A : Element; J : Natural) return Element is
     (if J = 0 then A else Xtime (Xpow (A, J - 1)))
   with Ghost => Proof_Only,
        Global => null,
        Subprogram_Variant => (Decreases => J);

   procedure Lemma_Mul_Ref_Bit (A : Element; J : Bit_Index_128;
                                N : Bit_Count) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (A, E_Bit (J), N)
               = (if N < 128 - J then Zero else Xpow (A, N - (128 - J))),
     Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Mul_Ref_Bit (A, J, N - 1);
         pragma Assert (Bit (E_Bit (J), 128 - N) = (128 - N = J));
      end if;
   end Lemma_Mul_Ref_Bit;

   --  A shifted left by J as a 256-bit polynomial.
   function Shl_C (A : Element; J : Bit_Index_128) return W4 is
     (if J < 64
      then (W0 => Shift_Left (A.Limbs (0), J),
            W1 => Shift_Left (A.Limbs (1), J)
                  xor Shift_Right (A.Limbs (0), 64 - J),
            W2 => Shift_Right (A.Limbs (1), 64 - J),
            W3 => 0)
      else (W0 => 0,
            W1 => Shift_Left (A.Limbs (0), J - 64),
            W2 => Shift_Left (A.Limbs (1), J - 64)
                  xor Shift_Right (A.Limbs (0), 128 - J),
            W3 => Shift_Right (A.Limbs (1), 128 - J)))
   with Ghost => Proof_Only, Global => null;

   procedure Lemma_Shl_Step (A : Element; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => J < 127,
     Post   => Shl1 (Shl_C (A, J)) = Shl_C (A, J + 1)
               and then Shift_Right (Shl_C (A, J).W3, 63) = 0
   is
      S  : constant W4 := Shl_C (A, J);
      T  : constant W4 := Shl_C (A, J + 1);
      AL : constant U64 := A.Limbs (0);
      AH : constant U64 := A.Limbs (1);
   begin
      if J < 63 then
         pragma Assert (Shift_Left (S.W0, 1) = T.W0);
         pragma Assert
           ((Shift_Left (Shift_Right (AL, 64 - J), 1)
             or Shift_Right (Shift_Left (AL, J), 63))
            = Shift_Right (AL, 63 - J));
         pragma Assert ((Shift_Left (S.W1, 1) or Shift_Right (S.W0, 63))
                        = T.W1);
         pragma Assert
           ((Shift_Left (Shift_Right (AH, 64 - J), 1)
             or Shift_Right (Shift_Left (AH, J), 63))
            = Shift_Right (AH, 63 - J));
         pragma Assert ((Shift_Left (S.W2, 1) or Shift_Right (S.W1, 63))
                        = T.W2);
         pragma Assert ((Shift_Left (S.W3, 1) or Shift_Right (S.W2, 63))
                        = T.W3);
      elsif J = 63 then
         pragma Assert (Shl1 (S) = T);
      else
         pragma Assert (Shift_Left (S.W0, 1) = T.W0);
         pragma Assert ((Shift_Left (S.W1, 1) or Shift_Right (S.W0, 63))
                        = T.W1);
         pragma Assert
           ((Shift_Left (Shift_Right (AL, 128 - J), 1)
             or Shift_Right (Shift_Left (AL, J - 64), 63))
            = Shift_Right (AL, 127 - J));
         pragma Assert ((Shift_Left (S.W2, 1) or Shift_Right (S.W1, 63))
                        = T.W2);
         pragma Assert
           ((Shift_Left (Shift_Right (AH, 128 - J), 1)
             or Shift_Right (Shift_Left (AH, J - 64), 63))
            = Shift_Right (AH, 127 - J));
         pragma Assert ((Shift_Left (S.W3, 1) or Shift_Right (S.W2, 63))
                        = T.W3);
      end if;
   end Lemma_Shl_Step;

   procedure Lemma_Red_Shl (A : Element; J : Bit_Index_128) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Red (Shl_C (A, J)) = Xpow (A, J),
     Subprogram_Variant => (Decreases => J)
   is
   begin
      if J > 0 then
         Lemma_Red_Shl (A, J - 1);
         Lemma_Shl_Step (A, J - 1);
         Lemma_Red_Shl1 (Shl_C (A, J - 1));
      end if;
   end Lemma_Red_Shl;

   procedure Lemma_Kara_Bit (A : Element; J : Bit_Index_128) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Kara (A, E_Bit (J)) = Shl_C (A, J)
   is
      AL : constant U64 := A.Limbs (0);
      AH : constant U64 := A.Limbs (1);
   begin
      if J < 64 then
         Lemma_C_Lin_X (AL, AH, Shift_Left (1, J));
         Clmul64.Lemma_Lo_Bit (AL, J, 64);
         Clmul64.Lemma_Hi_Bit (AL, J, 64);
         Clmul64.Lemma_Lo_Bit (AH, J, 64);
         Clmul64.Lemma_Hi_Bit (AH, J, 64);
         Clmul64.Lemma_By_Zero (AH, 64);
      else
         Lemma_C_Lin_X (AL, AH, Shift_Left (1, J - 64));
         Clmul64.Lemma_Lo_Bit (AL, J - 64, 64);
         Clmul64.Lemma_Hi_Bit (AL, J - 64, 64);
         Clmul64.Lemma_Lo_Bit (AH, J - 64, 64);
         Clmul64.Lemma_Hi_Bit (AH, J - 64, 64);
         Clmul64.Lemma_By_Zero (AL, 64);
      end if;
   end Lemma_Kara_Bit;

   --  The bits of B below K.
   function Low128 (B : Element; K : Bit_Count) return Element is
     (if K = 0 then Zero
      elsif Bit (B, K - 1) then Add (Low128 (B, K - 1), E_Bit (K - 1))
      else Low128 (B, K - 1))
   with Ghost => Proof_Only,
        Global => null,
        Subprogram_Variant => (Decreases => K);

   procedure Lemma_Low128_All (B : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Low128 (B, 128) = B
   is
   begin
      for K in 0 .. 127 loop
         pragma Loop_Invariant
           (Low128 (B, K)
            = (if K < 64
               then Elem (B.Limbs (0) and (Shift_Left (1, K) - 1), 0)
               else Elem (B.Limbs (0),
                          B.Limbs (1) and (Shift_Left (1, K - 64) - 1))));
         pragma Assert
           (Low128 (B, K + 1)
            = (if Bit (B, K) then Add (Low128 (B, K), E_Bit (K))
               else Low128 (B, K)));
         pragma Assert
           (Bit (B, K)
            = ((Shift_Right (B.Limbs (Limb_Index (K / 64)), K mod 64)
                and 1) = 1));
         pragma Assert
           (Low128 (B, K + 1)
            = (if K + 1 < 64
               then Elem (B.Limbs (0) and (Shift_Left (1, K + 1) - 1), 0)
               else Elem (B.Limbs (0),
                          B.Limbs (1)
                          and (Shift_Left (1, K + 1 - 64) - 1))));
      end loop;
   end Lemma_Low128_All;

   --  Mul_Ref reads B through its bits: equal limbs give equal products
   --  (the predefined equality of Element compares the limbs, which the
   --  provers do not identify with the logical equality).
   procedure Lemma_Mul_Ref_Ext (A, B1, B2 : Element; N : Bit_Count) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => B1 = B2,
     Post   => Mul_Ref (A, B1, N) = Mul_Ref (A, B2, N),
     Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Mul_Ref_Ext (A, B1, B2, N - 1);
         pragma Assert (Bit (B1, 128 - N) = Bit (B2, 128 - N));
      end if;
   end Lemma_Mul_Ref_Ext;

   --  The reduced Karatsuba product is Mul_Ref, by induction over the
   --  bits of B.
   procedure Lemma_Main (A, B : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Red (Kara (A, B)) = Mul_Ref (A, B, 128)
   is
   begin
      Clmul64.Lemma_By_Zero (A.Limbs (0), 64);
      Clmul64.Lemma_By_Zero (A.Limbs (1), 64);
      Clmul64.Lemma_By_Zero (A.Limbs (0) xor A.Limbs (1), 64);
      Lemma_Mul_Ref_Zero (A, 128);
      pragma Assert (Red (Kara (A, Zero)) = Mul_Ref (A, Low128 (B, 0), 128));
      for K in 0 .. 127 loop
         pragma Loop_Invariant
           (Red (Kara (A, Low128 (B, K))) = Mul_Ref (A, Low128 (B, K), 128));
         if Bit (B, K) then
            Lemma_Kara_Lin (A, Low128 (B, K), E_Bit (K));
            Lemma_Red_Lin (Kara (A, Low128 (B, K)), Kara (A, E_Bit (K)));
            Lemma_Mul_Ref_Lin (A, Low128 (B, K), E_Bit (K), 128);
            Lemma_Kara_Bit (A, K);
            Lemma_Red_Shl (A, K);
            Lemma_Mul_Ref_Bit (A, K, 128);
         end if;
         pragma Assert
           (Red (Kara (A, Low128 (B, K + 1)))
            = Mul_Ref (A, Low128 (B, K + 1), 128));
      end loop;
      pragma Assert
        (Red (Kara (A, Low128 (B, 128))) = Mul_Ref (A, Low128 (B, 128), 128));
      Lemma_Low128_All (B);
      pragma Assert (Low128 (B, 128) = B);
      pragma Assert (Kara (A, Low128 (B, 128)) = Kara (A, B));
      Lemma_Mul_Ref_Ext (A, Low128 (B, 128), B, 128);
   end Lemma_Main;

   ----------------------------------------------------------------------
   --  The product is associative (ADR 0066), against
   --  Mul_Ref: linear in each operand, Xtime moves out of either one
   --  (through x^128 = x^7 + x^2 + x + 1, checked on the basis), then
   --  Horner over the bits of the third operand.
   ----------------------------------------------------------------------

   --  x^7 + x^2 + x + 1, the image of x^128.
   R128 : constant Element := (Limbs => [0 => Reduction_Low, 1 => 0])
   with Ghost => Proof_Only;

   --  If C then X else Zero.
   function Sel (C : Boolean; X : Element) return Element is
     (if C then X else Zero)
   with Ghost => Proof_Only, Global => null;

   -------------------------------------------------------------------
   --  Xtime
   -------------------------------------------------------------------

   procedure Lemma_Xt_Lin (X, Y : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Xtime (Add (X, Y)) = Add (Xtime (X), Xtime (Y))
   is
   begin
      pragma Assert (Bit (Add (X, Y), 127) = (Bit (X, 127) /= Bit (Y, 127)));
   end Lemma_Xt_Lin;

   procedure Lemma_Xt_Ext (X, Y : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => X = Y,
     Post   => Xtime (X) = Xtime (Y)
   is
   begin
      pragma Assert (Bit (X, 127) = Bit (Y, 127));
   end Lemma_Xt_Ext;

   procedure Lemma_Xt_Zero with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Xtime (Zero) = Zero
   is
   begin
      pragma Assert (not Bit (Zero, 127));
   end Lemma_Xt_Zero;

   -------------------------------------------------------------------
   --  Mul_Ref: congruence, zero, linearity
   -------------------------------------------------------------------

   procedure Lemma_Ext_A (A1, A2, B : Element; N : Bit_Count) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => A1 = A2,
     Post   => Mul_Ref (A1, B, N) = Mul_Ref (A2, B, N),
     Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Ext_A (A1, A2, B, N - 1);
         Lemma_Xt_Ext (Mul_Ref (A1, B, N - 1), Mul_Ref (A2, B, N - 1));
      end if;
   end Lemma_Ext_A;

   procedure Lemma_Zero_A (B : Element; N : Bit_Count) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (Zero, B, N) = Zero,
     Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Zero_A (B, N - 1);
         Lemma_Xt_Ext (Mul_Ref (Zero, B, N - 1), Zero);
         Lemma_Xt_Zero;
      end if;
   end Lemma_Zero_A;

   procedure Lemma_Lin_A (A1, A2, B : Element; N : Bit_Count) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (Add (A1, A2), B, N)
               = Add (Mul_Ref (A1, B, N), Mul_Ref (A2, B, N)),
     Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Lin_A (A1, A2, B, N - 1);
         Lemma_Xt_Ext (Mul_Ref (Add (A1, A2), B, N - 1),
                       Add (Mul_Ref (A1, B, N - 1), Mul_Ref (A2, B, N - 1)));
         Lemma_Xt_Lin (Mul_Ref (A1, B, N - 1), Mul_Ref (A2, B, N - 1));
      end if;
   end Lemma_Lin_A;

   --  Xtime moves out of the first operand.
   procedure Lemma_Xt_A (A, B : Element; N : Bit_Count) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (Xtime (A), B, N) = Xtime (Mul_Ref (A, B, N)),
     Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Xt_A (A, B, N - 1);
         Lemma_Xt_Ext (Mul_Ref (Xtime (A), B, N - 1),
                       Xtime (Mul_Ref (A, B, N - 1)));
         Lemma_Xt_Lin (Xtime (Mul_Ref (A, B, N - 1)), A);
      end if;
   end Lemma_Xt_A;

   -------------------------------------------------------------------
   --  Powers of x
   -------------------------------------------------------------------

   procedure Lemma_Xpow_Ext (X, Y : Element; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => X = Y,
     Post   => Xpow (X, J) = Xpow (Y, J),
     Subprogram_Variant => (Decreases => J)
   is
   begin
      if J > 0 then
         Lemma_Xpow_Ext (X, Y, J - 1);
         Lemma_Xt_Ext (Xpow (X, J - 1), Xpow (Y, J - 1));
      end if;
   end Lemma_Xpow_Ext;

   procedure Lemma_Xpow_Lin (X, Y : Element; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Xpow (Add (X, Y), J) = Add (Xpow (X, J), Xpow (Y, J)),
     Subprogram_Variant => (Decreases => J)
   is
   begin
      if J > 0 then
         Lemma_Xpow_Lin (X, Y, J - 1);
         Lemma_Xt_Ext (Xpow (Add (X, Y), J - 1),
                       Add (Xpow (X, J - 1), Xpow (Y, J - 1)));
         Lemma_Xt_Lin (Xpow (X, J - 1), Xpow (Y, J - 1));
      end if;
   end Lemma_Xpow_Lin;

   procedure Lemma_Xpow_Add (X : Element; I, J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => I <= 1024 and then J <= 1024,
     Post   => Xpow (Xpow (X, I), J) = Xpow (X, I + J),
     Subprogram_Variant => (Decreases => J)
   is
   begin
      if J > 0 then
         Lemma_Xpow_Add (X, I, J - 1);
         Lemma_Xt_Ext (Xpow (Xpow (X, I), J - 1), Xpow (X, I + J - 1));
      end if;
   end Lemma_Xpow_Add;

   --  x^K is the bit K for K < 128, and x^128 is R128.
   procedure Lemma_Xpow_One (K : Bit_Count) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Xpow (One, K) = (if K < 128 then E_Bit (K) else R128),
     Subprogram_Variant => (Decreases => K)
   is
   begin
      if K > 0 then
         Lemma_Xpow_One (K - 1);
         Lemma_Xt_Ext (Xpow (One, K - 1), E_Bit (K - 1));
         if K - 1 < 63 then
            pragma Assert (not Bit (E_Bit (K - 1), 127));
            pragma Assert (Xtime (E_Bit (K - 1)) = E_Bit (K));
         elsif K - 1 = 63 then
            pragma Assert (not Bit (E_Bit (K - 1), 127));
            pragma Assert (Xtime (E_Bit (K - 1)) = E_Bit (K));
         elsif K - 1 < 127 then
            pragma Assert (not Bit (E_Bit (K - 1), 127));
            pragma Assert (Xtime (E_Bit (K - 1)) = E_Bit (K));
         else
            pragma Assert (Bit (E_Bit (127), 127));
            pragma Assert (Xtime (E_Bit (127)) = R128);
         end if;
      end if;
   end Lemma_Xpow_One;

   --  R128 as the sum of its four bits.
   procedure Lemma_R128_Bits with
     Ghost  => Proof_Only,
     Global => null,
     Post   => R128
               = Add (Add (Add (E_Bit (7), E_Bit (2)), E_Bit (1)), E_Bit (0))
   is
   begin
      null;
   end Lemma_R128_Bits;

   --  Mul_Ref (A, R128) as the sum of four powers of A.
   procedure Lemma_Mul_R128 (A : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (A, R128, 128)
               = Add (Add (Add (Xpow (A, 7), Xpow (A, 2)), Xpow (A, 1)),
                      Xpow (A, 0))
   is
      R7 : constant Element := E_Bit (7);
      R2 : constant Element := E_Bit (2);
      R1 : constant Element := E_Bit (1);
      R0 : constant Element := E_Bit (0);
   begin
      Lemma_R128_Bits;
      Lemma_Mul_Ref_Ext (A, R128, Add (Add (Add (R7, R2), R1), R0), 128);
      Lemma_Mul_Ref_Lin (A, Add (Add (R7, R2), R1), R0, 128);
      Lemma_Mul_Ref_Lin (A, Add (R7, R2), R1, 128);
      Lemma_Mul_Ref_Lin (A, R7, R2, 128);
      Lemma_Mul_Ref_Bit (A, 7, 128);
      Lemma_Mul_Ref_Bit (A, 2, 128);
      Lemma_Mul_Ref_Bit (A, 1, 128);
      Lemma_Mul_Ref_Bit (A, 0, 128);
   end Lemma_Mul_R128;

   --  x^128 A = R128 A on one bit of A.
   procedure Lemma_X128_Bit (I : Bit_Index_128) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Xpow (E_Bit (I), 128) = Mul_Ref (E_Bit (I), R128, 128)
   is
      E : constant Element := E_Bit (I);
      S : constant Element :=
        Add (Add (Add (Xpow (E, 7), Xpow (E, 2)), Xpow (E, 1)), Xpow (E, 0));
   begin
      Lemma_Mul_R128 (E);
      --  E = x^I, so E x^K = x^K x^I.
      Lemma_Xpow_One (I);
      Lemma_Xpow_Ext (Xpow (One, I), E, 128);
      Lemma_Xpow_Add (One, I, 128);
      Lemma_Xpow_Add (One, 128, I);
      Lemma_Xpow_One (128);
      Lemma_Xpow_Ext (Xpow (One, 128), R128, I);
      pragma Assert (Xpow (E, 128) = Xpow (R128, I));
      --  The four powers of E, each x^I times a bit of R128.
      Lemma_Xpow_Ext (Xpow (One, I), E, 7);
      Lemma_Xpow_Add (One, I, 7);
      Lemma_Xpow_Add (One, 7, I);
      Lemma_Xpow_One (7);
      Lemma_Xpow_Ext (Xpow (One, 7), E_Bit (7), I);
      pragma Assert (Xpow (E, 7) = Xpow (E_Bit (7), I));
      Lemma_Xpow_Ext (Xpow (One, I), E, 2);
      Lemma_Xpow_Add (One, I, 2);
      Lemma_Xpow_Add (One, 2, I);
      Lemma_Xpow_One (2);
      Lemma_Xpow_Ext (Xpow (One, 2), E_Bit (2), I);
      pragma Assert (Xpow (E, 2) = Xpow (E_Bit (2), I));
      Lemma_Xpow_Ext (Xpow (One, I), E, 1);
      Lemma_Xpow_Add (One, I, 1);
      Lemma_Xpow_Add (One, 1, I);
      Lemma_Xpow_One (1);
      Lemma_Xpow_Ext (Xpow (One, 1), E_Bit (1), I);
      pragma Assert (Xpow (E, 1) = Xpow (E_Bit (1), I));
      Lemma_Xpow_Ext (One, E_Bit (0), I);
      pragma Assert (Xpow (E, 0) = Xpow (E_Bit (0), I));
      --  Their sum is x^I R128.
      Lemma_R128_Bits;
      Lemma_Xpow_Ext (R128, Add (Add (Add (E_Bit (7), E_Bit (2)), E_Bit (1)),
                              E_Bit (0)), I);
      Lemma_Xpow_Lin (Add (Add (E_Bit (7), E_Bit (2)), E_Bit (1)),
                      E_Bit (0), I);
      Lemma_Xpow_Lin (Add (E_Bit (7), E_Bit (2)), E_Bit (1), I);
      Lemma_Xpow_Lin (E_Bit (7), E_Bit (2), I);
      pragma Assert (Xpow (R128, I) = S);
   end Lemma_X128_Bit;

   procedure Lemma_Xpow_Zero (J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Xpow (Zero, J) = Zero,
     Subprogram_Variant => (Decreases => J)
   is
   begin
      if J > 0 then
         Lemma_Xpow_Zero (J - 1);
         Lemma_Xt_Ext (Xpow (Zero, J - 1), Zero);
         Lemma_Xt_Zero;
      end if;
   end Lemma_Xpow_Zero;

   --  x^128 A = R128 A for every A, by induction over the bits of A.
   procedure Lemma_X128 (A : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Xpow (A, 128) = Mul_Ref (A, R128, 128)
   is
   begin
      Lemma_Xpow_Zero (128);
      Lemma_Zero_A (R128, 128);
      for K in 0 .. 127 loop
         pragma Loop_Invariant
           (Xpow (Low128 (A, K), 128) = Mul_Ref (Low128 (A, K), R128, 128));
         if Bit (A, K) then
            Lemma_X128_Bit (K);
            Lemma_Xpow_Lin (Low128 (A, K), E_Bit (K), 128);
            Lemma_Lin_A (Low128 (A, K), E_Bit (K), R128, 128);
         end if;
      end loop;
      Lemma_Low128_All (A);
      Lemma_Xpow_Ext (Low128 (A, 128), A, 128);
      Lemma_Ext_A (Low128 (A, 128), A, R128, 128);
   end Lemma_X128;

   -------------------------------------------------------------------
   --  Xtime moves out of the second operand
   -------------------------------------------------------------------

   --  Y shifted left by one, bit 127 dropped.
   function Shl (Y : Element) return Element is
     (Elem (Shift_Left (Y.Limbs (0), 1),
          Shift_Left (Y.Limbs (1), 1) or Shift_Right (Y.Limbs (0), 63)))
   with Ghost => Proof_Only, Global => null;

   procedure Lemma_Xt_Split (Y : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Xtime (Y) = Add (Shl (Y), Sel (Bit (Y, 127), R128))
   is
   begin
      null;
   end Lemma_Xt_Split;

   --  Horner over the top N + 1 bits of Y is bit 127 times x^N A plus
   --  Horner over the top N bits of Shl (Y).
   procedure Lemma_Top (A, Y : Element; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N <= 127,
     Post   => Mul_Ref (A, Y, N + 1)
               = Add (Sel (Bit (Y, 127), Xpow (A, N)),
                      Mul_Ref (A, Shl (Y), N)),
     Subprogram_Variant => (Decreases => N)
   is
   begin
      if N = 0 then
         Lemma_Xt_Zero;
      else
         Lemma_Top (A, Y, N - 1);
         Lemma_Xt_Ext (Mul_Ref (A, Y, N),
                       Add (Sel (Bit (Y, 127), Xpow (A, N - 1)),
                            Mul_Ref (A, Shl (Y), N - 1)));
         Lemma_Xt_Lin (Sel (Bit (Y, 127), Xpow (A, N - 1)),
                       Mul_Ref (A, Shl (Y), N - 1));
         if not Bit (Y, 127) then
            Lemma_Xt_Zero;
         end if;
         pragma Assert (Bit (Shl (Y), 128 - N) = Bit (Y, 127 - N));
      end if;
   end Lemma_Top;

   procedure Lemma_Xt_B (A, Y : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (A, Xtime (Y), 128) = Xtime (Mul_Ref (A, Y, 128))
   is
      S : constant Element := Shl (Y);
   begin
      Lemma_Top (A, Y, 127);
      pragma Assert (not Bit (S, 0));
      Lemma_Xt_Ext (Mul_Ref (A, Y, 128),
                    Add (Sel (Bit (Y, 127), Xpow (A, 127)),
                         Mul_Ref (A, S, 127)));
      Lemma_Xt_Lin (Sel (Bit (Y, 127), Xpow (A, 127)), Mul_Ref (A, S, 127));
      Lemma_Xt_Split (Y);
      Lemma_Mul_Ref_Ext (A, Xtime (Y), Add (S, Sel (Bit (Y, 127), R128)), 128);
      Lemma_Mul_Ref_Lin (A, S, Sel (Bit (Y, 127), R128), 128);
      if Bit (Y, 127) then
         Lemma_X128 (A);
      else
         Lemma_Xt_Zero;
         Lemma_Mul_Ref_Zero (A, 128);
      end if;
   end Lemma_Xt_B;

   -------------------------------------------------------------------
   --  Associativity
   -------------------------------------------------------------------

   procedure Lemma_Assoc_Ref (A, B, C : Element; N : Bit_Count) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (Mul_Ref (A, B, 128), C, N)
               = Mul_Ref (A, Mul_Ref (B, C, N), 128),
     Subprogram_Variant => (Decreases => N)
   is
   begin
      if N = 0 then
         Lemma_Mul_Ref_Zero (A, 128);
      else
         Lemma_Assoc_Ref (A, B, C, N - 1);
         Lemma_Xt_Ext (Mul_Ref (Mul_Ref (A, B, 128), C, N - 1),
                       Mul_Ref (A, Mul_Ref (B, C, N - 1), 128));
         Lemma_Xt_B (A, Mul_Ref (B, C, N - 1));
         pragma Assert
           (Xtime (Mul_Ref (Mul_Ref (A, B, 128), C, N - 1))
            = Mul_Ref (A, Xtime (Mul_Ref (B, C, N - 1)), 128));
         if Bit (C, 128 - N) then
            pragma Assert
              (Mul_Ref (B, C, N) = Add (Xtime (Mul_Ref (B, C, N - 1)), B));
            Lemma_Mul_Ref_Ext
              (A, Mul_Ref (B, C, N), Add (Xtime (Mul_Ref (B, C, N - 1)), B),
               128);
            Lemma_Mul_Ref_Lin (A, Xtime (Mul_Ref (B, C, N - 1)), B, 128);
            pragma Assert
              (Mul_Ref (Mul_Ref (A, B, 128), C, N)
               = Add (Xtime (Mul_Ref (Mul_Ref (A, B, 128), C, N - 1)),
                      Mul_Ref (A, B, 128)));
         else
            pragma Assert
              (Mul_Ref (B, C, N) = Xtime (Mul_Ref (B, C, N - 1)));
            Lemma_Mul_Ref_Ext
              (A, Mul_Ref (B, C, N), Xtime (Mul_Ref (B, C, N - 1)), 128);
            pragma Assert
              (Mul_Ref (Mul_Ref (A, B, 128), C, N)
               = Xtime (Mul_Ref (Mul_Ref (A, B, 128), C, N - 1)));
         end if;
      end if;
   end Lemma_Assoc_Ref;

   procedure Lemma_Mul_Assoc (A, B, C : Element) is
   begin
      Lemma_Assoc_Ref (A, B, C, 128);
      Lemma_Ext_A (Mul (A, B), Mul_Ref (A, B, 128), C, 128);
      Lemma_Mul_Ref_Ext (A, Mul (B, C), Mul_Ref (B, C, 128), 128);
   end Lemma_Mul_Assoc;

   -------------------------------------------------------------------
   --  Commutativity (ADR 0070): x^J times B is x^J (A B) with A = One,
   --  One is the unit of Mul_Ref on the left, so a single bit commutes
   --  with any element, then linearity over the bits of B.
   -------------------------------------------------------------------

   --  x^J moves out of the first operand.
   procedure Lemma_Xpow_A (A, B : Element; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (Xpow (A, J), B, 128) = Xpow (Mul_Ref (A, B, 128), J),
     Subprogram_Variant => (Decreases => J)
   is
   begin
      if J > 0 then
         Lemma_Xpow_A (A, B, J - 1);
         Lemma_Xt_A (Xpow (A, J - 1), B, 128);
         Lemma_Ext_A (Xpow (A, J), Xtime (Xpow (A, J - 1)), B, 128);
         Lemma_Xt_Ext (Mul_Ref (Xpow (A, J - 1), B, 128),
                       Xpow (Mul_Ref (A, B, 128), J - 1));
      end if;
   end Lemma_Xpow_A;

   --  One is the unit on the left.
   procedure Lemma_One_Ref (B : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (One, B, 128) = B
   is
   begin
      Lemma_Mul_Ref_Zero (One, 128);
      pragma Assert (Mul_Ref (One, Low128 (B, 0), 128) = Low128 (B, 0));
      for K in 0 .. 127 loop
         pragma Loop_Invariant
           (Mul_Ref (One, Low128 (B, K), 128) = Low128 (B, K));
         if Bit (B, K) then
            Lemma_Mul_Ref_Ext
              (One, Low128 (B, K + 1), Add (Low128 (B, K), E_Bit (K)), 128);
            Lemma_Mul_Ref_Lin (One, Low128 (B, K), E_Bit (K), 128);
            Lemma_Mul_Ref_Bit (One, K, 128);
            Lemma_Xpow_One (K);
         else
            Lemma_Mul_Ref_Ext (One, Low128 (B, K + 1), Low128 (B, K), 128);
         end if;
         pragma Assert
           (Mul_Ref (One, Low128 (B, K + 1), 128) = Low128 (B, K + 1));
      end loop;
      Lemma_Low128_All (B);
      Lemma_Mul_Ref_Ext (One, Low128 (B, 128), B, 128);
   end Lemma_One_Ref;

   --  A single bit commutes: both sides are x^K A.
   procedure Lemma_Bit_Comm (A : Element; K : Bit_Index_128) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (E_Bit (K), A, 128) = Mul_Ref (A, E_Bit (K), 128)
   is
   begin
      Lemma_Xpow_One (K);
      Lemma_Ext_A (E_Bit (K), Xpow (One, K), A, 128);
      Lemma_Xpow_A (One, A, K);
      Lemma_One_Ref (A);
      Lemma_Xpow_Ext (Mul_Ref (One, A, 128), A, K);
      Lemma_Mul_Ref_Bit (A, K, 128);
   end Lemma_Bit_Comm;

   procedure Lemma_Comm_Ref (A, B : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul_Ref (A, B, 128) = Mul_Ref (B, A, 128)
   is
   begin
      Lemma_Mul_Ref_Zero (A, 128);
      Lemma_Zero_A (A, 128);
      pragma Assert
        (Mul_Ref (A, Low128 (B, 0), 128) = Mul_Ref (Low128 (B, 0), A, 128));
      for K in 0 .. 127 loop
         pragma Loop_Invariant
           (Mul_Ref (A, Low128 (B, K), 128) = Mul_Ref (Low128 (B, K), A, 128));
         if Bit (B, K) then
            Lemma_Mul_Ref_Ext
              (A, Low128 (B, K + 1), Add (Low128 (B, K), E_Bit (K)), 128);
            Lemma_Mul_Ref_Lin (A, Low128 (B, K), E_Bit (K), 128);
            Lemma_Ext_A
              (Low128 (B, K + 1), Add (Low128 (B, K), E_Bit (K)), A, 128);
            Lemma_Lin_A (Low128 (B, K), E_Bit (K), A, 128);
            Lemma_Bit_Comm (A, K);
         else
            Lemma_Mul_Ref_Ext (A, Low128 (B, K + 1), Low128 (B, K), 128);
            Lemma_Ext_A (Low128 (B, K + 1), Low128 (B, K), A, 128);
         end if;
         pragma Assert
           (Mul_Ref (A, Low128 (B, K + 1), 128)
            = Mul_Ref (Low128 (B, K + 1), A, 128));
      end loop;
      Lemma_Low128_All (B);
      Lemma_Mul_Ref_Ext (A, Low128 (B, 128), B, 128);
      Lemma_Ext_A (Low128 (B, 128), B, A, 128);
   end Lemma_Comm_Ref;

   procedure Lemma_Mul_Comm (A, B : Element) is
   begin
      Lemma_Comm_Ref (A, B);
   end Lemma_Mul_Comm;

   procedure Lemma_Mul_One (A : Element) is
   begin
      pragma Assert (E_Bit (0) = One);
      Lemma_Mul_Ref_Bit (A, 0, 128);
      Lemma_Mul_Ref_Ext (A, One, E_Bit (0), 128);
   end Lemma_Mul_One;

   procedure Lemma_Mul_Distrib (A, B, C : Element) is
   begin
      Lemma_Mul_Ref_Lin (A, B, C, 128);
   end Lemma_Mul_Distrib;

   procedure Lemma_Mul_Distrib_Sub (A, B, C : Element) is
   begin
      Lemma_Mul_Ref_Lin (A, B, C, 128);
      Lemma_Mul_Ref_Ext (A, Sub (B, C), Add (B, C), 128);
   end Lemma_Mul_Distrib_Sub;

   function Mul (A, B : Element) return Element is
      L0, H0, L1, H1, L2, H2 : U64;
   begin
      Clmul64.Clmul_Kara
        (A.Limbs (0), A.Limbs (1), B.Limbs (0), B.Limbs (1),
         L0, H0, L1, H1, L2, H2);
      declare
         T0 : constant Element := Elem (L0, H0);
         T1 : constant Element := Elem (L1, H1);
         T2 : constant Element := Elem (L2, H2);
      begin
         Lemma_Upstream_Red (T0, T1, T2);
         Lemma_Main (A, B);
         return Reduce (T0, Reduce (T1, T2));
      end;
   end Mul;

   function Square (E : Element) return Element is
   begin
      return Mul (E, E);
   end Square;

   --  E^(2^N): N successive squarings. Local helper, not in the spec.
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
      --  Itoh-Tsujii style chain. T_k holds E^(2^k - 1); the step
      --  T_(a+b) = T_a^(2^b) * T_b follows from
      --  (2^a - 1) * 2^b + (2^b - 1) = 2^(a+b) - 1.
      --  Chain: 1, 2, 3, 6, 7, 14, 15, 30, 31, 62, 63, 126, 127:
      --  12 multiplications and 126 squarings, then one final squaring
      --  gives (E^(2^127 - 1))^2 = E^(2^128 - 2).
      T1   : constant Element := E;
      T2   : constant Element := Mul (Square_N (T1, 1), T1);
      T3   : constant Element := Mul (Square_N (T2, 1), T1);
      T6   : constant Element := Mul (Square_N (T3, 3), T3);
      T7   : constant Element := Mul (Square_N (T6, 1), T1);
      T14  : constant Element := Mul (Square_N (T7, 7), T7);
      T15  : constant Element := Mul (Square_N (T14, 1), T1);
      T30  : constant Element := Mul (Square_N (T15, 15), T15);
      T31  : constant Element := Mul (Square_N (T30, 1), T1);
      T62  : constant Element := Mul (Square_N (T31, 31), T31);
      T63  : constant Element := Mul (Square_N (T62, 1), T1);
      T126 : constant Element := Mul (Square_N (T63, 63), T63);
      T127 : constant Element := Mul (Square_N (T126, 1), T1);
   begin
      return Square (T127);
   end Inv;


   ----------------------------------------------------------------------
   --  Serialisation
   ----------------------------------------------------------------------

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

   function Limbs_Of_Bytes (B : Bytes_16) return Limb_Array is
     [Limb_Of_8 (B (0 .. 7)), Limb_Of_8 (B (8 .. 15))];

   function Bytes_Of_Limbs (L : Limb_Array) return Bytes_16 is
      R : Bytes_16 := [others => 0];
   begin
      R (0 .. 7)  := Bytes_Of_Limb (L (0));
      R (8 .. 15) := Bytes_Of_Limb (L (1));
      return R;
   end Bytes_Of_Limbs;

   procedure From_Bytes (B : Bytes_16; E : out Element; Ok : out Boolean)
   is
   begin
      Ok := True;
      E  := (Limbs => Limbs_Of_Bytes (B));
   end From_Bytes;


   function Inject (X : Subfield_Value) return Element is
      R : Element := Zero;
   begin
      for I in Basis_Index loop
         if (X / 2 ** I) mod 2 = 1 then
            R := Add (R, Subfield_Basis (I));
         end if;
         pragma Loop_Invariant (Proof_Only => R = Inject_Ref (X, I + 1));
      end loop;
      return R;
   end Inject;

   function Parity (V : Unsigned_64) return Unsigned_64 is
      X : Unsigned_64 := V;
   begin
      X := X xor Shift_Right (X, 32);
      X := X xor Shift_Right (X, 16);
      X := X xor Shift_Right (X, 8);
      X := X xor Shift_Right (X, 4);
      X := X xor Shift_Right (X, 2);
      X := X xor Shift_Right (X, 1);
      return X and 1;
   end Parity;

   function Subfield_Coords (E : Element) return Subfield_Value is
      R : Unsigned_16 := 0;
   begin
      --  Coordinate 15 first, so that each step shifts the previous
      --  ones up: modular arithmetic, no overflow to prove.
      for I in reverse Mask_Index loop
         R := Shift_Left (R, 1)
              or Unsigned_16 (Parity (E.Limbs (0) and Subfield_Mask (I)));
      end loop;
      return Subfield_Value (R);
   end Subfield_Coords;

end GF2_128;
