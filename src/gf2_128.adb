pragma SPARK_Mode (On);

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

   function Mul (A, B : Element) return Element is
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
         pragma Loop_Invariant (R = Mul_Ref (A, B, K));
      end loop;
      return R;
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

end GF2_128;
