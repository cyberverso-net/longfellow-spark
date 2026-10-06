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

end GF2_128;
