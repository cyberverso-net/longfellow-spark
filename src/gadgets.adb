pragma SPARK_Mode (On);

package body Gadgets is

   procedure Lemma_Value_Bits_Of (V : Unsigned_32) is
      B : constant Word_Bits := Bits_Of (V);
      U : constant Unsigned_64 := Unsigned_64 (V);
   begin
      for N in 1 .. 32 loop
         pragma Assert
           ((B (N - 1) = GF2_128.One)
            = ((Shift_Right (U, N - 1) and 1) = 1));
         pragma Loop_Invariant
           (Value_Upto (B, N) = (U and (Pow2 (N) - 1)));
      end loop;
      pragma Assert (Value_Upto (B, 32) = U);
      pragma Assert (for all I in Bit_Index => Is_Bit (B (I)));
   end Lemma_Value_Bits_Of;

   procedure Lemma_Bits_Of_Value (W : Word_Bits) is
   begin
      for N in 1 .. 32 loop
         pragma Loop_Invariant
           (for all I in 0 .. N - 1 =>
              ((Shift_Right (Value_Upto (W, N), I) and 1) = 1)
              = (W (I) = GF2_128.One));
      end loop;
      pragma Assert
        (for all I in Bit_Index =>
           ((Shift_Right (Value (W), I) and 1) = 1)
           = (W (I) = GF2_128.One));
      pragma Assert
        (for all I in Bit_Index =>
           ((Shift_Right (Word_Value (W), I) and 1) = 1)
           = (W (I) = GF2_128.One));
   end Lemma_Bits_Of_Value;

   procedure Lemma_Value_Ext (A, B : Word_Bits) is
   begin
      for N in 1 .. 32 loop
         pragma Assert ((A (N - 1) = GF2_128.One) = (B (N - 1) = GF2_128.One));
         pragma Loop_Invariant (Value_Upto (A, N) = Value_Upto (B, N));
      end loop;
   end Lemma_Value_Ext;

   procedure Lemma_Mul_Cong (A1, A2, B1, B2 : Element) is
   begin
      for N in 1 .. 128 loop
         pragma Assert (GF2_128.Bit (B1, 128 - N) = GF2_128.Bit (B2, 128 - N));
         pragma Loop_Invariant
           (GF2_128.Mul_Ref (A1, B1, N) = GF2_128.Mul_Ref (A2, B2, N));
      end loop;
   end Lemma_Mul_Cong;

   procedure Lemma_Mul_Zero (A : Element) is
   begin
      for N in 1 .. 128 loop
         pragma Assert (not GF2_128.Bit (GF2_128.Zero, 128 - N));
         pragma Loop_Invariant
           (GF2_128.Mul_Ref (A, GF2_128.Zero, N) = GF2_128.Zero);
      end loop;
   end Lemma_Mul_Zero;

end Gadgets;
