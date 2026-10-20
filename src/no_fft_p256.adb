pragma SPARK_Mode (On);

with P256_Field;

package body No_Fft_P256 is

   procedure Extend (Row : Element_Array; Enc : out Element_Array) is
   begin
      Enc := [others => P256_Field.Zero];
      for X in 0 .. Row'Last loop
         Enc (X) := Row (X);
         pragma Loop_Invariant
           (for all X2 in 0 .. X => Field_P256.Same (Enc (X2), Row (X2)));
      end loop;
   end Extend;

end No_Fft_P256;
