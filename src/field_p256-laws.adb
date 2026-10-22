pragma SPARK_Mode (On);

with Interfaces; use Interfaces;

package body Field_P256.Laws is

   procedure Lemma_Same (X, Y : P256_Field.Element) is
   begin
      pragma Assert
        (for all I in P256_Field.Limb_Index => X.Limbs (I) = Y.Limbs (I));
      pragma Assert
        (P256_Field.Eq (P256_Field.Norm (X), P256_Field.Norm (Y)));
   end Lemma_Same;

end Field_P256.Laws;
