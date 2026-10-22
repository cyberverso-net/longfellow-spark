--  Field_P256.Laws: the predefined equality of two elements in normal
--  form gives Same (ADR 0066). Every result of P256_Field.Mul is in
--  normal form. In a unit of its own, as Field_GF2_128.Laws.

pragma SPARK_Mode (On);

with Proof_Levels;

package Field_P256.Laws is

   procedure Lemma_Same (X, Y : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => X = Y
               and then P256_Field.Eq (X, P256_Field.Norm (X))
               and then P256_Field.Eq (Y, P256_Field.Norm (Y)),
     Post   => Same (X, Y);

end Field_P256.Laws;
