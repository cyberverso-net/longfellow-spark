--  Field_P256.Laws: the predefined equality of two elements gives Same
--  (ADR 0066). The limbs are scalar components (ADR 0070), so equal
--  limbs make equal elements. In a unit of its own, as
--  Field_GF2_128.Laws.

pragma SPARK_Mode (On);

with Proof_Levels;

package Field_P256.Laws is

   procedure Lemma_Same (X, Y : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => X = Y,
     Post   => Same (X, Y);

end Field_P256.Laws;
