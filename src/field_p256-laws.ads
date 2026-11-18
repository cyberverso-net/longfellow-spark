--  Field_P256.Laws: the predefined equality of two elements gives Same
--  (ADR 0066). The limbs are scalar components (ADR 0070), so equal
--  limbs make equal elements. In a unit of its own, as
--  Field_GF2_128.Laws.
--
--  Documentation: docs/guide/03-sumcheck.md, Section 3.1. Proof status:
--  the lemma is proved, at the level Proof_Only (register row T8); it
--  rests on Same being the equality of the element type (row T6).

pragma SPARK_Mode (On);

with Proof_Levels;

package Field_P256.Laws is

   procedure Lemma_Same (X, Y : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => X = Y,
     Post   => Same (X, Y);

end Field_P256.Laws;
