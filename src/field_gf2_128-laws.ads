--  Field_GF2_128.Laws: the predefined equality of two elements gives Same
--  (ADR 0066). In a unit of its own: in the body of Field_GF2_128, which
--  implements Same, the provers do not establish it.

pragma SPARK_Mode (On);

with Proof_Levels;

package Field_GF2_128.Laws is

   procedure Lemma_Same (X, Y : GF2_128.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => X = Y,
     Post   => Same (X, Y);

end Field_GF2_128.Laws;
