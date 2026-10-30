--  Packed_Circuits over the P-256 base field.

pragma SPARK_Mode (On);

with Packed_Circuits;
with Sumcheck_Algebra_P256;

package Packed_Circuits_P256 is new Packed_Circuits
  (SA => Sumcheck_Algebra_P256);
