--  Packed_Circuits over the P-256 base field (ADR 0080): a
--  library-level instance, proved by GNATprove with make prove
--  (partition circuits). What is proved, tested and trusted is stated
--  in the header of Packed_Circuits.

pragma SPARK_Mode (On);

with Packed_Circuits;
with Sumcheck_Algebra_P256;

package Packed_Circuits_P256 is new Packed_Circuits
  (SA => Sumcheck_Algebra_P256);
