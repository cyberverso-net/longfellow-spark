--  Packed_Circuits over the binary field GF(2^128) (ADR 0080): a
--  library-level instance, proved by GNATprove with make prove
--  (partition circuits). What is proved, tested and trusted is stated
--  in the header of Packed_Circuits.

pragma SPARK_Mode (On);

with Packed_Circuits;
with Sumcheck_Algebra_GF2_128;

package Packed_Circuits_GF2_128 is new Packed_Circuits
  (SA => Sumcheck_Algebra_GF2_128);
