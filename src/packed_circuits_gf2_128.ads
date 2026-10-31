--  Packed_Circuits over the binary field GF(2^128).

pragma SPARK_Mode (On);

with Packed_Circuits;
with Sumcheck_Algebra_GF2_128;

package Packed_Circuits_GF2_128 is new Packed_Circuits
  (SA => Sumcheck_Algebra_GF2_128);
