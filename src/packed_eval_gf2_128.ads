--  Packed_Eval over the binary field GF(2^128).

pragma SPARK_Mode (On);

with Packed_Eval;
with Sumcheck_Algebra_GF2_128;
with Packed_Circuits_GF2_128;

package Packed_Eval_GF2_128 is new Packed_Eval
  (SA => Sumcheck_Algebra_GF2_128,
   PC => Packed_Circuits_GF2_128);
