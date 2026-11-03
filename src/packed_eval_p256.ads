--  Packed_Eval over the prime field P-256.

pragma SPARK_Mode (On);

with Packed_Eval;
with Sumcheck_Algebra_P256;
with Packed_Circuits_P256;

package Packed_Eval_P256 is new Packed_Eval
  (SA => Sumcheck_Algebra_P256,
   PC => Packed_Circuits_P256);
