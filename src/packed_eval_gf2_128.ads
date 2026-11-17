--  Packed_Eval over the binary field GF(2^128) (ADR 0080): a
--  library-level instance, proved by GNATprove with make prove
--  (partition packed_hquad). The command-line provers use this instance
--  too. What is proved, tested and trusted is stated in the header of
--  Packed_Eval.

pragma SPARK_Mode (On);

with Packed_Eval;
with Sumcheck_Algebra_GF2_128;
with Packed_Circuits_GF2_128;

package Packed_Eval_GF2_128 is new Packed_Eval
  (SA => Sumcheck_Algebra_GF2_128,
   PC => Packed_Circuits_GF2_128);
