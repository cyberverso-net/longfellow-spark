--  Sumcheck_Verifier over GF(2^128) (ADR 0022, ADR 0024): a
--  library-level instance, proved by GNATprove with make prove.

pragma SPARK_Mode (On);

with Sumcheck_Verifier;
with Sumcheck_Algebra_GF2_128;
with Sumcheck_Expression_GF2_128;

package Sumcheck_Verifier_GF2_128 is new
  Sumcheck_Verifier (Sumcheck_Algebra_GF2_128, Sumcheck_Expression_GF2_128);
