--  Sumcheck_Transcript over GF(2^128) (ADR 0028): a library-level
--  instance, proved by GNATprove with make prove.

pragma SPARK_Mode (On);

with Sumcheck_Transcript;
with Sumcheck_Algebra_GF2_128;
with Sumcheck_Expression_GF2_128;
with Sumcheck_Verifier_GF2_128;

package Sumcheck_Transcript_GF2_128 is new
  Sumcheck_Transcript
    (Sumcheck_Algebra_GF2_128, Sumcheck_Expression_GF2_128,
     Sumcheck_Verifier_GF2_128);
