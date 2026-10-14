--  Sumcheck_Transcript over the P-256 base field (ADR 0028): a
--  library-level instance, proved by GNATprove with make prove.

pragma SPARK_Mode (On);

with Sumcheck_Transcript;
with Sumcheck_Algebra_P256;
with Sumcheck_Expression_P256;
with Sumcheck_Verifier_P256;

package Sumcheck_Transcript_P256 is new
  Sumcheck_Transcript
    (Sumcheck_Algebra_P256, Sumcheck_Expression_P256, Sumcheck_Verifier_P256);
