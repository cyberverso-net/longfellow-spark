--  Sumcheck_Verifier over the P-256 base field (ADR 0022, ADR 0024): a
--  library-level instance, proved by GNATprove with make prove.

pragma SPARK_Mode (On);

with Sumcheck_Verifier;
with Sumcheck_Algebra_P256;
with Sumcheck_Expression_P256;

package Sumcheck_Verifier_P256 is new
  Sumcheck_Verifier (Sumcheck_Algebra_P256, Sumcheck_Expression_P256);
