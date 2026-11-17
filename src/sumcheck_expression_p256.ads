--  Sumcheck_Expression over the P-256 base field (ADR 0024, ADR 0026):
--  a library-level instance, proved by GNATprove with make prove.
--  Proof status and documentation: see Sumcheck_Expression and
--  docs/guide/03-sumcheck.md, Section 4.2.

pragma SPARK_Mode (On);

with Sumcheck_Expression;
with Sumcheck_Algebra_P256;

package Sumcheck_Expression_P256 is new
  Sumcheck_Expression (Sumcheck_Algebra_P256);
