--  Sumcheck_Expression over GF(2^128) (ADR 0024, ADR 0026): a
--  library-level instance, proved by GNATprove with make prove.
--  Proof status and documentation: see Sumcheck_Expression and
--  docs/guide/03-sumcheck.md, Section 4.2.

pragma SPARK_Mode (On);

with Sumcheck_Expression;
with Sumcheck_Algebra_GF2_128;

package Sumcheck_Expression_GF2_128 is new
  Sumcheck_Expression (Sumcheck_Algebra_GF2_128);
