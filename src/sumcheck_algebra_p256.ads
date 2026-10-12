--  Sumcheck_Algebra over the P-256 base field (ADR 0024). A
--  library-level generic instantiation: GNATprove analyses this
--  instance, with the contracts of P256_Field visible, and make prove
--  counts its checks.

pragma SPARK_Mode (On);

with Sumcheck_Algebra;
with Field_P256;

package Sumcheck_Algebra_P256 is new Sumcheck_Algebra (Field_P256.Sig);
