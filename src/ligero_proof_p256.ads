--  Ligero_Proof over the P-256 base field (ADR 0035): a library-level
--  instance, proved by GNATprove with make prove (partition ligero).
--  What is proved, tested and trusted is stated in the header of
--  Ligero_Proof.

pragma SPARK_Mode (On);

with Ligero_Proof;
with Sumcheck_Algebra_P256;

package Ligero_Proof_P256 is new Ligero_Proof (Sumcheck_Algebra_P256);
