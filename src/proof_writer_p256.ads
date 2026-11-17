--  Proof_Writer over the P-256 base field (ADR 0049): a library-level
--  instance, proved by GNATprove with make prove (partition prover).
--  The command-line provers use this instance too. What is proved,
--  tested and trusted is stated in the header of Proof_Writer.

pragma SPARK_Mode (On);

with Proof_Writer;
with Ligero_Verifier_P256;

package Proof_Writer_P256 is new Proof_Writer (Ligero_Verifier_P256);
