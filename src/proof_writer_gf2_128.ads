--  Proof_Writer over GF(2^128) (ADR 0049): a library-level instance,
--  proved by GNATprove with make prove (partition prover). The
--  command-line provers use this instance too. What is proved, tested
--  and trusted is stated in the header of Proof_Writer.

pragma SPARK_Mode (On);

with Proof_Writer;
with Ligero_Verifier_GF2_128;

package Proof_Writer_GF2_128 is new Proof_Writer (Ligero_Verifier_GF2_128);
