--  Ligero_Verifier over GF(2^128) (ADR 0035): a library-level instance,
--  proved by GNATprove with make prove (partition verifier). What is
--  proved, tested and trusted is stated in the header of
--  Ligero_Verifier.

pragma SPARK_Mode (On);

with Ligero_Verifier;
with Sumcheck_Transcript_GF2_128;
with Ligero_Proof_GF2_128;
with Lagrange_GF2_128;

package Ligero_Verifier_GF2_128 is new
  Ligero_Verifier
    (Sumcheck_Transcript_GF2_128, Ligero_Proof_GF2_128, Lagrange_GF2_128);
