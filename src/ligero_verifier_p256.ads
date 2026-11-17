--  Ligero_Verifier over the P-256 base field (ADR 0035): a library-level
--  instance, proved by GNATprove with make prove (partition verifier).
--  What is proved, tested and trusted is stated in the header of
--  Ligero_Verifier. In this instance Draw_Challenges calls the P-256
--  sampler and is declared possibly non-terminating (register row V4).

pragma SPARK_Mode (On);

with Ligero_Verifier;
with Sumcheck_Transcript_P256;
with Ligero_Proof_P256;
with Lagrange_P256;

package Ligero_Verifier_P256 is new
  Ligero_Verifier
    (Sumcheck_Transcript_P256, Ligero_Proof_P256, Lagrange_P256);
