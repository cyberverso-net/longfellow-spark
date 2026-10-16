pragma SPARK_Mode (On);

with Ligero_Verifier;
with Sumcheck_Transcript_P256;
with Ligero_Proof_P256;
with Lagrange_P256;

package Ligero_Verifier_P256 is new
  Ligero_Verifier
    (Sumcheck_Transcript_P256, Ligero_Proof_P256, Lagrange_P256);
