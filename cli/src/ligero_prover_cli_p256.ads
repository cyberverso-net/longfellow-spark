--  Ligero_Prover over P-256 with the source of longfellow_prove.

pragma SPARK_Mode (Off);

with Ligero_Prover;
with Ligero_Verifier_P256;
with Sampling_Cli_P256;

package Ligero_Prover_Cli_P256 is new Ligero_Prover
  (LV => Ligero_Verifier_P256, SP => Sampling_Cli_P256);
