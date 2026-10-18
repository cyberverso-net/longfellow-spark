--  Sumcheck_Prover over P-256 with the source of longfellow_prove.

pragma SPARK_Mode (Off);

with Sumcheck_Prover;
with Sumcheck_Transcript_P256;
with Sampling_Cli_P256;

package Sumcheck_Prover_Cli_P256 is new Sumcheck_Prover
  (ST => Sumcheck_Transcript_P256, SP => Sampling_Cli_P256);
