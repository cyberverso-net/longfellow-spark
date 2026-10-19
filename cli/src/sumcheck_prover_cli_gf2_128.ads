--  Sumcheck_Prover over GF(2^128) with the source of longfellow_prove.

pragma SPARK_Mode (Off);

with Sumcheck_Prover;
with Sumcheck_Transcript_GF2_128;
with Sampling_Cli_GF2_128;

package Sumcheck_Prover_Cli_GF2_128 is new Sumcheck_Prover
  (ST => Sumcheck_Transcript_GF2_128, SP => Sampling_Cli_GF2_128);
