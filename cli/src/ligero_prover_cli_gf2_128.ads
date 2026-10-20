--  Ligero_Prover over GF(2^128) with the source of longfellow_prove.

pragma SPARK_Mode (Off);

with Additive_Fft;
with Ligero_Prover;
with Ligero_Verifier_GF2_128;
with Sampling_Cli_GF2_128;

package Ligero_Prover_Cli_GF2_128 is new Ligero_Prover
  (LV      => Ligero_Verifier_GF2_128,
   SP      => Sampling_Cli_GF2_128,
   Use_Fft => True,
   Extend  => Additive_Fft.Extend);
