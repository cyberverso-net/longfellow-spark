--  Ligero_Prover over GF(2^128), encoding with the additive FFT, with
--  the source of the command-line provers, longfellow_prove and
--  longfellow_prove_mdoc (Cli_Random, ADR 0050).
--
--  Proof status: outside SPARK (SPARK_Mode Off), compiled with the
--  run-time checks on (register rows C2 and T7). GNATprove proves the
--  generic on its library instance Ligero_Prover_GF2_128, over
--  Simple_Rng (header of src/ligero_prover.ads); this instance is the
--  same generic over Cli_Random, whose bytes are trusted (rows C1 and
--  P4).

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
