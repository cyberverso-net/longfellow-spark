--  Ligero_Prover over P-256, encoding with the real FFT, with the
--  source of the command-line provers, longfellow_prove and
--  longfellow_prove_mdoc (Cli_Random, ADR 0050).
--
--  Proof status: outside SPARK (SPARK_Mode Off), compiled with the
--  run-time checks on (register rows C2 and T7). GNATprove proves the
--  generic on its library instance Ligero_Prover_P256, over Simple_Rng
--  (header of src/ligero_prover.ads); this instance is the same generic
--  over Cli_Random, whose bytes are trusted (rows C1 and P4).

pragma SPARK_Mode (Off);

with Rfft_P256;
with Ligero_Prover;
with Ligero_Verifier_P256;
with Sampling_Cli_P256;

package Ligero_Prover_Cli_P256 is new Ligero_Prover
  (LV      => Ligero_Verifier_P256,
   SP      => Sampling_Cli_P256,
   Use_Fft => True,
   Extend  => Rfft_P256.Extend);
