--  Ligero_Prover over P-256 with the test source Simple_Rng, encoding
--  with the real FFT (Rfft_P256; ADR 0049, 0050, 0057): a library-level
--  instance, proved by GNATprove with make prove (partition
--  ligero-prover). The command-line provers instantiate the generic
--  again, as Ligero_Prover_Cli_P256, over their own source Cli_Random
--  (outside SPARK, register row C2). What is proved, tested and trusted
--  is stated in the header of Ligero_Prover.

pragma SPARK_Mode (On);

with Rfft_P256;
with Ligero_Prover;
with Ligero_Verifier_P256;
with Sampling_P256;

package Ligero_Prover_P256 is new Ligero_Prover
  (LV      => Ligero_Verifier_P256,
   SP      => Sampling_P256,
   Use_Fft => True,
   Extend  => Rfft_P256.Extend);
