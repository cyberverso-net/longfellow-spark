--  Ligero_Prover over GF(2^128) with the test source Simple_Rng,
--  encoding with the additive FFT (Additive_Fft; ADR 0049, 0050, 0057):
--  a library-level instance, proved by GNATprove with make prove
--  (partition ligero-prover). The command-line provers instantiate the
--  generic again, as Ligero_Prover_Cli_GF2_128, over their own source
--  Cli_Random (outside SPARK, register row C2). What is proved, tested
--  and trusted is stated in the header of Ligero_Prover.

pragma SPARK_Mode (On);

with Additive_Fft;
with Ligero_Prover;
with Ligero_Verifier_GF2_128;
with Sampling_GF2_128;

package Ligero_Prover_GF2_128 is new Ligero_Prover
  (LV      => Ligero_Verifier_GF2_128,
   SP      => Sampling_GF2_128,
   Use_Fft => True,
   Extend  => Additive_Fft.Extend);
