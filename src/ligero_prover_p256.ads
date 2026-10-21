--  Ligero_Prover over P-256 with the test source Simple_Rng (ADR
--  0049, ADR 0050). A library-level generic instantiation: GNATprove
--  analyses this instance and make prove counts its checks; the
--  command-line prover instantiates the generic again with the
--  operating system's source.

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
