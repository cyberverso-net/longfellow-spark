--  Ligero_Prover over GF(2^128) with the test source Simple_Rng (ADR
--  0049, ADR 0050). A library-level generic instantiation: GNATprove
--  analyses this instance and make prove counts its checks; the
--  command-line prover instantiates the generic again with the
--  operating system's source.

pragma SPARK_Mode (On);

with Ligero_Prover;
with Ligero_Verifier_GF2_128;
with Sampling_GF2_128;

package Ligero_Prover_GF2_128 is new Ligero_Prover
  (LV => Ligero_Verifier_GF2_128, SP => Sampling_GF2_128);
