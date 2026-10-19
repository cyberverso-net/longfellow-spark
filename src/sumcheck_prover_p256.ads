--  Sumcheck_Prover over the P-256 base field with the test source
--  Simple_Rng (ADR 0049, ADR 0050). A library-level generic
--  instantiation: GNATprove analyses this instance and make prove
--  counts its checks; the command-line prover instantiates the generic
--  again with the operating system's source.

pragma SPARK_Mode (On);

with Sumcheck_Prover;
with Sumcheck_Transcript_P256;
with Sampling_P256;

package Sumcheck_Prover_P256 is new Sumcheck_Prover
  (ST => Sumcheck_Transcript_P256, SP => Sampling_P256);
