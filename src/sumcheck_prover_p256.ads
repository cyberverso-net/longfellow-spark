--  Sumcheck_Prover over the P-256 base field with the test source
--  Simple_Rng (ADR 0049, ADR 0050): a library-level instance, proved by
--  GNATprove with make prove (partition prover). The command-line
--  provers instantiate the generic again, as Sumcheck_Prover_Cli_P256,
--  over their own source Cli_Random (outside SPARK, register row C2).
--  What is proved, tested and trusted is stated in the header of
--  Sumcheck_Prover.

pragma SPARK_Mode (On);

with Sumcheck_Prover;
with Sumcheck_Transcript_P256;
with Sampling_P256;
with Packed_HQuad_P256;

package Sumcheck_Prover_P256 is new Sumcheck_Prover
  (ST => Sumcheck_Transcript_P256, SP => Sampling_P256,
   PH => Packed_HQuad_P256);
