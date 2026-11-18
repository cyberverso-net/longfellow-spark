--  Sumcheck_Prover over GF(2^128) with the test source Simple_Rng (ADR
--  0049, ADR 0050): a library-level instance, proved by GNATprove with
--  make prove (partition prover). The command-line provers instantiate
--  the generic again, as Sumcheck_Prover_Cli_GF2_128, over their own
--  source Cli_Random (outside SPARK, register row C2). What is proved,
--  tested and trusted is stated in the header of Sumcheck_Prover.

pragma SPARK_Mode (On);

with Sumcheck_Prover;
with Sumcheck_Transcript_GF2_128;
with Sampling_GF2_128;
with Packed_HQuad_GF2_128;

package Sumcheck_Prover_GF2_128 is new Sumcheck_Prover
  (ST => Sumcheck_Transcript_GF2_128, SP => Sampling_GF2_128,
   PH => Packed_HQuad_GF2_128);
