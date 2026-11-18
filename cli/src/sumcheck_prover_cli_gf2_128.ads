--  Sumcheck_Prover over GF(2^128) with the source of the command-line
--  provers, longfellow_prove and longfellow_prove_mdoc (Cli_Random, ADR
--  0050).
--
--  Proof status: outside SPARK (SPARK_Mode Off), compiled with the
--  run-time checks on (register rows C2 and T7). The predicate checks
--  of the circuit stay suppressed inside the generic, which GNATprove
--  proves (ADR 0072). GNATprove proves the generic on its library
--  instance Sumcheck_Prover_GF2_128, over Simple_Rng (header of
--  src/sumcheck_prover.ads); this instance is the same generic over
--  Cli_Random, whose bytes are trusted (rows C1 and P4).

pragma SPARK_Mode (Off);

with Sumcheck_Prover;
with Sumcheck_Transcript_GF2_128;
with Sampling_Cli_GF2_128;
with Packed_HQuad_GF2_128;

package Sumcheck_Prover_Cli_GF2_128 is new Sumcheck_Prover
  (ST => Sumcheck_Transcript_GF2_128, SP => Sampling_Cli_GF2_128,
   PH => Packed_HQuad_GF2_128);
