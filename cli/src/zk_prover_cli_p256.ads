--  Zk_Prover over P-256 with the source of the command-line provers,
--  longfellow_prove and longfellow_prove_mdoc (Cli_Random, ADR 0050).
--
--  Proof status: outside SPARK (SPARK_Mode Off), compiled with the
--  run-time checks on (register rows C2 and T7). The predicate checks
--  of the circuit stay suppressed inside the generic, which GNATprove
--  proves (ADR 0072). GNATprove proves the generic on its library
--  instance Zk_Prover_P256, over Simple_Rng (header of
--  src/zk_prover.ads); this instance is the same generic over
--  Cli_Random, whose bytes are trusted (rows C1 and P4).

pragma SPARK_Mode (Off);

with Zk_Prover;
with Ligero_Prover_Cli_P256;
with Sumcheck_Prover_Cli_P256;
with Proof_Writer_P256;
with Packed_HQuad_P256;
with Packed_Eval_P256;

package Zk_Prover_Cli_P256 is new Zk_Prover
  (LPR => Ligero_Prover_Cli_P256,
   PH  => Packed_HQuad_P256,
   SPR => Sumcheck_Prover_Cli_P256,
   PW  => Proof_Writer_P256,
   PE  => Packed_Eval_P256);
