--  Zk_Prover over GF(2^128) with the source of longfellow_prove.

pragma SPARK_Mode (Off);

with Zk_Prover;
with Ligero_Prover_Cli_GF2_128;
with Sumcheck_Prover_Cli_GF2_128;
with Proof_Writer_GF2_128;

package Zk_Prover_Cli_GF2_128 is new Zk_Prover
  (LPR => Ligero_Prover_Cli_GF2_128,
   SPR => Sumcheck_Prover_Cli_GF2_128,
   PW  => Proof_Writer_GF2_128);
