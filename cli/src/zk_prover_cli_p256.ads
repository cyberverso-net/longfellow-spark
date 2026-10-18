--  Zk_Prover over P-256 with the source of longfellow_prove.

pragma SPARK_Mode (Off);

with Zk_Prover;
with Ligero_Prover_Cli_P256;
with Sumcheck_Prover_Cli_P256;
with Proof_Writer_P256;

package Zk_Prover_Cli_P256 is new Zk_Prover
  (LPR => Ligero_Prover_Cli_P256,
   SPR => Sumcheck_Prover_Cli_P256,
   PW  => Proof_Writer_P256);
