--  Zk_Prover over P-256 with the test source Simple_Rng (ADR 0049,
--  ADR 0050). A library-level generic instantiation: GNATprove analyses
--  this instance and make prove counts its checks; the command-line
--  prover instantiates the generic again with the operating system's
--  source.

pragma SPARK_Mode (On);

with Zk_Prover;
with Ligero_Prover_P256;
with Sumcheck_Prover_P256;
with Proof_Writer_P256;

package Zk_Prover_P256 is new Zk_Prover
  (LPR => Ligero_Prover_P256,
   SPR => Sumcheck_Prover_P256,
   PW  => Proof_Writer_P256);
