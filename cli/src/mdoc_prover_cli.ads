--  Mdoc_Prover over the chains of longfellow_prove_mdoc, with the
--  source of the command line (Cli_Random, ADR 0050).
--
--  Proof status: outside SPARK (SPARK_Mode Off), compiled with the
--  run-time checks on (register rows C2 and T7). GNATprove proves the
--  generic on its library instance Mdoc_Prover_Lib, over Simple_Rng
--  (header of src/mdoc_prover.ads); this instance is the same generic
--  over Cli_Random, whose bytes are trusted (rows C1 and P4).

pragma SPARK_Mode (Off);

with Mdoc_Prover;
with Ligero_Prover_Cli_GF2_128;
with Zk_Prover_Cli_GF2_128;
with Ligero_Prover_Cli_P256;
with Zk_Prover_Cli_P256;

package Mdoc_Prover_Cli is new Mdoc_Prover
  (LPRH => Ligero_Prover_Cli_GF2_128,
   ZKH  => Zk_Prover_Cli_GF2_128,
   LPRS => Ligero_Prover_Cli_P256,
   ZKS  => Zk_Prover_Cli_P256);
