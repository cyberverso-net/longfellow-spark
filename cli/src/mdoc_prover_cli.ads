--  Mdoc_Prover over the chains of longfellow_prove_mdoc, with the
--  source of the command line (Cli_Random, ADR 0050). Outside the
--  proof perimeter: the source is; the generic is proved on its
--  library instance Mdoc_Prover_Lib.

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
