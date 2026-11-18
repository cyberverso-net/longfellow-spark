--  Mdoc_Prover over the library chains of both fields, with the test
--  source Simple_Rng (ADR 0049, ADR 0050). A library-level generic
--  instantiation: GNATprove analyses this instance and make prove
--  counts its checks (the partition mdoc); the command-line prover
--  instantiates the generic again over Cli_Random, which reads the
--  operating system's generator, or Simple_Rng under --seed
--  (Mdoc_Prover_Cli).
--
--  Documentation: docs/guide/09-mdoc.md, Section 3.2. Proof status:
--  that of Mdoc_Prover, which GNATprove proves through this instance.

pragma SPARK_Mode (On);

with Mdoc_Prover;
with Ligero_Prover_GF2_128;
with Zk_Prover_GF2_128;
with Ligero_Prover_P256;
with Zk_Prover_P256;

package Mdoc_Prover_Lib is new Mdoc_Prover
  (LPRH => Ligero_Prover_GF2_128,
   ZKH  => Zk_Prover_GF2_128,
   LPRS => Ligero_Prover_P256,
   ZKS  => Zk_Prover_P256);
