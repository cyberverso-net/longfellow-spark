--  Zk_Prover over GF(2^128) with the test source Simple_Rng (ADR 0049,
--  ADR 0050): a library-level instance, proved by GNATprove with make
--  prove (partition ligero-prover). The command-line provers
--  instantiate the generic again, as Zk_Prover_Cli_GF2_128, over their
--  own source Cli_Random (outside SPARK, register row C2). What is
--  proved, tested and trusted is stated in the header of Zk_Prover.

pragma SPARK_Mode (On);

with Zk_Prover;
with Ligero_Prover_GF2_128;
with Sumcheck_Prover_GF2_128;
with Proof_Writer_GF2_128;
with Packed_HQuad_GF2_128;
with Packed_Eval_GF2_128;

package Zk_Prover_GF2_128 is new Zk_Prover
  (LPR => Ligero_Prover_GF2_128,
   PH  => Packed_HQuad_GF2_128,
   SPR => Sumcheck_Prover_GF2_128,
   PW  => Proof_Writer_GF2_128,
   PE  => Packed_Eval_GF2_128);
