--  Sampling over GF(2^128) with the test source Simple_Rng (ADR 0050):
--  a library-level instance, proved by GNATprove with make prove
--  (partition prover). The command-line provers instantiate the generic
--  again, as Sampling_Cli_GF2_128, over their own source Cli_Random
--  (outside SPARK, register row C2). What is proved, tested and trusted
--  is stated in the header of Sampling.

pragma SPARK_Mode (On);

with Sampling;
with Field_GF2_128;
with Simple_Rng;

package Sampling_GF2_128 is new Sampling
  (F => Field_GF2_128.Sig, Fill => Simple_Rng.Fill);
