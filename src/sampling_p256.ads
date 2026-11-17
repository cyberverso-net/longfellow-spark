--  Sampling over P-256 with the test source Simple_Rng (ADR 0050): a
--  library-level instance, proved by GNATprove with make prove
--  (partition prover). The command-line provers instantiate the generic
--  again, as Sampling_Cli_P256, over their own source Cli_Random
--  (outside SPARK, register row C2). What is proved, tested and trusted
--  is stated in the header of Sampling.

pragma SPARK_Mode (On);

with Sampling;
with Field_P256;
with Simple_Rng;

package Sampling_P256 is new Sampling
  (F => Field_P256.Sig, Fill => Simple_Rng.Fill);
