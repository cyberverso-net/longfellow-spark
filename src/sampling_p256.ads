--  Sampling over P-256 with the test source Simple_Rng (ADR
--  0050). A library-level generic instantiation: GNATprove analyses
--  this instance and make prove counts its checks; the command-line
--  prover instantiates the generic again with the operating system's
--  source.

pragma SPARK_Mode (On);

with Sampling;
with Field_P256;
with Simple_Rng;

package Sampling_P256 is new Sampling
  (F => Field_P256.Sig, Fill => Simple_Rng.Fill);
