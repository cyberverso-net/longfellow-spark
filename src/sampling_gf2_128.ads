--  Sampling over GF(2^128) with the test source Simple_Rng (ADR
--  0050). A library-level generic instantiation: GNATprove analyses
--  this instance and make prove counts its checks; the command-line
--  prover instantiates the generic again with the operating system's
--  source.

pragma SPARK_Mode (On);

with Sampling;
with Field_GF2_128;
with Simple_Rng;

package Sampling_GF2_128 is new Sampling
  (F => Field_GF2_128.Sig, Fill => Simple_Rng.Fill);
