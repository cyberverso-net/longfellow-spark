--  Sampling over GF(2^128) with the source of longfellow_prove (Cli_Random,
--  ADR 0050). Outside the proof perimeter: the source is; the generic
--  is proved on its library instances.

pragma SPARK_Mode (Off);

with Sampling;
with Field_GF2_128;
with Cli_Random;

package Sampling_Cli_GF2_128 is new Sampling
  (F => Field_GF2_128.Sig, Fill => Cli_Random.Fill);
