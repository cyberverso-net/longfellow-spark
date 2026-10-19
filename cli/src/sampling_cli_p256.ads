--  Sampling over P-256 with the source of longfellow_prove (Cli_Random,
--  ADR 0050). Outside the proof perimeter: the source is; the generic
--  is proved on its library instances.

pragma SPARK_Mode (Off);

with Sampling;
with Field_P256;
with Cli_Random;

package Sampling_Cli_P256 is new Sampling
  (F => Field_P256.Sig, Fill => Cli_Random.Fill);
