--  Sampling over P-256 with the source of the command-line provers,
--  longfellow_prove and longfellow_prove_mdoc (Cli_Random, ADR 0050).
--
--  Proof status: outside SPARK (SPARK_Mode Off), compiled with the
--  run-time checks on (register rows C2 and T7). GNATprove proves the
--  generic on its library instance Sampling_P256, over Simple_Rng
--  (header of src/sampling.ads); this instance is the same generic over
--  Cli_Random, whose bytes are trusted (rows C1 and P4).

pragma SPARK_Mode (Off);

with Sampling;
with Field_P256;
with Cli_Random;

package Sampling_Cli_P256 is new Sampling
  (F => Field_P256.Sig, Fill => Cli_Random.Fill);
