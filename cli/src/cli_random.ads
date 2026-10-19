--  Cli_Random: the randomness source of longfellow_prove (ADR 0050).
--  Fill reads the operating system's generator (Os_Random) unless a
--  seed was set, in which case it reads Simple_Rng, the generator of
--  the upstream reference test: reproducible, hence predictable, a
--  test option. One source procedure, so that one chain of prover
--  instances serves both. Outside the proof perimeter (SPARK_Mode
--  Off), as Os_Random.

pragma SPARK_Mode (Off);

with Interfaces; use Interfaces;
with Bytes;      use Bytes;

package Cli_Random is

   --  From now on, Fill draws from Simple_Rng seeded with S.
   procedure Set_Seed (S : Unsigned_64);

   procedure Fill (B : out Byte_Array);

end Cli_Random;
