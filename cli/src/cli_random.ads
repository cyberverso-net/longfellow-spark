--  Cli_Random: the randomness source of the two command-line provers,
--  longfellow_prove and longfellow_prove_mdoc (ADR 0050). Fill reads
--  the operating system's generator (Os_Random) unless a seed was set,
--  in which case it reads Simple_Rng, the generator of the upstream
--  reference test: reproducible, hence predictable, a test option
--  (--seed). One source procedure, so that one chain of prover
--  instances serves both.
--
--  Documentation: docs/guide/07-prover.md, Section 3.2.
--
--  Proof status: outside SPARK (SPARK_Mode Off), as Os_Random, and
--  compiled with the run-time checks on (register rows C2 and T7).
--  Trusted: that Fill changes no state the prover reads (row C2); the
--  bytes of the default source (rows C1 and P4); that Simple_Rng is
--  upstream's generator, behind --seed (row R7).

pragma SPARK_Mode (Off);

with Interfaces; use Interfaces;
with Bytes;      use Bytes;

package Cli_Random is

   --  From now on, Fill draws from Simple_Rng seeded with S.
   procedure Set_Seed (S : Unsigned_64);

   procedure Fill (B : out Byte_Array);

end Cli_Random;
