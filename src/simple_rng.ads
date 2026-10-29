--  Simple_Rng: the seeded generator of the upstream reference test
--  (longfellow-zk/longfellow-zk d5e6be7,
--  docs/specs/rust/tests/test_reference.rs, struct SimpleRng), a
--  linear congruential generator: the state is
--  multiplied by 6364136223846793005 and incremented by
--  1442695040888963407 modulo 2^64 for every byte, and the byte is
--  bits 32 to 39 of the new state. It is a TEST source (ADR 0050): it
--  makes the prover's output reproducible, which is what the byte-for-
--  byte comparison with the shipped upstream proofs needs, and it makes
--  it predictable, which forfeits zero knowledge. The command-line
--  prover offers it behind an explicit option only; its default source
--  is the operating system's generator. It is a library unit of src/
--  because the library-level instances of the prover units name their
--  source at instantiation (ADR 0050, Decision).
--
--  Documentation: docs/guide/07-prover.md. Proof status: Silver; the
--  recurrence is tested by the byte identity with the upstream proofs.
--  Constant-time discipline: not applicable, the state is not a secret
--  of the protocol and the source is for tests.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Bytes;      use Bytes;

package Simple_Rng with
  Abstract_State => State,
  Initializes    => State
is

   --  Start from the seed, as SimpleRng::new.
   procedure Seed (S : Unsigned_64) with
     Global => (Output => State);

   --  Fill B with the next B'Length bytes.
   procedure Fill (B : out Byte_Array) with
     Global => (In_Out => State);

end Simple_Rng;
