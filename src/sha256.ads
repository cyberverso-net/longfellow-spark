--  Sha256: the SHA-256 hash of FIPS 180-4, as the incremental
--  accumulator of the Fiat-Shamir transcript (draft Section 3.1: the
--  seed of the generator is SHA-256 of everything absorbed so far).
--
--  Documentation: docs/guide/04-transcript.md. Decisions implemented
--  here: ADR 0029 (written in SPARK, Silver, functional correctness
--  by NIST vectors, constant-time exemption); frame: ADR 0002, 0003,
--  0020. Index: docs/adr/README.md. The ghost model of the absorbed
--  bytes (ADR 0031) lives in Transcript, the single caller of Update,
--  because GNAT 16 has no ghost record components.
--
--  Proof status (Silver = absence of run-time errors, Gold = proved
--  functional contracts).
--
--    Initial, Update, Digest : Silver. That Digest is the SHA-256 of
--              the absorbed bytes is NOT proved; it is tested against
--              the FIPS 180-4 examples and CAVP short messages
--              (tests/vectors/sha256.txt, harness transcript_kat) and,
--              through the transcript, against draft Appendix B.2.
--
--  Interface. A Context accumulates bytes (Update); Digest is a
--  function, so it returns the hash of everything absorbed so far and
--  leaves the context as it was, and the accumulator survives, as
--  get_hash does in the reference (docs/specs/rust/src/transcript.rs
--  at d5e6be7). Messages longer than 2^61 bytes are outside FIPS
--  180-4 (the length field is 64 bits of bit length); the byte counter
--  is modular and no precondition states the bound.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0029.
--  This package processes public data only, the content of a proof
--  string; it MUST NOT be used on secret data.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Bytes;      use Bytes;

package Sha256 is

   type Context is private;

   function Initial return Context with
     Global => null;

   procedure Update (Ctx : in out Context; Data : Byte_Array) with
     Global => null;

   --  The digest of the absorbed bytes, the 32 bytes in the order of
   --  FIPS 180-4 (big-endian words H0 .. H7).
   function Digest (Ctx : Context) return Bytes_32 with
     Global => null;

private

   type Word_Index is range 0 .. 7;
   type State is array (Word_Index) of Unsigned_32;

   subtype Fill_Count is Natural range 0 .. 63;

   --  H is the running state; Block holds the Fill bytes of the current
   --  incomplete block; Total counts the absorbed bytes modulo 2^64.
   type Context is record
      H     : State;
      Block : Bytes_64;
      Fill  : Fill_Count;
      Total : Unsigned_64;
   end record;

end Sha256;
