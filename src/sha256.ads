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
--              Since block 6 of Phase D the child Sha256.Trace repeats
--              the compression of a block with its trace, over the same
--              round functions and constants, declared in the private
--              part below for both (ADR 0086); this unit's own code
--              path is unchanged.
--
--  Interface. A Context accumulates bytes (Update); Digest is a
--  function, so it returns the hash of everything absorbed so far and
--  leaves the context as it was, and the accumulator survives, as
--  get_hash does in the reference (docs/specs/rust/src/transcript.rs
--  at d5e6be7). Messages longer than 2^61 bytes are outside FIPS
--  180-4 (the length field is 64 bits of bit length); the byte counter
--  is modular and no precondition states the bound.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE to the
--  verifier's use, by ADR 0029: the transcript and the Merkle check
--  process the public content of a proof string. The prover hashes the
--  nonces and the columns of the committed tableau (Ligero_Prover.
--  Hash_Leaves), which are secret until the proof is written; ADR 0051
--  admits that use because the compression function has
--  data-independent control flow and memory access, and each leaf is
--  hashed over a fixed length. No other use on secret data is admitted
--  without a new decision.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Bytes;      use Bytes;

package Sha256 is

   type Context is private;

   --  The eight working words of the hash (FIPS 180-4 Section 5.3.3),
   --  public so that the child Sha256.Trace exposes the compression of
   --  one block with its trace (Phase D, block 6, ADR 0086).
   type Word_Index is range 0 .. 7;
   type State is array (Word_Index) of Unsigned_32;

   --  Section 5.3.3: the initial hash value.
   Initial_State : constant State :=
     [16#6A09E667#, 16#BB67AE85#, 16#3C6EF372#, 16#A54FF53A#,
      16#510E527F#, 16#9B05688C#, 16#1F83D9AB#, 16#5BE0CD19#];

   function Initial return Context with
     Global => null;

   procedure Update (Ctx : in out Context; Data : Byte_Array) with
     Global => null;

   --  The digest of the absorbed bytes, the 32 bytes in the order of
   --  FIPS 180-4 (big-endian words H0 .. H7).
   function Digest (Ctx : Context) return Bytes_32 with
     Global => null;

private

   --  FIPS 180-4 Section 4.2.2: the first 32 bits of the fractional
   --  parts of the cube roots of the first 64 primes; and the six
   --  functions of Section 4.1.2. Shared with the child Sha256.Trace,
   --  whose traced compression is this unit's compression with the
   --  words of the rounds written out.
   type Round_Index is range 0 .. 63;
   type Round_Constants is array (Round_Index) of Unsigned_32;

   K : constant Round_Constants :=
     [16#428A2F98#, 16#71374491#, 16#B5C0FBCF#, 16#E9B5DBA5#,
      16#3956C25B#, 16#59F111F1#, 16#923F82A4#, 16#AB1C5ED5#,
      16#D807AA98#, 16#12835B01#, 16#243185BE#, 16#550C7DC3#,
      16#72BE5D74#, 16#80DEB1FE#, 16#9BDC06A7#, 16#C19BF174#,
      16#E49B69C1#, 16#EFBE4786#, 16#0FC19DC6#, 16#240CA1CC#,
      16#2DE92C6F#, 16#4A7484AA#, 16#5CB0A9DC#, 16#76F988DA#,
      16#983E5152#, 16#A831C66D#, 16#B00327C8#, 16#BF597FC7#,
      16#C6E00BF3#, 16#D5A79147#, 16#06CA6351#, 16#14292967#,
      16#27B70A85#, 16#2E1B2138#, 16#4D2C6DFC#, 16#53380D13#,
      16#650A7354#, 16#766A0ABB#, 16#81C2C92E#, 16#92722C85#,
      16#A2BFE8A1#, 16#A81A664B#, 16#C24B8B70#, 16#C76C51A3#,
      16#D192E819#, 16#D6990624#, 16#F40E3585#, 16#106AA070#,
      16#19A4C116#, 16#1E376C08#, 16#2748774C#, 16#34B0BCB5#,
      16#391C0CB3#, 16#4ED8AA4A#, 16#5B9CCA4F#, 16#682E6FF3#,
      16#748F82EE#, 16#78A5636F#, 16#84C87814#, 16#8CC70208#,
      16#90BEFFFA#, 16#A4506CEB#, 16#BEF9A3F7#, 16#C67178F2#];

   function Ch (X, Y, Z : Unsigned_32) return Unsigned_32 is
     ((X and Y) xor ((not X) and Z));

   function Maj (X, Y, Z : Unsigned_32) return Unsigned_32 is
     ((X and Y) xor (X and Z) xor (Y and Z));

   function Sigma_0 (X : Unsigned_32) return Unsigned_32 is
     (Rotate_Right (X, 2) xor Rotate_Right (X, 13) xor Rotate_Right (X, 22));

   function Sigma_1 (X : Unsigned_32) return Unsigned_32 is
     (Rotate_Right (X, 6) xor Rotate_Right (X, 11) xor Rotate_Right (X, 25));

   function Small_0 (X : Unsigned_32) return Unsigned_32 is
     (Rotate_Right (X, 7) xor Rotate_Right (X, 18) xor Shift_Right (X, 3));

   function Small_1 (X : Unsigned_32) return Unsigned_32 is
     (Rotate_Right (X, 17) xor Rotate_Right (X, 19) xor Shift_Right (X, 10));

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
