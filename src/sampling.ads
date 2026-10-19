--  Sampling: the prover's draws from a byte stream (Phase C, ADR 0050),
--  as the reference builds them on Rng::bytes (docs/specs/rust/src/
--  algebra at d5e6be7): an element is Serialized_Size bytes read by
--  From_Bytes, repeated until accepted (sample_gf2_128: one draw of 16
--  bytes; sample_p256: 32 bytes little-endian, rejected at or above p,
--  a loop); a subfield element is Subfield_Size bytes read by
--  From_Subfield_Bytes (BinarySubfield::sample: 2 bytes on the basis;
--  on P-256 the field's own sampler); a Merkle nonce is 32 bytes
--  (commit_merkle_heap). Generic over the field signature and the
--  source, a procedure that fills any array with fresh bytes, so that
--  the prover is proved for any source.
--
--  Documentation: docs/guide/07-prover.md.
--
--  Proof status. Silver. The rejection loops are literal, as ADR 0030:
--  no cap, declared possibly non-terminating for a field that rejects.
--  Constant-time discipline (ADR 0051): the draws depend on the
--  randomness, not on the witness.

pragma SPARK_Mode (On);

with Bytes; use Bytes;
with Field_Signature;

generic
   with package F is new Field_Signature (<>);
   with procedure Fill (B : out Byte_Array);
package Sampling is

   subtype Element is F.Element;

   procedure Sample_Element (E : out Element) with
     Always_Terminates => not F.Sampling_Rejects;

   procedure Sample_Subfield (E : out Element) with
     Always_Terminates => not F.Sampling_Rejects;

   procedure Sample_Nonce (N : out Bytes_32);

end Sampling;
