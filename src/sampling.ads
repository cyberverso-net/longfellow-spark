--  Sampling: the prover's draws from a byte stream (ADR 0050), as the
--  reference builds them on Rng::bytes (docs/specs/rust/src/algebra at
--  d5e6be7): an element is Serialized_Size bytes read by From_Bytes,
--  repeated until accepted (sample_gf2_128: one draw of 16 bytes;
--  sample_p256: 32 bytes little-endian, rejected at or above p, a
--  loop); a subfield element is Subfield_Size bytes read by
--  From_Subfield_Bytes (BinarySubfield::sample: 2 bytes on the basis;
--  on P-256 the field's own sampler); a Merkle nonce is 32 bytes
--  (commit_merkle_heap). Generic over the field signature and the
--  source, a procedure that fills any array with fresh bytes, so that
--  the prover is proved for any source.
--
--  Documentation: docs/guide/07-prover.md, Sections 2.2, 3.1 and 3.2.
--
--  Proof status. Silver, for any byte stream the source gives: nothing
--  in the proof depends on the bytes being random. On GF(2^128) the
--  loops are dead and the procedures are proved to terminate. On P-256
--  the rejection loops are literal, as ADR 0030 decides: no cap,
--  declared possibly non-terminating (register row V4). Trusted: the
--  quality of the bytes, which is the source's (Simple_Rng in the
--  library instances, a test source, row R7; Cli_Random on the command
--  line, rows C1 and P4).
--
--  Constant-time discipline (ADR 0051): the draws depend on the
--  randomness, not on the witness. On P-256 the rejection loop branches
--  on whether a draw is canonical, as does the Runtime postcondition of
--  P256_Field.From_Bytes, one of the declared exceptions of register
--  row S4. The guarantee is scoped to builds with assertions disabled
--  (ADR 0006).

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
