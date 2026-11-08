--  Mdoc_Proof: the layout of an mDoc proof (longfellow-zk/longfellow-zk
--  d5e6be7, rust/applications/mdoc_zk/runtime/src/proto.rs,
--  MdocProof::write and read; Phase D, block 5, ADR 0058). The proof
--  is one byte string: the six tags of Mdoc_Mac, each as its 128-bit
--  value in 16 little-endian bytes (96 bytes); then the proof of the
--  hash circuit, the proof string of draft Section 7.5 that
--  Proof_Writer writes and Zk_Verifier reads; then the proof of the
--  signature circuit, the same; nothing after. The length of the hash
--  proof is not written: the reader learns it by reading the proof
--  under the geometry of its circuit (Zk_Verifier.Receive returns the
--  offset after it, After), and the signature proof starts there.
--
--  This package holds the fixed part, the tags. The two proofs are
--  read and written by the generic units, at the offsets Mdoc_Prover
--  and Mdoc_Verifier compute.
--
--  Documentation: docs/guide/09-mdoc.md.
--
--  Proof status. Gold: Write_Tags writes the 16 bytes of each tag at
--  16 I, and Read_Tags reads them back, the postconditions naming the
--  bytes; Read_Tags of Write_Tags is the identity by the contracts of
--  GF2_128.Bytes_Of_Limbs. Silver on everything.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE. The tags are
--  public, and the proof string is public once written.

pragma SPARK_Mode (On);

with Bytes;    use Bytes;
with GF2_128;  use GF2_128;
with Mdoc_Mac; use Mdoc_Mac;

package Mdoc_Proof is

   Tag_Bytes : constant := 16;
   Tags_Len  : constant := 6 * Tag_Bytes;

   --  The offset of the hash proof in an mDoc proof.
   Hash_First : constant := Tags_Len;

   procedure Write_Tags (T : Tags; B : out Byte_Array) with
     Global => null,
     Pre    => B'First = 0 and then B'Length = Tags_Len,
     Post   =>
       (for all I in Tag_Index =>
          B (Tag_Bytes * I .. Tag_Bytes * I + Tag_Bytes - 1)
          = To_Bytes (T (I)));

   --  The six tags at the start of B.
   function Read_Tags (B : Byte_Array) return Tags with
     Global => null,
     Pre    => B'First = 0 and then B'Length >= Tags_Len,
     Post   =>
       (for all I in Tag_Index =>
          Read_Tags'Result (I).Limbs
          = Limbs_Of_Bytes
              (B (Tag_Bytes * I .. Tag_Bytes * I + Tag_Bytes - 1)));

end Mdoc_Proof;
