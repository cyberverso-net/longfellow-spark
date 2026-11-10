--  Mdoc_Witness: the two witnesses of the mDoc proof of age from the
--  parsed credential (Phase D, block 6, ADR 0086), in the layouts of
--  upstream's runtime/src/concrete/legacy/private.rs at d5e6be7
--  (push_witness_hash, push_witness_attrs, push_witness_sig) with the
--  encodings of concrete/builder.rs.
--
--  The hash circuit's witness, GF(2^128) elements, in order: the three
--  bound values (the digest the issuer signed, the two coordinates of
--  the device key) as 768 bits, little-endian bytes and least
--  significant bit first (push_raw_bytes); the number of blocks of the
--  signed message as 8 bits; the padded signed message from its byte
--  18 to the end of the circuit's capacity (the first 18 bytes are the
--  COSE prefix the circuit holds); the SHA-256 trace of every block of
--  the capacity, the zero blocks included, each block as 184 words
--  (the schedule words 16 to 63, the e and the a of the 64 rounds
--  interleaved, the eight words of the new state) in the legacy
--  plucked form (push_v32_legacy: eight 4-bit chunks, least
--  significant first, the chunk c as the subfield element with bits
--  (c << 1) xor 15 over the first five elements of the basis); the four
--  12-bit offsets validFrom, validUntil, deviceKeyInfo, valueDigests;
--  per requested attribute the padded issuer-signed item into two
--  blocks as 1,024 bits, the trace of the two blocks, its digest offset
--  as 12 bits, then ei_pos, ei_len, ev_pos, ev_len as 12 bits each
--  (version 7: the slot position and the length of the identifier and
--  of the value; version 6: shifted and recomputed from the request's
--  identifier and value), and for version 7 the slot positions 1 to 3,
--  the four lengths as 12 bits each and the permutation as 8 bits;
--  last the six pads mac_ap. For version 7 and one attribute 84,166
--  elements, for version 6 74,154, the private counts of the archives.
--
--  The signature circuit's witness, P-256 elements: the three bound
--  values reduced into the field; the ECDSA witness of the issuer's
--  signature on the digest under the issuer's key, and of the device's
--  on the device authentication digest under the device key
--  (Ecdsa_Witness, 1,034 elements each); then per bound value the two
--  pads and the two halves of the value, each as 64 elements of two
--  bits (push_plucked_128_legacy: the chunk v as 2 v - 3), where block
--  5 already placed the pads (Mdoc_Inputs.Place_Pads). 2,839 elements.
--
--  Refusals, as statuses: an attribute of the request that the document
--  does not hold (upstream's AttributeNotFound), an item that does not
--  pad into two blocks (above Max_Item_Bytes: upstream refuses 256 and
--  above with AttributeTooLong and stops on 120 to 255), a signature
--  value s at or above the group order (upstream stops; the ECDSA
--  witness requires it below). On a refusal the witness array is zero
--  (postcondition): nothing of the credential stays in it.
--
--  Documentation: docs/guide/09-mdoc.md, Section 3.7.
--
--  Proof status (Silver = absence of run-time errors, Gold = proved
--  functional contracts).
--
--    Hash_Witness, Sig_Witness : Silver; Gold on the count (the whole
--              array is written, the position after the last piece is
--              its length), on the three encodings (the local
--              procedures Put_Bits, Put_V32_Legacy and Put_Plucked_128
--              write bit K, chunk K and pair K of their value at
--              position K of their piece), and, when Hash_Witness
--              accepts, on the pads being the last six elements of the
--              hash witness, as Mdoc_Inputs.Witness_Parts reads them;
--              on a refusal the array is zero. That the order of the
--              pieces and the elements are upstream's is tested: the
--              byte identity with the four witness files of the two
--              archives (mdoc_witness_kat) and the digests of both
--              witnesses of the 38 test documents against an
--              independent Python transcription.
--    Messages, Reduce : Silver.
--
--  Constant time: the encodings are fixed loops over fixed widths, and
--  each bit or chunk becomes an element without a branch on its value
--  (the bit as a limb, the chunk through Inject, the pair through the
--  field's arithmetic); the compression of every block of the capacity
--  is constant time; the arithmetic is the fields' and the curve's (ADR
--  0051, ADR 0086). What branches on the document is its structure,
--  which ADR 0086 declares: the length of an item against the bound,
--  the lookup of the requested attribute (identifiers of public
--  length), and the padding of the message and of the item, declared
--  outside the perimeter with the parse.

pragma SPARK_Mode (On);

with Bytes;   use Bytes;
with GF2_128;
with P256_Field;
with Cbor_Parse;
with Mdoc_Parse;
with Mdoc_Inputs;
with Mdoc_Mac;
with Ecdsa_Witness;
with Sumcheck_Algebra_GF2_128;
with Sumcheck_Algebra_P256;

package Mdoc_Witness is

   use type GF2_128.Element;
   use type P256_Field.Element;

   package SAH renames Sumcheck_Algebra_GF2_128;
   package SAP renames Sumcheck_Algebra_P256;

   subtype Version_Number is Mdoc_Parse.Version_Number;
   subtype Parsed_Mdoc is Mdoc_Parse.Parsed_Mdoc;
   subtype Attribute_List is Mdoc_Inputs.Attribute_List;

   --  An issuer-signed item pads into two SHA-256 blocks: at most 119
   --  bytes, tag 24 and head included.
   Max_Item_Bytes : constant := 2 * 64 - 9;

   --  One block's trace: 184 words of eight elements each.
   Block_Elements : constant := 184 * 8;

   function Mso_Blocks (V : Version_Number) return Positive is
     (Mdoc_Parse.Max_Blocks (V))
   with Global => null, Pre => V in 6 .. 7;

   function Per_Attribute (V : Version_Number) return Positive is
     (1_024 + 2 * Block_Elements + 12 + 4 * 12
      + (if V = 7 then 7 * 12 + 8 else 0))
   with Global => null, Pre => V in 6 .. 7;

   --  The private count of the hash circuit at a version for N
   --  requested attributes: 84,166 for version 7 and one, 74,154 for
   --  version 6 and one.
   function Hash_Count (V : Version_Number; N : Natural) return Positive is
     (768 + 8 + (64 * Mso_Blocks (V) - 18) * 8
      + Mso_Blocks (V) * Block_Elements + 4 * 12
      + N * Per_Attribute (V) + Mdoc_Inputs.Pad_Elements)
   with Global => null,
        Pre => V in 6 .. 7 and then N <= Mdoc_Inputs.Max_Attributes;

   Sig_Count : constant :=
     3 + 2 * Ecdsa_Witness.Count + Mdoc_Inputs.Sig_Tail_Elements;

   type Status is
     (Ok,
      Attribute_Not_Found,
      Attribute_Too_Long,
      Signature_Not_Canonical);

   --  The three bound values as the tags take them (Mdoc_Mac.Messages):
   --  32 little-endian bytes each, the order of the witness.
   function Messages (P : Parsed_Mdoc) return Mdoc_Mac.Messages with
     Global => null;

   --  The 256-bit integer of 32 big-endian bytes, as four words.
   function Nat_Of (B : Bytes_32) return Ecdsa_Witness.Nat_256 with
     Global => null;

   --  The integer of the four words modulo p, as upstream's reduce_nat:
   --  the words combined in the field.
   function Reduce (N : Ecdsa_Witness.Nat_256) return P256_Field.Element with
     Global => null;

   procedure Hash_Witness
     (Version : Version_Number;
      Mdoc    : Byte_Array;
      P       : Parsed_Mdoc;
      Attrs   : Attribute_List;
      Ap      : Mdoc_Mac.Pads;
      W       : out SAH.Element_Array;
      Result  : out Status)
   with
     Global => null,
     Pre    => Version in 6 .. 7
               and then Mdoc'Length <= Cbor_Parse.Max_Bytes
               and then Mdoc_Parse.In_Bounds (P, Mdoc'Length)
               and then P.Mso_Len <= Mdoc_Parse.Max_Wrapped_Mso (Version)
               and then Attrs'Length <= Mdoc_Inputs.Max_Attributes
               and then W'First = 0
               and then W'Length = Hash_Count (Version, Attrs'Length),
     Post   => (if Result = Ok then
                  (for all I in Mdoc_Mac.Message_Index =>
                     (for all H in Mdoc_Mac.Half_Index =>
                        W (W'Last - 5 + 2 * I + H) = Ap (I) (H)))
                else (for all I in W'Range => W (I) = GF2_128.Zero));

   procedure Sig_Witness
     (Mdoc       : Byte_Array;
      P          : Parsed_Mdoc;
      Pk_X, Pk_Y : P256_Field.Element;
      Ap         : Mdoc_Mac.Pads;
      W          : out SAP.Element_Array;
      Result     : out Status)
   with
     Global => null,
     Pre    => Mdoc'Length <= Cbor_Parse.Max_Bytes
               and then Mdoc_Parse.In_Bounds (P, Mdoc'Length)
               and then W'First = 0
               and then W'Length = Sig_Count,
     Post   => Result in Ok | Signature_Not_Canonical
               and then (if Result /= Ok then
                           (for all I in W'Range => W (I) = P256_Field.Zero));

end Mdoc_Witness;
