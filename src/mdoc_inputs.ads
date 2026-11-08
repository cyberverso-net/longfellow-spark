--  Mdoc_Inputs: the public inputs of the two circuits of an mDoc proof
--  and the ends of the hash circuit's witness, in the legacy layout of
--  circuit versions 5 to 7 (longfellow-zk/longfellow-zk d5e6be7,
--  rust/applications/mdoc_zk/runtime/src/concrete/legacy/public.rs,
--  push_legacy_input_hash and push_legacy_input_sig, and private.rs,
--  push_witness_hash; Phase D, block 5, ADR 0058).
--
--  A circuit takes its inputs as field elements, one per wire. The
--  builders of upstream push one element per bit for everything that
--  is "bits", least significant bit first (an element One or Zero), one
--  element per 128-bit value for the tags and the challenge av, and
--  the field elements themselves for the issuer's key and the digest.
--
--  The hash circuit, over GF(2^128), for one or more attributes:
--
--    1          the constant one (OneWire, ADR 0064)
--    per attribute, version 7:
--      256      the CBOR text string of the identifier (Cbor_Encode),
--               as bits, then zero bits to 32 bytes
--      512      the CBOR value as bits, then zero bits to 64 bytes
--      8 + 8    two lengths: 1 + 17 + 1 + id_len (the framing of
--               "elementIdentifier" in the issuer-signed item) and
--               value_len + 12 + 1 (the framing of "elementValue")
--    per attribute, versions 5 and 6:
--      768      one buffer: the CBOR text of the identifier, the CBOR
--               text "elementValue", the value; as bits, then zero
--               bits to 96 bytes
--      8        its length
--    160        the date now, 20 bytes "YYYY-MM-DDThh:mm:ssZ" as bits;
--               a shorter date is padded with the element 2, which no
--               bit can equal
--    6          the tags, one element each
--    1          av
--
--  952 elements for version 7 with one attribute, 944 for version 6:
--  Hash_Count. The signature circuit, over P-256: the constant one, the
--  issuer's public key as two elements, e2 (Device_Auth) as one
--  element, the six tags as 128 bits each, av as 128 bits: 900
--  elements, Sig_Count. The counts are what upstream's verifier
--  compares with the circuit's (AttributeNumberMismatch), and so does
--  this layer (Mdoc_Status.Input_Count).
--
--  The witness of the hash circuit (block 6 builds it; this block reads
--  it from upstream's files) begins with the three values the tags
--  bind, as 32 little-endian bytes each, as bits (768 elements), and
--  ends with mac_ap, the six pads as elements: Witness_Parts reads both
--  ends. The witness of the signature circuit ends with, for each of
--  the three values, its two pads then the two halves of the value,
--  each 128-bit value as 64 elements of two bits, least significant
--  pair first, the element 2 v - 3 of the pair v (push_witness_sig,
--  push_plucked_128_legacy, lookup_point of the P-256 field). The pads
--  are one-time: a proof made with the pads of the file and a fresh
--  av, beside upstream's own proof under the same pads, would give the
--  bound values away (tag + tag' = (av + av') m). So a proof made from
--  the files draws fresh pads and places them in both witnesses
--  (Place_Pads), after checking that the file's pads are where the
--  layout says (Sig_Pads_Match).
--
--  Documentation: docs/guide/09-mdoc.md.
--
--  Proof status. Gold on the counts: Hash_Count is the closed formula
--  above, Hash_Inputs fills exactly that many elements and puts the
--  constant one first and the tags and av last at the stated positions;
--  Sig_Inputs the same for its first four elements; Place_Pads leaves
--  the pads where Witness_Parts and Sig_Pads_Match read them. Silver on
--  everything. That the bits are upstream's is tested: the harness
--  mdoc_kat compares the arrays with the Python transcription
--  (tests/vectors/mdoc_layer.txt) and with the public parts of
--  upstream's witness files.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE to the public
--  inputs, which are public. Witness_Parts, Sig_Pads_Match and
--  Place_Pads touch the witness, which is secret: they index on
--  constants, Witness_Parts accumulates each byte and the layout check
--  in masks over every element without a short circuit, Sig_Pads_Match
--  accumulates its 384 element comparisons in a mask (Diff: the limbs
--  xor-ed and or-ed, no record equality), and each has
--  one branch at the end, on the result of its layout check, as ADR
--  0051 admits for the prover's own checks.

pragma SPARK_Mode (On);

with Interfaces;  use Interfaces;
with Bytes;       use Bytes;
with GF2_128;
with P256_Field;
with Cbor_Encode;
with Mdoc_Mac;
with Mdoc_Spec;
with Sumcheck_Algebra_GF2_128;
with Sumcheck_Algebra_P256;

package Mdoc_Inputs is

   package SAH renames Sumcheck_Algebra_GF2_128;
   package SAP renames Sumcheck_Algebra_P256;

   use type GF2_128.Element;
   use type P256_Field.Element;

   subtype Version_Number is Mdoc_Spec.Version_Number;

   ----------------------------------------------------------------------
   --  The request: the attributes and the date
   ----------------------------------------------------------------------

   Max_Id_Len     : constant := 64;
   Max_Value_Len  : constant := 96;
   Max_Attributes : constant := 4;

   subtype Id_Length is Natural range 0 .. Max_Id_Len;
   subtype Value_Length is Natural range 0 .. Max_Value_Len;

   --  An attribute: its identifier (the bytes of the name, such as
   --  "age_over_18") and its value as the CBOR bytes the credential
   --  holds (F5 for true, 6A "Mustermann" for a text).
   type Attribute is record
      Id        : Byte_Array (0 .. Max_Id_Len - 1) := [others => 0];
      Id_Len    : Id_Length := 0;
      Value     : Byte_Array (0 .. Max_Value_Len - 1) := [others => 0];
      Value_Len : Value_Length := 0;
   end record;

   type Attribute_List is array (Positive range <>) of Attribute;

   --  The date as upstream takes it: at most 20 bytes.
   Now_Len : constant := 20;

   --  An attribute fits the layout of a version when its pieces fit
   --  the fixed buffers.
   function Fits (Version : Version_Number; A : Attribute) return Boolean is
     (if Version = 7 then
        Cbor_Encode.Head_Len (A.Id_Len) + A.Id_Len <= 32
        and then A.Value_Len <= 64
      else
        Cbor_Encode.Head_Len (A.Id_Len) + A.Id_Len + 13 + A.Value_Len <= 96)
   with Global => null;

   function All_Fit
     (Version : Version_Number; Attrs : Attribute_List) return Boolean
   is
     (for all K in Attrs'Range => Fits (Version, Attrs (K)))
   with Global => null;

   ----------------------------------------------------------------------
   --  The counts
   ----------------------------------------------------------------------

   --  The elements of one attribute: 256 + 512 + 8 + 8 at version 7,
   --  768 + 8 before.
   function Per_Attribute (Version : Version_Number) return Positive is
     (if Version = 7 then 784 else 776)
   with Global => null;

   --  The date's bits, the six tags, av.
   Tail_Count : constant := 8 * Now_Len + 6 + 1;

   function Hash_Count (Version : Version_Number; N : Natural) return Positive
   is
     (1 + N * Per_Attribute (Version) + Tail_Count)
   with Global => null, Pre => N <= Max_Attributes;

   Sig_Count : constant := 1 + 2 + 1 + 6 * 128 + 128;

   ----------------------------------------------------------------------
   --  The public inputs
   ----------------------------------------------------------------------

   procedure Hash_Inputs
     (Version : Version_Number;
      Attrs   : Attribute_List;
      Now     : Byte_Array;
      T       : Mdoc_Mac.Tags;
      Av      : GF2_128.Element;
      Pub     : out SAH.Element_Array)
   with
     Global => null,
     Pre    =>
       Attrs'Length <= Max_Attributes
       and then All_Fit (Version, Attrs)
       and then Now'Length <= Now_Len
       and then Pub'First = 0
       and then Pub'Length = Hash_Count (Version, Attrs'Length),
     Post   =>
       Pub (0) = SAH.One
       and then Pub (Pub'Last) = Av
       and then (for all I in Mdoc_Mac.Tag_Index =>
                   Pub (Pub'Last - 6 + I) = T (I));

   procedure Sig_Inputs
     (Pk_X, Pk_Y, E2 : P256_Field.Element;
      T              : Mdoc_Mac.Tags;
      Av             : GF2_128.Element;
      Pub            : out SAP.Element_Array)
   with
     Global => null,
     Pre    => Pub'First = 0 and then Pub'Length = Sig_Count,
     Post   =>
       Pub (0) = SAP.One and then Pub (1) = Pk_X and then Pub (2) = Pk_Y
       and then Pub (3) = E2;

   ----------------------------------------------------------------------
   --  The ends of the hash circuit's witness
   ----------------------------------------------------------------------

   --  The three messages as bits, 768 elements; the six pads.
   Message_Elements : constant := 3 * 32 * 8;
   Pad_Elements     : constant := 6;

   --  Ok when Priv holds both ends and the first 768 elements are
   --  bits; then Ap is the last six elements and M the three values.
   procedure Witness_Parts
     (Priv : SAH.Element_Array;
      Ap   : out Mdoc_Mac.Pads;
      M    : out Mdoc_Mac.Messages;
      Ok   : out Boolean)
   with
     Global => null,
     Pre    => Priv'First = 0,
     Post   =>
       (if Ok then
          Priv'Length >= Message_Elements + Pad_Elements
          and then (for all I in Mdoc_Mac.Message_Index =>
                      (for all H in Mdoc_Mac.Half_Index =>
                         Ap (I) (H) = Priv (Priv'Last - 5 + 2 * I + H))));

   --  The tail of the signature circuit's witness: three times two pads
   --  and two halves, 64 elements each.
   Sig_Tail_Elements : constant := 3 * 4 * 64;

   --  The element of a two-bit value: 2 v - 3 (lookup_point of P-256
   --  for the legacy plucker of width 2).
   function Plucked (V : Natural) return P256_Field.Element is
     (P256_Field.Sub (P256_Field.Of_Natural (2 * V),
                      P256_Field.Of_Natural (3)))
   with Global => null, Pre => V <= 3;

   --  Pair K of a 128-bit value, least significant first.
   function Pair (E : GF2_128.Element; K : Natural) return Natural is
     (Natural (Shift_Right (E.Limbs (GF2_128.Limb_Index (K / 32)),
                            2 * (K mod 32)) and 3))
   with Global => null, Pre => K <= 63, Post => Pair'Result <= 3;

   --  The position of element K of half H of message I in the tail.
   function Sig_Pad_Index
     (Sig_Priv : SAP.Element_Array; I, H, K : Natural) return Natural
   is
     (Sig_Priv'Length - Sig_Tail_Elements + 256 * I + 64 * H + K)
   with Global => null,
        Pre => Sig_Priv'First = 0
               and then Sig_Priv'Length >= Sig_Tail_Elements
               and then I <= 2 and then H <= 1 and then K <= 63;

   --  The limbs of two elements xor-ed and or-ed: zero exactly when the
   --  elements are equal, without a branch on either.
   function Diff (A, B : P256_Field.Element) return Unsigned_64 is
     ((A.L0 xor B.L0) or (A.L1 xor B.L1) or (A.L2 xor B.L2) or (A.L3 xor B.L3))
   with Global => null, Post => (Diff'Result = 0) = (A = B);

   --  The pads encoded at the end of Sig_Priv are Ap: every one of the
   --  384 elements compared, no short circuit.
   function Sig_Pads_Match
     (Sig_Priv : SAP.Element_Array; Ap : Mdoc_Mac.Pads) return Boolean
   with Global => null,
        Pre  => Sig_Priv'First = 0
                and then Sig_Priv'Length >= Sig_Tail_Elements,
        Post => Sig_Pads_Match'Result
                = (for all I in Mdoc_Mac.Message_Index =>
                     (for all H in Mdoc_Mac.Half_Index =>
                        (for all K in 0 .. 63 =>
                           Sig_Priv (Sig_Pad_Index (Sig_Priv, I, H, K))
                           = Plucked (Pair (Ap (I) (H), K)))));

   --  Ap written into both witnesses, in place of the pads they hold.
   procedure Place_Pads
     (Hash_Priv : in out SAH.Element_Array;
      Sig_Priv  : in out SAP.Element_Array;
      Ap        : Mdoc_Mac.Pads)
   with
     Global => null,
     Pre    =>
       Hash_Priv'First = 0
       and then Hash_Priv'Length >= Message_Elements + Pad_Elements
       and then Sig_Priv'First = 0
       and then Sig_Priv'Length >= Sig_Tail_Elements,
     Post   =>
       (for all I in Mdoc_Mac.Message_Index =>
          (for all H in Mdoc_Mac.Half_Index =>
             Hash_Priv (Hash_Priv'Last - 5 + 2 * I + H) = Ap (I) (H)))
       and then Sig_Pads_Match (Sig_Priv, Ap);

end Mdoc_Inputs;
