--  Mdoc_Relation.Hash.Conditions: the conditions under which the
--  relation of the hash circuit is read as a statement about a
--  credential (ADR 0091; the conditions table of chapter 10). The
--  checker's theorem needs none of them: an evaluation of the circuit
--  that accepts implies Hash_Relation, unconditionally. They are what
--  an evaluator adds to go from the relation, which speaks of bytes at
--  offsets the prover chose, to the credential the issuer signed.
--
--  Three kinds, by their prefix:
--
--    H_    a hypothesis on the issuer, the relying party or SHA-256:
--          not something the circuit or this project can establish;
--    Fact_ a fact about the circuit, proved here or by the checker;
--    Limit_ a known limit of the circuit, stated, not assumed.
--
--  The model. No proved model of the MSO's CBOR structure exists: the
--  parse (Mdoc_Parse, over the table of Cbor_Parse) is proved safe and
--  in bounds, and what it extracts, and where, is trusted as upstream's
--  code specifies it (register row R12). The hypotheses are predicates
--  over the parse's outputs, the offsets of Parsed_Mdoc and the item's
--  locator: those outputs are the model, by name. So the meaning of a
--  hypothesis rests on R12, and a second theorem, if block 5 decides
--  for one, would rest on it too.
--
--  The hypotheses that are predicates are executable: the harness
--  relation_cases evaluates them on the test documents, and the lint
--  for issuers of block 5 is a program around them. H_Sha256,
--  H_Digest_Preimage and H_Now_Form are not predicates over a
--  document; they are stated below as text.
--
--  Documentation: docs/guide/10-certified-circuits.md, Section 1.
--
--  Proof status (Silver = absence of run-time errors, Gold = proved
--  functional contracts).
--
--    The predicates : Silver, for any input of the stated bounds.
--    Fact_Padding   : Gold, for every pattern of the clauses but the
--                     digest's.
--
--  Constant time: NOT APPLICABLE. Ghost, never compiled into the
--  library.
--
--  ----------------------------------------------------------------------
--  H_Sha256 (soundness, on SHA-256; register family S, cited from R2)
--  ----------------------------------------------------------------------
--
--  What the circuit checks: the compression function iterated from the
--  initial value over the blocks the prover supplies gives e (the
--  clause Chain), and over the item's two blocks gives the 32 bytes at
--  the digest's index (the clause Value_Digest). The blocks are not
--  checked to be a padded message: the circuit reads no padding.
--
--  The premise, in two parts: no one can find a sequence of blocks,
--  other than the padded message the issuer signed, whose chain from
--  the initial value gives the same e; nor two blocks, other than an
--  item the issuer hashed, whose chain gives one of the issuer's value
--  digests. Both are second-preimage resistance of the iterated
--  compression, which follows from the collision resistance of the
--  compression function together with the infeasibility of reaching
--  the initial value as a chaining value (what the length in the
--  padding otherwise provides).
--
--  ----------------------------------------------------------------------
--  H_Digest_Preimage (soundness, on SHA-256 and on P-256)
--  ----------------------------------------------------------------------
--
--  What the circuit checks: the clause Value_Digest takes as the value
--  digest any byte string 58 20 and its 32 bytes in the signed
--  message, at the index the prover chooses. Such a string can occur
--  outside valueDigests, and two cases differ by who wrote it:
--
--    - Bytes the issuer chose: the other entries of the MSO, and two
--      random bytes of a digest, which are 58 20 once in 65,536. They
--      are the matter of H_Matching_By_Content, whose row of the
--      conditions table already names "a digest outside valueDigests".
--    - The device key's coordinates x and y, which have that head: the
--      holder chose the key before issuance, and the issuer signs it.
--      To use a coordinate as a value digest, a prover needs either
--      two blocks whose chain from the initial value is that
--      coordinate, a preimage of SHA-256's iterated compression; or a
--      key whose coordinate is a digest of its choosing and whose
--      private key it knows, a discrete logarithm on P-256.
--
--  The premise: both are infeasible. The first is preimage resistance,
--  a different premise from H_Sha256's second-preimage resistance;
--  the second is the hardness of the discrete logarithm on P-256,
--  which the device signature already rests on.
--
--  ----------------------------------------------------------------------
--  H_Now_Form (soundness, relying party)
--  ----------------------------------------------------------------------
--
--  The 20 bytes of now are the relying party's current time in the form
--  YYYY-MM-DDThh:mm:ssZ, upper-case T and Z. The clauses Valid_From and
--  Valid_Until compare bytes; their reading as times holds for that
--  form on both sides. Limit_Date_Separators is the same form on the
--  issuer's side, which the builder checks for this project's prover
--  (Validity_Form_Unsupported).

pragma SPARK_Mode (On);

with Mdoc_Parse;

package Mdoc_Relation.Hash.Conditions is

   ----------------------------------------------------------------------
   --  Occurrences of a pattern in the MSO map
   ----------------------------------------------------------------------

   --  The MSO map: the bytes the circuit's index 0 points at (the map
   --  that follows D8 18 59 and its two bytes of length), as the parse
   --  places them. At most the 2,533 bytes the windows cover.
   function Map_Ok (Map : Byte_Array) return Boolean is
     (Map'First = 0 and then Map'Length <= Max_Mso_Len)
   with Global => null;

   --  The pattern occurs at K, inside the map.
   function Occurs (Map : Byte_Array; K : Natural; Pattern : Byte_Array)
     return Boolean
   is
     (K <= Map'Length
      and then Pattern'Length <= Map'Length - K
      and then
        (for all I in 0 .. Pattern'Length - 1 =>
           Map (K + I) = Pattern (Pattern'First + I)))
   with Global => null,
        Pre => Map_Ok (Map) and then Pattern'Length <= 100;

   --  The pattern occurs nowhere in the map but at K.
   function Only_At (Map : Byte_Array; Pattern : Byte_Array; K : Natural)
     return Boolean
   is
     (for all J in 0 .. Map'Length - 1 =>
        (if Occurs (Map, J, Pattern) then J = K))
   with Global => null,
        Pre => Map_Ok (Map) and then Pattern'Length <= 100;

   --  58 20 and the digest: the 34 bytes the clause Value_Digest reads.
   subtype Digest_Pattern_Array is Byte_Array (0 .. 33);

   function Digest_Pattern (D : Bytes_32) return Digest_Pattern_Array is
     ([for I in 0 .. 33 => (if I < 2 then Digest_Head (I) else D (I - 2))])
   with Global => null;

   ----------------------------------------------------------------------
   --  H_Matching_By_Content (soundness, issuer)
   ----------------------------------------------------------------------

   --  Each pattern the clauses search for occurs in the MSO map only
   --  where the structure puts it, as the parse found it: the keys of
   --  validFrom and validUntil with their tag 0 and head, deviceKeyInfo
   --  with its COSE_Key up to x's head, valueDigests, and 58 20 with the
   --  requested item's digest D at that item's entry of valueDigests.
   --  With the relation, it makes every index of the witness the
   --  parse's offset. An occurrence that runs past the map's end into
   --  the padding is Fact_Padding's, not this hypothesis's.
   function H_Matching_By_Content
     (Map : Byte_Array;
      P   : Mdoc_Parse.Parsed_Mdoc;
      It  : Mdoc_Parse.Item;
      D   : Bytes_32) return Boolean
   is
     (Only_At (Map, Valid_From_Key, P.Valid_From_Offset)
      and then Only_At (Map, Valid_Until_Key, P.Valid_Until_Offset)
      and then Only_At (Map, Device_Key_Key, P.Device_Key_Info_Offset)
      and then Only_At (Map, Value_Digests_Key, P.Value_Digests_Offset)
      and then Only_At (Map, Digest_Pattern (D), It.Digest_Offset))
   with Global => null, Pre => Map_Ok (Map);

   ----------------------------------------------------------------------
   --  H_Types_In_Item (soundness, issuer)
   ----------------------------------------------------------------------

   --  The slot the parse's permutation gives a field (the same packing
   --  as the witness's perm: two bits per field, digestID lowest).
   function Parse_Slot (It : Mdoc_Parse.Item; F : Field)
     return Mdoc_Parse.Slot_Index
   is
     (Mdoc_Parse.Slot_Index ((It.Permutation / 4 ** F) mod 4))
   with Global => null;

   --  The byte at Offset into the field's entry, or None when the entry
   --  does not reach it.
   None : constant := 256;

   function Entry_Byte
     (Item_Bytes : Byte_Array; It : Mdoc_Parse.Item; F : Field;
      Offset     : Natural) return Natural
   is
     (if It.Slot (Parse_Slot (It, F)) < Item_Bytes'Length
        and then Offset < Item_Bytes'Length - It.Slot (Parse_Slot (It, F))
      then Natural (Item_Bytes (It.Slot (Parse_Slot (It, F)) + Offset))
      else None)
   with Global => null,
        Pre => Item_Bytes'First = 0 and then Offset <= 9;

   --  digestID is an unsigned integer and random a byte string: the
   --  major types of the heads at bytes 9 and 7 of their entries, which
   --  the circuit does not read (Cbor_Length_Ok). The parse already
   --  refuses a digestID of another type (Invalid_Value,
   --  Unexpected_Type); it does not look at random's.
   function H_Types_In_Item
     (Item_Bytes : Byte_Array; It : Mdoc_Parse.Item) return Boolean
   is
     (Entry_Byte (Item_Bytes, It, Digest_Id_Field, 9) / 32 = 0
      and then Entry_Byte (Item_Bytes, It, Random_Field, 7) / 32 = 2)
   with Global => null, Pre => Item_Bytes'First = 0;

   ----------------------------------------------------------------------
   --  Fact_Padding (soundness, circuit)
   ----------------------------------------------------------------------

   --  The preimage from byte N on is the SHA-256 padding of a message
   --  of N bytes: 16#80#, zeros, the bit length in the last eight bytes
   --  of block nb (big-endian; below 2^15 bits, so six zero bytes and
   --  two), then the zero blocks. Under H_Sha256 the blocks the circuit
   --  hashed are the issuer's padded message, so this holds with N the
   --  length of the message the issuer signed.
   subtype Message_Length is Natural range 25 .. 64 * Max_Blocks - 9;

   function Padded_From (V : Private_Part; N : Message_Length) return Boolean
   is
     (V.Count in 1 .. Max_Blocks
      and then N + 9 <= 64 * Natural (V.Count)
      and then 64 * Natural (V.Count) < N + 9 + 64
      and then Preimage_Byte (V, N) = 16#80#
      and then
        (for all I in N + 1 .. 64 * Natural (V.Count) - 3 =>
           Preimage_Byte (V, I) = 0)
      and then Preimage_Byte (V, 64 * Natural (V.Count) - 2)
               = Unsigned_8 ((8 * N) / 256)
      and then Preimage_Byte (V, 64 * Natural (V.Count) - 1)
               = Unsigned_8 ((8 * N) mod 256)
      and then Zero_Tail (V))
   with Global => null;

   --  A pattern the padding cannot hold: no byte 0 or 16#80#, and a
   --  first byte that is neither the high byte of a bit length (below
   --  16#50#) nor its low byte (a multiple of 8).
   function Padding_Safe (Pattern : Byte_Array) return Boolean is
     (Pattern'Length >= 1
      and then
        (for all I in Pattern'Range =>
           Pattern (I) /= 0 and then Pattern (I) /= 16#80#)
      and then Pattern (Pattern'First) >= 16#50#
      and then Pattern (Pattern'First) mod 8 /= 0)
   with Global => null;

   --  A pattern of the clauses matches only inside the message: every
   --  byte of the window lies before N. The keys of validFrom,
   --  validUntil, deviceKeyInfo and valueDigests, and the key of y at
   --  65 bytes into the device key's window. Not the digest's 58 20
   --  and 32 bytes: the digest may hold any byte, and a window that
   --  reaches into the padding holds bytes no one chose, a preimage
   --  (H_Digest_Preimage).
   procedure Fact_Padding
     (V : Private_Part; N : Message_Length; K : Index_12)
   with
     Global => null,
     Pre    => Padded_From (V, N),
     Post   =>
       (if Matches (V, K, 0, Valid_From_Key)
        then 25 + K + Valid_From_Key'Length <= N)
       and then (if Matches (V, K, 0, Valid_Until_Key)
                 then 25 + K + Valid_Until_Key'Length <= N)
       and then (if Matches (V, K, 0, Device_Key_Key)
                 then 25 + K + Device_Key_Key'Length <= N)
       and then (if Matches (V, K, 0, Value_Digests_Key)
                 then 25 + K + Value_Digests_Key'Length <= N)
       and then (if Matches (V, K, 65, Device_Key_Y_Key)
                 then 25 + K + 65 + Device_Key_Y_Key'Length <= N);

end Mdoc_Relation.Hash.Conditions;
