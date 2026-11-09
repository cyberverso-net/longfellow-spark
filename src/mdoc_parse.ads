--  Mdoc_Parse: the walk of the mDoc that upstream's parse_mdoc makes
--  (circuits/src/cbor/mdoc.rs at d5e6be7), over the table of
--  Cbor_Parse (Phase D, block 6, ADR 0086). From the document the
--  holder presents it reads what the two circuits need:
--
--    - documents[0].issuerSigned.issuerAuth, a COSE_Sign1 array (tag
--      18 or not): its third element is the wrapped MSO (tag 24 over
--      a byte string, the only encoding the circuits accept:
--      validate_mso_layout), its fourth the issuer's signature, 64
--      bytes r then s; the digest the issuer signed is the SHA-256 of
--      the signed message, format_cose_sign1_message (the fixed COSE
--      header, the byte-string head of the wrapped MSO, the MSO);
--    - in the MSO map: the device key (deviceKeyInfo.deviceKey, the
--      COSE_Key integers -2 and -3 as byte strings, big-endian), and
--      the positions of the keys docType, validityInfo.validFrom,
--      validityInfo.validUntil, deviceKeyInfo and valueDigests, which
--      the circuit receives as offsets into the MSO;
--    - documents[0].deviceSigned.deviceAuth.deviceSignature, a
--      COSE_Sign1 array whose fourth element is the device's signature;
--      the digest it signed is Device_Auth.Digest of the session
--      transcript and the document type (block 5);
--    - the issuer-signed items of issuerSigned.nameSpaces: per item its
--      wrapped bytes (tag 24, head and map), the identifier, the value,
--      the locator of its four entries (digestID, random,
--      elementIdentifier, elementValue, in any order: the position and
--      length of each, the permutation of the slots) and the position,
--      in the MSO, of its digest under valueDigests.
--
--  Unique keys are enforced where upstream enforces them
--  (map_entry_unique): a second "documents", "issuerSigned", a second
--  namespace, a fifth entry of an item are errors. The results are
--  positions in the document (relative to its first index) and the
--  fixed-size values; nothing of variable length is copied, so the
--  record is bounded by Max_Items items. The bounds (ADR 0086): the
--  wrapped MSO at most Max_Wrapped_Mso (Version) bytes, the SHA-256
--  capacity of the hash circuit less the prefix, the head and the
--  padding (2,531 for version 7, 2,211 for version 6), and a map of at
--  least 256 bytes; at most Max_Items items. An excess is a status.
--
--  Documentation: docs/guide/09-mdoc.md, Section 3.6.
--
--  Proof status (Silver = absence of run-time errors, Gold = proved
--  functional contracts).
--
--    Parse        : Silver on any document; Gold on the ranges of the
--                   result lying inside the document and the MSO
--                   (the postcondition). That the values are upstream's
--                   is tested: against a Python transcription on the
--                   38 test documents, and against the front of the
--                   hash witness files of both archives
--                   (mdoc_parse_kat).
--    Signed_Message, Find_Item : Silver.
--
--  Constant time: NOT constant time, declared (ADR 0086), as
--  Cbor_Parse, whose UTF-8 check reads the bytes of every text; the
--  walk itself compares keys of public text and copies the signatures,
--  the coordinates and the digests by length.

pragma SPARK_Mode (On);

with Interfaces;   use Interfaces;
with Bytes;        use Bytes;
with Cbor_Parse;
with Device_Auth;
with Mdoc_Spec;

package Mdoc_Parse is

   subtype Version_Number is Mdoc_Spec.Version_Number;
   subtype Position is Cbor_Parse.Position;

   --  The SHA-256 capacity of the hash circuit, in blocks, and the
   --  longest wrapped MSO it leaves room for: the padded message is
   --  the 18-byte COSE prefix (the signing header and the byte-string
   --  marker 16#59#), the two bytes of length, the wrapped MSO, the
   --  byte 16#80# and the eight bytes of length.
   function Max_Blocks (V : Version_Number) return Positive is
     (if V = 6 then 35 else 40)
   with Global => null, Pre => V in 6 .. 7;

   Cose_Prefix_Len : constant := 18;

   function Max_Wrapped_Mso (V : Version_Number) return Positive is
     (64 * Max_Blocks (V) - 9 - Cose_Prefix_Len - 2)
   with Global => null, Pre => V in 6 .. 7;

   Min_Mso_Map : constant := 256;
   Max_Items   : constant := 256;
   subtype Item_Count is Natural range 0 .. Max_Items;
   subtype Item_Index is Item_Count range 1 .. Max_Items;

   --  The outcomes, upstream's MdocParseError kind by kind: the four
   --  places where its CBOR parser fails (the context of its Cbor
   --  error, with the parser's status in Cbor_Detail), then the
   --  errors of the walk. Too_Many_Items and Document_Too_Long are this
   --  project's bounds (ADR 0086).
   type Status is
     (Ok,
      Cbor_Root,             --  the document is not one CBOR item
      Cbor_Mso_Wrapper,      --  the wrapped MSO is not one CBOR item
      Cbor_Mso_Map,          --  the MSO map is not one CBOR item
      Cbor_Item,             --  an issuer-signed item's map is not
      Missing_Field,
      Duplicate_Field,
      Unexpected_Type,
      Invalid_Length,        --  a signature not of 64 bytes, an item
                             --  not of four entries
      Invalid_Value,         --  the MSO not under tag 24, a negative
                             --  digestID
      Unknown_Field,         --  a fifth kind of key in an item
      Unsupported_Encoding,  --  the MSO layout validate_mso_layout
                             --  refuses
      Too_Big,               --  the MSO beyond the SHA-256 capacity
      Too_Many_Items,        --  more than Max_Items issuer-signed items
      Document_Too_Long);    --  more than Cbor_Parse.Max_Bytes bytes

   type Slot_Index is range 0 .. 3;
   type Slot_Positions is array (Slot_Index) of Position;

   --  One issuer-signed item (upstream's ParsedAttr, by positions in
   --  the document): the identifier's text, the value's CBOR, the
   --  wrapped item; the locator (slot_position, length, permutation of
   --  mso_attribute's FieldLocator); the position in the MSO map of
   --  the digest under valueDigests; the digestID.
   type Item is record
      Name_Start   : Position := 0;
      Name_Len     : Position := 0;
      Value_Start  : Position := 0;
      Value_Len    : Position := 0;
      Item_Start   : Position := 0;
      Item_Len     : Position := 0;
      Slot         : Slot_Positions := [others => 0];
      Length       : Slot_Positions := [others => 0];
      Permutation  : Natural := 0;
      Digest_Offset : Position := 0;
      Digest_Id    : Unsigned_64 := 0;
   end record;

   type Item_Table is array (Item_Index) of Item;

   --  Upstream's ParsedMdoc: the seven 256-bit values as big-endian
   --  bytes (the digests as SHA-256 writes them, the signature values
   --  as the document carries them, the coordinates as upstream's
   --  from_bytes_be reads them: left-padded when shorter than 32
   --  bytes, the last 32 bytes when longer), the wrapped MSO as a
   --  range of the document, the
   --  five offsets into the MSO map, the items.
   type Parsed_Mdoc is record
      Issuer_Sig_Digest : Bytes_32 := [others => 0];
      Issuer_Sig_R      : Bytes_32 := [others => 0];
      Issuer_Sig_S      : Bytes_32 := [others => 0];
      Device_Pk_X       : Bytes_32 := [others => 0];
      Device_Pk_Y       : Bytes_32 := [others => 0];
      Device_Sig_Digest : Bytes_32 := [others => 0];
      Device_Sig_R      : Bytes_32 := [others => 0];
      Device_Sig_S      : Bytes_32 := [others => 0];
      Mso_Start         : Position := 0;  --  the wrapped MSO
      Mso_Len           : Position := 0;
      Doc_Type_Offset   : Position := 0;  --  in the MSO map bytes
      Valid_From_Offset : Position := 0;
      Valid_Until_Offset : Position := 0;
      Device_Key_Info_Offset : Position := 0;
      Value_Digests_Offset : Position := 0;
      Count             : Item_Count := 0;
      Items             : Item_Table := [others => <>];
   end record;

   --  The MSO map bytes start five bytes into the wrapped MSO (tag 24,
   --  two bytes; the byte-string head 16#59# and two bytes of length).
   Mso_Head_Len : constant := 5;

   --  The ranges of a result lie inside the document and the MSO: the
   --  MSO and the five offsets (Head_In_Bounds), then every item.
   function Head_In_Bounds (P : Parsed_Mdoc; Length : Position)
     return Boolean
   is
     (P.Mso_Len >= Mso_Head_Len + Min_Mso_Map
      and then P.Mso_Start + P.Mso_Len <= Length
      and then P.Doc_Type_Offset < P.Mso_Len - Mso_Head_Len
      and then P.Valid_From_Offset < P.Mso_Len - Mso_Head_Len
      and then P.Valid_Until_Offset < P.Mso_Len - Mso_Head_Len
      and then P.Device_Key_Info_Offset < P.Mso_Len - Mso_Head_Len
      and then P.Value_Digests_Offset < P.Mso_Len - Mso_Head_Len)
   with Ghost, Global => null;

   function Item_In_Bounds (It : Item; Mso_Len, Length : Position)
     return Boolean
   is
     (It.Name_Start + It.Name_Len <= Length
      and then It.Value_Start + It.Value_Len <= Length
      and then It.Item_Start + It.Item_Len <= Length
      and then It.Digest_Offset < Mso_Len - Mso_Head_Len)
   with Ghost, Global => null, Pre => Mso_Len >= Mso_Head_Len;

   function Items_In_Bounds (P : Parsed_Mdoc; Length : Position)
     return Boolean
   is
     (for all I in 1 .. P.Count =>
        Item_In_Bounds (P.Items (I), P.Mso_Len, Length))
   with Ghost, Global => null, Pre => P.Mso_Len >= Mso_Head_Len;

   function In_Bounds (P : Parsed_Mdoc; Length : Position) return Boolean is
     (Head_In_Bounds (P, Length) and then Items_In_Bounds (P, Length))
   with Ghost, Global => null;

   procedure Parse
     (Mdoc        : Byte_Array;
      Transcript  : Byte_Array;
      Doc_Type    : Byte_Array;
      Version     : Version_Number;
      P           : out Parsed_Mdoc;
      Result      : out Status;
      Cbor_Detail : out Cbor_Parse.Status)
   with
     Global => null,
     Pre    => Transcript'Length <= Device_Auth.Max_Session_Transcript
               and then Doc_Type'Length <= Device_Auth.Max_Doc_Type
               and then Version in 6 .. 7,
     Post   => (if Result = Ok then
                  Mdoc'Length <= Cbor_Parse.Max_Bytes
                  and then In_Bounds (P, Mdoc'Length)
                  and then P.Mso_Len <= Max_Wrapped_Mso (Version));

   --  The signed message of the issuer (format_cose_sign1_message):
   --  the 17-byte signing header, the byte-string head of the wrapped
   --  MSO (three bytes, since the map has at least 256 bytes and the
   --  whole at most 65,535), the wrapped MSO. Its length is at most
   --  64 * Max_Blocks (Version) - 9, so that it pads into the blocks.
   Signing_Header_Len : constant := 17;
   Max_Message        : constant := 64 * 40 - 9;

   function Message_Length (P : Parsed_Mdoc) return Natural is
     (Signing_Header_Len + 3 + P.Mso_Len)
   with Global => null;

   procedure Signed_Message
     (Mdoc : Byte_Array;
      P    : Parsed_Mdoc;
      Msg  : out Byte_Array;
      Len  : out Natural)
   with
     Global => null,
     Pre    => Mdoc'Length <= Cbor_Parse.Max_Bytes
               and then In_Bounds (P, Mdoc'Length)
               and then P.Mso_Len <= 65_535
               and then Msg'First = 0 and then Msg'Length >= Max_Message
               and then Message_Length (P) <= Max_Message,
     Post   => Len = Message_Length (P);

   --  The item whose identifier is Id (upstream's get_attribute), or 0.
   function Find_Item
     (Mdoc : Byte_Array; P : Parsed_Mdoc; Id : Byte_Array) return Item_Count
   with
     Global => null,
     Pre    => Mdoc'Length <= Cbor_Parse.Max_Bytes
               and then In_Bounds (P, Mdoc'Length),
     Post   => Find_Item'Result <= P.Count;

end Mdoc_Parse;
