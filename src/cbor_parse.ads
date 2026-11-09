--  Cbor_Parse: a bounded parser for CBOR (RFC 8949), for the mDoc the
--  holder presents (Phase D, block 6, ADR 0086). It transcribes
--  upstream's parser, circuits/src/cbor/parse.rs at d5e6be7 (parse_exact):
--  the major types 0 to 7, lengths of 1, 2, 4 or 8 bytes (additional
--  information 24 to 27), indefinite lengths and the reserved values
--  28 to 31 refused, text strings that must be UTF-8, trailing bytes
--  refused. Nothing else: no canonical order, no duplicate keys at this
--  level (Mdoc_Parse checks the keys it looks up).
--
--  Where upstream recurses into a tree on the heap, this parser walks
--  the bytes once with an explicit stack of Max_Depth frames and fills
--  a table of at most Max_Elements elements: the kind, the byte range
--  (Start, the first byte after the head, Stop), the argument of the
--  head, the parent, the first child and the next sibling. Positions
--  are relative to the first index of the parsed array, so that the
--  same table serves a slice of the document (the wrapped MSO, an
--  item) as well as the document itself. The bounds (ADR 0086): a
--  document of at most Max_Bytes, a depth of Max_Depth, Max_Elements
--  elements; an excess is a status, never a truncation.
--
--  Documentation: docs/guide/09-mdoc.md, Section 3.6.
--
--  Proof status (Silver = absence of run-time errors, Gold = proved
--  functional contracts).
--
--    Parse_Exact : Silver on any bytes; Gold on the invariants of the
--                  table (Valid): every element's range lies inside
--                  the parsed bytes, every child lies inside its
--                  parent, the links point forward within the table.
--                  That the table is the CBOR structure of the bytes
--                  is tested, against a Python transcription and on
--                  upstream's 38 test documents (mdoc_parse_kat).
--    The accessors: Silver; their results are elements of the table
--                  or zero.
--
--  Constant time: NOT constant time, declared (ADR 0086): a parser of
--  a variable-length document indexes on the lengths and positions it
--  finds, as upstream's does, and the UTF-8 check of every text string
--  (Is_Utf8) branches on the bytes of the text, so its timing depends
--  on the text values of the document (an identifier, a text value of
--  an item) as well as on its structure. What it reveals, it reveals
--  to an observer on the holder's own device, about the holder's own
--  credential; the signatures and the digests are copied by length.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Bytes;      use Bytes;

package Cbor_Parse is

   Max_Bytes    : constant := 262_144;
   Max_Depth    : constant := 16;
   Max_Elements : constant := 4_096;

   --  A position in the parsed bytes, relative to their first index;
   --  Max_Bytes itself is the position one past the last byte.
   subtype Position is Natural range 0 .. Max_Bytes;

   subtype Element_Count is Natural range 0 .. Max_Elements;
   subtype Element_Index is Element_Count range 1 .. Max_Elements;

   type Kind is
     (Unsigned_Int,   --  major type 0: Value is the integer
      Negative_Int,   --  major type 1: the integer is -1 - Value
      Byte_String,    --  major type 2: Value is the length
      Text_String,    --  major type 3: Value is the length, UTF-8
      Array_Kind,     --  major type 4: Value is the number of items
      Map_Kind,       --  major type 5: Value is the number of pairs
      Tag,            --  major type 6: Value is the tag number
      Simple,         --  major type 7, information 0 .. 24
      Float_16,       --  major type 7, information 25: the bits
      Float_32,       --  26
      Float_64);      --  27

   type Element is record
      Kind    : Cbor_Parse.Kind := Unsigned_Int;
      Start   : Position := 0;      --  the first byte of the head
      Content : Position := 0;      --  the first byte after the head
      Stop    : Position := 0;      --  one past the last byte
      Value   : Unsigned_64 := 0;   --  the argument of the head
      Count   : Natural := 0;       --  children: items, 2 * pairs, 1
      Parent  : Element_Count := 0; --  0 for the root
      Child   : Element_Count := 0; --  the first child, or 0
      Next    : Element_Count := 0; --  the next sibling, or 0
   end record;

   type Element_Table is array (Element_Index) of Element;

   --  The parsed structure: Elements (1 .. Count), the root at 1, and
   --  Length, the number of bytes parsed.
   type Document is record
      Length   : Position := 0;
      Count    : Element_Count := 0;
      Elements : Element_Table := [others => <>];
   end record;

   --  The invariants of a complete table: ranges inside the bytes,
   --  the head (at least one byte) before the content, children inside
   --  their parent, the links forward (a child or a sibling comes later
   --  in the table; a child's parent is the element, a sibling's parent
   --  the same, and a sibling starts where the element ended or later),
   --  the root and only the root without a parent.
   function Valid (Doc : Document) return Boolean is
     (for all I in 1 .. Doc.Count =>
        Doc.Elements (I).Start < Doc.Elements (I).Content
        and then Doc.Elements (I).Content <= Doc.Elements (I).Stop
        and then Doc.Elements (I).Stop <= Doc.Length
        and then Doc.Elements (I).Child <= Doc.Count
        and then Doc.Elements (I).Next <= Doc.Count
        and then (Doc.Elements (I).Child = 0
                  or else (Doc.Elements (I).Child > I
                           and then Doc.Elements (Doc.Elements (I).Child).Parent = I))
        and then (Doc.Elements (I).Next = 0
                  or else (Doc.Elements (I).Next > I
                           and then Doc.Elements (Doc.Elements (I).Next).Parent
                                    = Doc.Elements (I).Parent
                           and then Doc.Elements (Doc.Elements (I).Next).Start
                                    >= Doc.Elements (I).Stop))
        and then Doc.Elements (I).Parent < I
        and then (Doc.Elements (I).Parent = 0) = (I = 1)
        and then (if Doc.Elements (I).Parent > 0 then
                    Doc.Elements (Doc.Elements (I).Parent).Content
                      <= Doc.Elements (I).Start
                    and then Doc.Elements (I).Stop
                      <= Doc.Elements (Doc.Elements (I).Parent).Stop))
   with Ghost, Global => null;

   type Status is
     (Ok,
      Truncated,          --  the bytes end inside a head or a string
      Reserved_Info,      --  additional information 28 .. 31, which
                          --  covers indefinite lengths (31)
      Length_Too_Large,   --  a length or a count beyond the bounds
      Not_Utf8,           --  a text string that is not UTF-8
      Trailing_Bytes,     --  bytes after the first complete item
      Too_Deep,           --  nesting beyond Max_Depth
      Too_Many_Elements); --  more than Max_Elements elements

   --  One complete item over all of Data, as upstream's parse_exact.
   --  On Ok the table is Valid and holds at least the root; otherwise
   --  Result says why and the table is not to be read.
   procedure Parse_Exact
     (Data   : Byte_Array;
      Doc    : out Document;
      Result : out Status)
   with
     Global => null,
     Pre    => Data'Length <= Max_Bytes,
     Post   => (if Result = Ok then
                  Doc.Count >= 1
                  and then Doc.Length = Data'Length
                  and then Valid (Doc));

   --  The accessors read a Valid table of Data, the array it was parsed
   --  from (the same length; positions are relative to Data'First).

   --  The I-th item of the array A (I from 0), or 0 if there is none.
   function Array_Item
     (Doc : Document; A : Element_Index; I : Natural) return Element_Count
   with
     Global => null,
     Pre    => Valid (Doc) and then A <= Doc.Count,
     Post   => Array_Item'Result <= Doc.Count
               and then (if Array_Item'Result > 0 then
                           Doc.Elements (Array_Item'Result).Parent = A);

   --  Whether the text string E spells S (bytes equal to the characters).
   function Text_Equals
     (Doc : Document; Data : Byte_Array; E : Element_Index; S : String)
      return Boolean
   with
     Global => null,
     Pre    => Valid (Doc) and then E <= Doc.Count
               and then Data'Length = Doc.Length;

   --  Whether the byte string or text string E has the same bytes as B.
   function Bytes_Equal
     (Doc : Document; Data : Byte_Array; E : Element_Index; B : Byte_Array)
      return Boolean
   with
     Global => null,
     Pre    => Valid (Doc) and then E <= Doc.Count
               and then Data'Length = Doc.Length;

   type Lookup is (Found, Missing, Duplicate, Not_A_Map);

   --  The unique entry of the map M whose key is the text Key
   --  (upstream's map_entry_unique): the key and value elements when
   --  Found; Duplicate if two keys spell Key; Not_A_Map if M is not a
   --  map. A key of another kind never matches.
   procedure Map_Text_Entry
     (Doc    : Document;
      Data   : Byte_Array;
      M      : Element_Index;
      Key    : String;
      Key_El : out Element_Count;
      Val_El : out Element_Count;
      Result : out Lookup)
   with
     Global => null,
     Pre    => Valid (Doc) and then M <= Doc.Count
               and then Data'Length = Doc.Length,
     Post   => Key_El <= Doc.Count and then Val_El <= Doc.Count
               and then (if Result = Found then
                           Key_El > 0 and then Val_El > 0
                           and then Doc.Elements (Key_El).Parent = M
                           and then Doc.Elements (Val_El).Parent = M);

   --  The same with the key given as bytes (a text key of another
   --  table, for instance): a text key whose bytes equal Key.
   procedure Map_Bytes_Entry
     (Doc    : Document;
      Data   : Byte_Array;
      M      : Element_Index;
      Key    : Byte_Array;
      Key_El : out Element_Count;
      Val_El : out Element_Count;
      Result : out Lookup)
   with
     Global => null,
     Pre    => Valid (Doc) and then M <= Doc.Count
               and then Data'Length = Doc.Length,
     Post   => Key_El <= Doc.Count and then Val_El <= Doc.Count
               and then (if Result = Found then
                           Key_El > 0 and then Val_El > 0
                           and then Doc.Elements (Key_El).Parent = M
                           and then Doc.Elements (Val_El).Parent = M);

   --  The same for an integer key: the integer Magnitude when Negative
   --  is False, -1 - Magnitude when it is True (the key -2 is Negative
   --  with Magnitude 1).
   procedure Map_Int_Entry
     (Doc       : Document;
      M         : Element_Index;
      Negative  : Boolean;
      Magnitude : Unsigned_64;
      Key_El    : out Element_Count;
      Val_El    : out Element_Count;
      Result    : out Lookup)
   with
     Global => null,
     Pre    => Valid (Doc) and then M <= Doc.Count,
     Post   => Key_El <= Doc.Count and then Val_El <= Doc.Count
               and then (if Result = Found then
                           Key_El > 0 and then Val_El > 0
                           and then Doc.Elements (Key_El).Parent = M
                           and then Doc.Elements (Val_El).Parent = M);

   --  The content of the tag E when it carries the number N, or 0.
   function Tag_Child
     (Doc : Document; E : Element_Index; N : Unsigned_64) return Element_Count
   with
     Global => null,
     Pre    => Valid (Doc) and then E <= Doc.Count,
     Post   => Tag_Child'Result <= Doc.Count
               and then (if Tag_Child'Result > 0 then
                           Doc.Elements (Tag_Child'Result).Parent = E);

end Cbor_Parse;
