--  Cbor_Encode: the head of a CBOR text string or byte string (RFC
--  8949, Section 3), as upstream's mDoc application writes it
--  (longfellow-zk/longfellow-zk d5e6be7, rust/applications/mdoc_zk/
--  circuits/src/cbor/cbor_encode.rs, append_len): the major type in
--  the high three bits, then the length itself when it is below 24,
--  or the additional-information value 24, 25 or 26 followed by the
--  length in one, two or four big-endian bytes. The mDoc layer uses it
--  twice (Phase D, block 5, ADR 0058): for the identifier of an
--  attribute among the public inputs of the hash circuit, encoded as
--  a text string (Mdoc_Inputs), and for the byte strings and the
--  document type inside the device authentication structure
--  (Device_Auth). Lengths above 2^32 - 1 do not occur; Natural is
--  below that bound on every target of the project.
--
--  Documentation: docs/guide/09-mdoc.md.
--
--  Proof status. Gold: Head_Len is the length of the head by the
--  cases of the standard, and Head returns exactly those bytes, the
--  postcondition spelling each byte out. Silver on everything.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE. The lengths
--  encoded are public: the requested attribute, the document type and
--  the session transcript are the relying party's data.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Bytes;      use Bytes;

package Cbor_Encode is

   --  Major type 3 (text string) and major type 2 (byte string), as
   --  the high bits of the initial byte.
   Text_Major  : constant Unsigned_8 := 16#60#;
   Bytes_Major : constant Unsigned_8 := 16#40#;

   --  The bytes of the head of a string of N bytes.
   function Head_Len (N : Natural) return Positive is
     (if N <= 23 then 1
      elsif N <= 255 then 2
      elsif N <= 65535 then 3
      else 5)
   with Global => null, Post => Head_Len'Result in 1 | 2 | 3 | 5;

   --  The head itself, indexed from 0.
   function Head (Major : Unsigned_8; N : Natural) return Byte_Array with
     Global => null,
     Pre    => Major in Text_Major | Bytes_Major,
     Post   =>
       Head'Result'First = 0
       and then Head'Result'Length = Head_Len (N)
       and then
         (if N <= 23 then
            Head'Result (0) = (Major or Unsigned_8 (N))
          elsif N <= 255 then
            Head'Result (0) = (Major or 24)
            and then Head'Result (1) = Unsigned_8 (N)
          elsif N <= 65535 then
            Head'Result (0) = (Major or 25)
            and then Head'Result (1) = Unsigned_8 (N / 256)
            and then Head'Result (2) = Unsigned_8 (N mod 256)
          else
            Head'Result (0) = (Major or 26)
            and then Head'Result (1) = Unsigned_8 (N / 2**24)
            and then Head'Result (2) = Unsigned_8 ((N / 2**16) mod 256)
            and then Head'Result (3) = Unsigned_8 ((N / 256) mod 256)
            and then Head'Result (4) = Unsigned_8 (N mod 256));

end Cbor_Encode;
