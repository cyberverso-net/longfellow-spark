--  Uleb128: the unsigned LEB128 integers of the LFC2 circuit format
--  (Phase B, ADR 0046), as the upstream production reader defines them
--  (google/longfellow-zk d5e6be7, rust/core/proto/src/uleb.rs,
--  read_uleb128_max4): at most four bytes, each carrying seven bits
--  least significant group first and a continuation bit; a fourth byte
--  with the continuation bit set is an error; the value is therefore
--  below 2^28. Non-minimal encodings are accepted, as upstream does.
--  Zigzag decoding of the deltas as decode_delta_u32: even values are
--  halved, odd values v give -(v / 2) - 1.
--
--  Documentation: docs/guide/06-circuits.md.
--
--  Proof status. Gold: Read returns the value of the bytes it consumed
--  (Payload), consumes one to four bytes, and fails exactly when no
--  terminating byte lies within four bytes of the file; Zigzag is its
--  definition. Silver on everything.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0037:
--  a circuit file is public data.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Bytes;      use Bytes;

package Uleb128 is

   Max_Bytes : constant := 4;
   Max_Value : constant := 2**28 - 1;

   subtype Value is Natural range 0 .. Max_Value;

   --  128^I for I in 0 .. Max_Bytes, by cases: the provers handle the
   --  constants where they do not handle a variable exponent.
   function Pow128 (I : Natural) return Positive is
     (case I is
         when 0      => 1,
         when 1      => 128,
         when 2      => 16384,
         when 3      => 2097152,
         when others => 268435456)
   with Global => null, Pre => I <= Max_Bytes;

   --  The seven-bit payloads of the N bytes at Pos, least significant
   --  first: the integer an N-byte encoding denotes.
   function Payload (B : Byte_Array; Pos : Natural; N : Natural)
                     return Natural is
     (if N = 0 then 0
      else Payload (B, Pos, N - 1)
           + Natural (B (Pos + N - 1) and 16#7F#) * Pow128 (N - 1))
   with Ghost, Global => null,
        Pre  => N <= Max_Bytes and then Pos >= B'First
                and then (N = 0
                          or else (Pos <= B'Last
                                   and then B'Last - Pos >= N - 1)),
        Post => Payload'Result < Pow128 (N),
        Subprogram_Variant => (Decreases => N);

   --  Ok when a byte without the continuation bit lies within four
   --  bytes from Pos: V is the value and Pos advances past that byte.
   --  Otherwise V is 0 and Pos is unchanged (Truncated when the file
   --  ends first, Bad_Integer when a fourth byte continues; Long says
   --  which).
   procedure Read
     (B    : Byte_Array;
      Pos  : in out Natural;
      V    : out Value;
      Ok   : out Boolean;
      Long : out Boolean)
   with
     Global => null,
     Pre    => B'First = 0 and then Pos <= B'Length,
     Post   =>
       (if Ok then
          Pos - Pos'Old in 1 .. Max_Bytes
          and then Pos <= B'Length
          and then (B (Pos - 1) and 16#80#) = 0
          and then V = Payload (B, Pos'Old, Pos - Pos'Old)
          and then not Long
        else Pos = Pos'Old and then V = 0);

   --  decode_delta_u32: the signed delta of a value.
   function Zigzag (V : Value) return Integer is
     (if V mod 2 = 0 then V / 2 else -(V / 2) - 1)
   with Global => null,
        Post => Zigzag'Result in -(2**27) .. 2**27 - 1;

end Uleb128;
