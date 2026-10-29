--  Transcript: the Fiat-Shamir transcript of draft Section 3, SHA-256
--  accumulator and AES-256 counter-mode generator (FsPrf), with the
--  byte-level codec of Section 3.2 and the extraction methods of
--  Section 3.4 (nat, choose). The field enters only through the
--  serialised bytes it is given: this package is not generic and
--  knows nothing of field elements.
--
--  Documentation: docs/guide/04-transcript.md. Decisions implemented
--  here: ADR 0028 (scope, the package with state, the Exhausted flag
--  at the 2^40 block bound), 0030 (literal rejection sampling, declared
--  non-termination), 0031 (the Gold perimeter: codec over a ghost byte
--  sequence, nat, choose); frame: ADR 0002, 0003, 0020, 0029. Index:
--  docs/adr/README.md.
--
--  One transcript at a time. The package holds the state; Reset starts
--  a new transcript from a label, as Transcript::new does in the
--  reference (docs/specs/rust/src/transcript.rs at d5e6be7). A program
--  that needs two transcripts drives them in sequence (ADR 0031).
--
--  Proof status (Silver = absence of run-time errors, Gold = proved
--  functional contracts). The Gold statements about the absorbed bytes
--  are proof-only: they sit at SPARKlib's assertion level SPARKlib_Full
--  (see bytes.ads), are proved by GNATprove for all inputs and are
--  never compiled, in no build profile. They are stated with
--  Byte_Seqs.Logical_Eq, the logical equality of sequences, for the
--  same reason stage 3 states its equalities with Same (ADR 0023):
--  the extensional "=" of SPARKlib gives the provers no congruence,
--  and the proof of a frame is a chain of substitutions.
--
--    Absorbed     : ghost model, the bytes handed to SHA-256 so far.
--                   Appended to in exactly two places, Absorb and
--                   Absorb_Byte in the body, which are also the only
--                   calls of Sha256.Update.
--    Reset, Write_Bytes, Write0, Write_Element, Write_Slice :
--                   Gold, structural (ADR 0023): each appends its frame
--                   of Section 3.2 to Absorbed, as the ghost functions
--                   Bytes_Frame, Zero_Frame, Element_Frame and
--                   Slice_Frame spell it out piece by piece, and
--                   discards the generator.
--    Get_Random_Bytes : Silver with proved shape: the generator is live
--                   afterwards (seeded from the digest when it was not),
--                   Exhausted is sticky. That the bytes are AES-256 of
--                   the counter under the digest is tested (Appendix
--                   B.2 of the draft, ADR 0032), not proved.
--    Nat          : Gold, the result is below n; the mask and byte
--                   length of Section 3.4.1 are carried as invariants.
--                   Declared possibly non-terminating (ADR 0030).
--    Choose       : Gold, the k results are distinct and below n, from
--                   the permutation invariant of the Fisher-Yates array.
--                   Declared possibly non-terminating (it calls Nat).
--    Is_Exhausted : the generator passed 2^40 blocks (ADR 0028); the
--                   reference panics there, this package returns zero
--                   bytes from then on and the flag never clears, so a
--                   replay reports it as a status.
--
--  Pinned spec: IETF draft-irtf-cfrg-longfellow-00, Sections 3.1, 3.1.1,
--  3.2, 3.4.1, 3.4.2; test vectors Appendix B.2.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0029.
--  The transcript processes the public content of a proof string; it
--  MUST NOT be given secret data.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with Fisher_Yates;

package Transcript with
  Abstract_State => State,
  Initializes    => (State, Absorbed)
is

   --  The model: every byte handed to SHA-256 since Reset, in order.
   Absorbed : Byte_Seq with Ghost => SPARKlib_Full;

   --  A generator is live between a draw and the next write.
   function Generator_Live return Boolean with
     Ghost  => SPARKlib_Full,
     Global => (Input => State);

   --  The generator passed 2^40 blocks since it was seeded; sticky.
   function Is_Exhausted return Boolean with
     Global => (Input => State);

   --  The largest payload a frame may carry.
   Max_Payload : constant := Byte_Index'Last - 32;

   --  The eight little-endian bytes of N (the length prefix of the
   --  codec, and the counter block of FsPrf).
   function Length_Bytes (N : Unsigned_64) return Bytes_8 with
     Global => null,
     Post   =>
       Length_Bytes'Result (0) = Unsigned_8 (N mod 256)
       and then Length_Bytes'Result (1) = Unsigned_8 (Shift_Right (N, 8) mod 256)
       and then Length_Bytes'Result (2) = Unsigned_8 (Shift_Right (N, 16) mod 256)
       and then Length_Bytes'Result (3) = Unsigned_8 (Shift_Right (N, 24) mod 256)
       and then Length_Bytes'Result (4) = Unsigned_8 (Shift_Right (N, 32) mod 256)
       and then Length_Bytes'Result (5) = Unsigned_8 (Shift_Right (N, 40) mod 256)
       and then Length_Bytes'Result (6) = Unsigned_8 (Shift_Right (N, 48) mod 256)
       and then Length_Bytes'Result (7) = Unsigned_8 (Shift_Right (N, 56) mod 256);

   ----------------------------------------------------------------------
   --  The frames of Section 3.2 (ghost, proof-only): S followed by the
   --  frame, piece by piece, in the order the bytes reach SHA-256
   ----------------------------------------------------------------------

   --  Byte array: tag 0x00, the eight length bytes, the bytes.
   function Bytes_Frame (S : Byte_Seq; D : Byte_Array) return Byte_Seq is
     (Append (Append (Byte_Seqs.Add (S, 0),
                      Length_Bytes (Unsigned_64 (D'Length))),
              D))
   with Ghost => SPARKlib_Full;

   --  write0 (n): the byte array frame around n zero bytes.
   function Zero_Frame (S : Byte_Seq; N : Natural) return Byte_Seq is
     (Add_Zeros (Append (Byte_Seqs.Add (S, 0), Length_Bytes (Unsigned_64 (N))),
                 N))
   with Ghost => SPARKlib_Full;

   --  Field element: tag 0x01, the serialised element.
   function Element_Frame (S : Byte_Seq; E : Byte_Array) return Byte_Seq is
     (Append (Byte_Seqs.Add (S, 1), E))
   with Ghost => SPARKlib_Full;

   --  Field element array: tag 0x02, the eight count bytes (the head),
   --  then the serialised elements with no per-element tag.
   function Slice_Header (S : Byte_Seq; Count : Natural) return Byte_Seq is
     (Append (Byte_Seqs.Add (S, 2), Length_Bytes (Unsigned_64 (Count))))
   with Ghost => SPARKlib_Full;

   function Slice_Frame
     (S : Byte_Seq; Count : Natural; E : Byte_Array) return Byte_Seq
   is
     (Append (Slice_Header (S, Count), E))
   with Ghost => SPARKlib_Full;

   ----------------------------------------------------------------------
   --  Absorb
   ----------------------------------------------------------------------

   --  A new transcript: fresh accumulator, no generator, not exhausted,
   --  then the label as a byte array frame (Transcript::new).
   procedure Reset (Label : Byte_Array) with
     Global => (In_Out => (State, Absorbed)),
     Pre    => Label'Length <= Max_Payload,
     Post   =>
       (SPARKlib_Full =>
          Byte_Seqs.Logical_Eq
            (Absorbed, Bytes_Frame (Byte_Seqs.Empty_Sequence, Label))
          and then not Generator_Live and then not Is_Exhausted);

   procedure Write_Bytes (D : Byte_Array) with
     Global => (In_Out => (State, Absorbed)),
     Pre    => D'Length <= Max_Payload,
     Post   =>
       (SPARKlib_Full =>
          Is_Exhausted'Old <= Is_Exhausted
          and then Byte_Seqs.Logical_Eq (Absorbed, Bytes_Frame (Absorbed'Old, D))
          and then not Generator_Live);

   procedure Write0 (N : Natural) with
     Global => (In_Out => (State, Absorbed)),
     Pre    => N <= Max_Payload,
     Post   =>
       (SPARKlib_Full =>
          Is_Exhausted'Old <= Is_Exhausted
          and then Byte_Seqs.Logical_Eq (Absorbed, Zero_Frame (Absorbed'Old, N))
          and then not Generator_Live);

   procedure Write_Element (E : Byte_Array) with
     Global => (In_Out => (State, Absorbed)),
     Pre    => E'Length <= Max_Payload,
     Post   =>
       (SPARKlib_Full =>
          Is_Exhausted'Old <= Is_Exhausted
          and then Byte_Seqs.Logical_Eq
            (Absorbed, Element_Frame (Absorbed'Old, E))
          and then not Generator_Live);

   --  E is the concatenation of the Count serialised elements; the
   --  caller knows their size, this package does not.
   procedure Write_Slice (Count : Natural; E : Byte_Array) with
     Global => (In_Out => (State, Absorbed)),
     Pre    => E'Length <= Max_Payload,
     Post   =>
       (SPARKlib_Full =>
          Is_Exhausted'Old <= Is_Exhausted
          and then Byte_Seqs.Logical_Eq
            (Absorbed, Slice_Frame (Absorbed'Old, Count, E))
          and then not Generator_Live);

   --  The same frame one element at a time (ADR 0039), for slices too
   --  long to serialise in one array: Begin_Slice absorbs the head,
   --  then Slice_Element each serialised element; Count calls absorb
   --  exactly what Write_Slice absorbs for their concatenation.
   procedure Begin_Slice (Count : Natural) with
     Global => (In_Out => (State, Absorbed)),
     Post   =>
       (SPARKlib_Full =>
          Is_Exhausted'Old <= Is_Exhausted
          and then Byte_Seqs.Logical_Eq
            (Absorbed, Slice_Header (Absorbed'Old, Count))
          and then not Generator_Live);

   procedure Slice_Element (E : Byte_Array) with
     Global => (In_Out => (State, Absorbed)),
     Pre    => E'Length <= Max_Payload,
     Post   =>
       (SPARKlib_Full =>
          Is_Exhausted'Old <= Is_Exhausted
          and then Byte_Seqs.Logical_Eq (Absorbed, Append (Absorbed'Old, E))
          and then not Generator_Live);

   ----------------------------------------------------------------------
   --  Squeeze
   ----------------------------------------------------------------------

   --  D'Length pseudorandom bytes: the generator is seeded with the
   --  digest of the absorbed bytes when none is live, and unread bytes
   --  of a block are kept for the next request (Section 3.1).
   procedure Get_Random_Bytes (D : out Byte_Array) with
     Global => (In_Out => State),
     Post   =>
       (SPARKlib_Full =>
          Is_Exhausted'Old <= Is_Exhausted and then Generator_Live);

   --  Section 3.4.1: a uniform natural below N by minimal bitmask
   --  rejection, reading the byte length of N bytes little-endian.
   --  The loop retries until a draw is accepted; no cap (ADR 0030).
   procedure Nat (N : Positive; R : out Natural) with
     Global            => (In_Out => State),
     Always_Terminates => False,
     Post              => Is_Exhausted'Old <= Is_Exhausted and then R < N;

   --  Section 3.4.2: K distinct naturals below N, Fisher-Yates over a
   --  fresh array 0 .. N - 1 driven by Nat (N - i): the draws here,
   --  the shuffle in Fisher_Yates. Empty when N or K is 0; K <= N as
   --  the reference asserts.
   Max_Choose_N : constant := Fisher_Yates.Max_N;

   subtype Index_Array is Fisher_Yates.Index_Array;

   procedure Choose (N, K : Natural; R : out Index_Array) with
     Global            => (In_Out => State),
     Always_Terminates => False,
     Pre               =>
       K <= N and then N <= Max_Choose_N
       and then R'First = 0 and then R'Last = K - 1,
     Post              =>
       Is_Exhausted'Old <= Is_Exhausted
       and then (for all I in R'Range => R (I) < N)
       and then
         (for all I in R'Range =>
            (for all J in R'Range => (if I /= J then R (I) /= R (J))));

end Transcript;
