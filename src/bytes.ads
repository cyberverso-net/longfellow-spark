--  Bytes: the byte array shared by the protocol code, and the ghost
--  byte sequence that models what a transcript has absorbed.
--
--  Documentation: docs/guide/04-transcript.md. Decisions implemented
--  here: ADR 0028 (one byte type for stage 4; P256_Field keeps its
--  Byte_Array as a subtype of this one), ADR 0031 (the absorbed-bytes
--  model as a functional sequence from SPARKlib); frame: ADR 0002,
--  0003, 0020. Index: docs/adr/README.md.
--
--  Proof status. Byte_Array and its subtypes carry no code. Byte_Seqs
--  is an instance of SPARKlib's functional infinite sequences
--  (SPARK.Containers.Functional.Infinite_Sequences, crate sparklib
--  pinned in alire.toml to the release of the toolchain); its
--  contracts are AdaCore's and are used here as given, with the same
--  standing as Big_Integers in the P-256 ghost model (trusted as a
--  model, ADR 0031). Append is a ghost function, Gold: its
--  postcondition states the length, the unchanged prefix and the
--  appended elements.
--
--  The model is proof-only. SPARKlib declares its lemma vocabulary
--  (Equal_Prefix and the like) at its assertion level SPARKlib_Full,
--  which depends on the level Static and therefore can never be
--  enabled at run time; ghost code that refers to it must sit at that
--  level too. Big_Length and Append do, and so does every contract of
--  the transcript that uses them: they are proved by GNATprove for all
--  inputs and are never compiled, in no build profile, so the absorbed
--  sequence costs nothing at run time and the test build of ADR 0010
--  does not execute them. What the test build does check is the
--  output: the B.2 vectors of the draft, byte for byte (ADR 0032).
--
--  Why a ghost sequence rather than a ghost array: the bytes a
--  transcript absorbs are unbounded in principle (Write0 of the term
--  count absorbs as many zero bytes as the circuit has terms), so a
--  fixed-capacity array would cap the circuits the contracts speak of.
--  A functional sequence is a mathematical value: no capacity, no
--  aliasing, and equality is extensional (two sequences are equal when
--  they have the same length and the same elements).
--
--  Constant-time discipline: not applicable, no executable code.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with SPARK.Big_Integers; use SPARK.Big_Integers;
with SPARK.Containers.Functional.Infinite_Sequences;

package Bytes is

   --  The index stops one short of Natural'Last so that the length of
   --  any array fits an Integer, which the ghost model converts to a
   --  big integer without a range check.
   subtype Byte_Index is Natural range 0 .. Natural'Last - 1;

   type Byte_Array is array (Byte_Index range <>) of Unsigned_8;

   subtype Bytes_8  is Byte_Array (0 .. 7);
   subtype Bytes_16 is Byte_Array (0 .. 15);
   subtype Bytes_32 is Byte_Array (0 .. 31);
   subtype Bytes_64 is Byte_Array (0 .. 63);

   ----------------------------------------------------------------------
   --  Ghost model: a sequence of bytes
   ----------------------------------------------------------------------

   --  An instance of SPARKlib's functional sequences. GNAT 16 does not
   --  accept the Ghost aspect on an instantiation, so the instance is
   --  an ordinary package; only ghost code of this project refers to
   --  it. Positions are 1-based big integers (First = 1, Last = Length),
   --  as in SPARKlib.
   package Byte_Seqs is new SPARK.Containers.Functional.Infinite_Sequences
     (Element_Type => Unsigned_8);

   subtype Byte_Seq is Byte_Seqs.Sequence;

   --  The length of an array as a big integer; the index subtype makes
   --  the conversion safe.
   function Big_Length (D : Byte_Array) return Big_Natural is
     (To_Big_Integer (D'Length))
   with Ghost => SPARKlib_Full;

   --  S followed by the bytes of D in order. Gold: the postcondition
   --  is the full characterisation (length, S kept as a prefix, the
   --  bytes of D after it); the body builds the result one element at
   --  a time with Byte_Seqs.Add.
   function Append (S : Byte_Seq; D : Byte_Array) return Byte_Seq with
     Ghost => SPARKlib_Full,
     Post  =>
       Byte_Seqs.Length (Append'Result) = Byte_Seqs.Length (S) + Big_Length (D)
       and then Byte_Seqs.Equal_Prefix (S, Append'Result)
       and then
         (for all I in D'Range =>
            Byte_Seqs.Get
              (Append'Result,
               Byte_Seqs.Length (S) + To_Big_Integer (I - D'First + 1))
            = D (I));

   --  S followed by N zero bytes, defined by recursion on N so that
   --  Add_Zeros (S, N + 1) = Add (Add_Zeros (S, N), 0) holds by
   --  definition: that is what the byte-by-byte loop of Write0 needs.
   function Add_Zeros (S : Byte_Seq; N : Natural) return Byte_Seq is
     (if N = 0 then S else Byte_Seqs.Add (Add_Zeros (S, N - 1), 0))
   with
     Ghost              => SPARKlib_Full,
     Subprogram_Variant => (Decreases => N);

end Bytes;
