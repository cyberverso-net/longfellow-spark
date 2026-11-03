--  Pinned_Circuits: the circuit files whose identifier was checked once
--  (ADR 0074), as upstream's mDoc application expects of its caller
--  (lib/circuits/mdoc/mdoc_zk.cc at d5e6be7: a list of supported
--  circuits, the identifier checked once and the circuit then kept as
--  trusted). Each entry is the SHA-256 of the bytes of an LFC2 file and
--  the identifier that a full Read of that file recomputed. A file in
--  the list is loaded with the identifier pinned (Read_Pinned, or
--  Read_Packed with Pinned True), any other with the identifier
--  recomputed. The two command-line programs load the packed form
--  (Read_Packed below, the memory milestone, ADR 0080); Read, the
--  expanded one, serves the tests. interop_kat checks every entry
--  against a full load of its file in tests/vectors, in both forms.
--  Outside the proof perimeter (SPARK_Mode Off); the trust model lists
--  the table as trusted.

pragma SPARK_Mode (Off);

with Bytes; use Bytes;
with Circuit_Reader;
with Circuit_Status;

package Pinned_Circuits is

   type Entry_Index is range 1 .. 3;

   --  The file of an entry, relative to the root of the repository.
   function Path (E : Entry_Index) return String;

   --  Whether the circuit of an entry is over GF(2^128) (else P-256).
   function Binary (E : Entry_Index) return Boolean;

   --  The SHA-256 of the file bytes and the identifier of an entry.
   function File_Digest (E : Entry_Index) return Bytes_32;
   function Id (E : Entry_Index) return Bytes_32;

   --  Whether B is the file of an entry, and its identifier if so.
   procedure Lookup (B : Byte_Array; Found : out Boolean; Id : out Bytes_32);

   --  The load of the expanded circuit: Read_Pinned when B is in the
   --  list and Full is False, Read otherwise.
   generic
      with package CR is new Circuit_Reader (<>);
   procedure Read
     (B    : Byte_Array;
      Full : Boolean;
      C    : out CR.Circuit_Access;
      H    : out CR.Header;
      St   : out Circuit_Status.Status);

   --  The load of the packed circuit: Read_Packed with the identifier
   --  pinned when B is in the list and Full is False, recomputed
   --  otherwise.
   generic
      with package CR is new Circuit_Reader (<>);
   procedure Read_Packed
     (B    : Byte_Array;
      Full : Boolean;
      P    : out CR.Packed_Access;
      H    : out CR.Header;
      St   : out Circuit_Status.Status);

end Pinned_Circuits;
