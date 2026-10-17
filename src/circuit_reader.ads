--  Circuit_Reader: the loader of LFC2 circuit files (Phase B, ADR
--  0046), generic over the sumcheck algebra of a field, so that the
--  loaded circuit is the Raw_Circuit of stage 3 and the constants are
--  read with the field's From_Bytes. The format is the one the
--  upstream production reader defines (google/longfellow-zk d5e6be7,
--  rust/core/proto/src/reader/lfc2.rs): the magic "LFC2"; the ULEB128
--  integers field_id, nv, ncopies (1), npublic_input,
--  subfield_boundary, ninput, nl; nconst constants of Section 7.2.1;
--  per layer logw, nw, a table of deltas (g, h0, h1 zigzag, a constant
--  index), a dictionary of segments (sequences of delta indices) and a
--  sequence of tokens (segment indices) whose expansion by prefix sums
--  is the layer's term list; then the 32-byte identifier, SHA-256 of
--  the canonical form (compute_id of rust/core/proto/src/circuit.rs).
--
--  Read makes two passes over the bytes: the first validates and
--  counts the layers and terms, the second allocates the circuit once
--  on the heap (ADR 0047) and fills it; then Well_Formed of the core is
--  checked and the identifier recomputed and compared. Where this
--  project is stricter than upstream the header of Circuit_Status says
--  so. The circuit is returned through an access type under SPARK's
--  ownership rules; the caller passes C.all to the verifier and calls
--  Free when done.
--
--  Documentation: docs/guide/06-circuits.md. Decisions: ADR 0046
--  (scope, the format, the status), 0047 (the heap), 0048 (vectors);
--  frame: ADR 0011, 0022.
--
--  Proof status. Silver on arbitrary bytes, with the ownership checks
--  (no dangling or null dereference, every allocation freed on every
--  path that does not return it). Gold on the shape of the result: on
--  Ok the circuit is well formed and its identifier is the stored one;
--  on any other status no circuit is returned. The expansion of
--  deltas, segments and tokens agrees with upstream by the vectors
--  (ADR 0048), not by proof.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0037.

pragma SPARK_Mode (On);

with Bytes;           use Bytes;
with Sumcheck_Algebra;
with Circuit_Status;  use Circuit_Status;

generic
   with package SA is new Sumcheck_Algebra (<>);
   --  FieldID of lib/proto/circuit_io.h: P-256 is 1, GF(2^128) is 4.
   Field_Id  : Natural;
   --  Binary fields hash the bit width into the identifier, prime
   --  fields the encoding of -1 (compute_id).
   Is_Binary : Boolean;
package Circuit_Reader is

   subtype Raw_Circuit is SA.Raw_Circuit;

   type Circuit_Access is access Raw_Circuit;

   --  What the file carries besides the circuit: the field identifier,
   --  the subfield boundary (the prover's, Phase C) and the identifier
   --  the transcript binds (Write_Sumcheck_Statement).
   type Header is record
      Field_Id          : Natural;
      Subfield_Boundary : Natural;
      Id                : Bytes_32;
   end record;

   Null_Header : constant Header :=
     (Field_Id => 0, Subfield_Boundary => 0, Id => [others => 0]);

   --  ceil_lg2 of the reference: 0 for N <= 1, else the least K with
   --  2^K >= N.
   function Ceil_Lg2 (N : Natural) return Natural with
     Global => null,
     Pre    => N <= SA.Max_Wires,
     Post   => Ceil_Lg2'Result <= 24
               and then (if N <= 1 then Ceil_Lg2'Result = 0);

   --  compute_id: SHA-256 of the field tag, the header words, each
   --  layer's nw, logw and term count and each term's g, h0, h1 and
   --  constant, all integers as eight little-endian bytes.
   function Compute_Id
     (C : Raw_Circuit; Subfield_Boundary : Natural) return Bytes_32
   with Global => null,
        Pre    => SA.Well_Formed (C);

   --  The loader. On Ok, C is the circuit (well formed) and H its
   --  header, with H.Id the identifier the file stored, equal to the
   --  recomputed one; on any other status C is null and H is
   --  Null_Header.
   procedure Read
     (B  : Byte_Array;
      C  : out Circuit_Access;
      H  : out Header;
      St : out Status)
   with
     Global => null,
     Pre    => B'First = 0,
     Post   =>
       (St = Ok) = (C /= null)
       and then (if St = Ok then
                   SA.Well_Formed (C.all)
                   and then H.Field_Id = Field_Id
                   and then H.Id = Compute_Id (C.all, H.Subfield_Boundary)
                 else H = Null_Header);

   procedure Free (C : in out Circuit_Access) with
     Global => null,
     Post   => C = null;

end Circuit_Reader;
