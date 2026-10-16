--  Ligero_Proof: a Ligero proof (draft Section 4.4.4, LigeroProof of
--  ligero/common.rs at d5e6be7) and its reader from the proof string
--  of Section 7.4 (read_ligero_proof of ligero/proof.rs). Generic over
--  the stage 3 algebra of a field, for the element array type.
--
--  The record holds the four response polynomials (BLOCK, DBLOCK, NREQ
--  and DBLOCK - BLOCK elements), the NREQ column nonces, the opened
--  columns (NROW * NREQ elements, row-major: row r at r * NREQ) and the
--  Merkle path, in a capacity of 2 n digests with its count. The sizes
--  are the geometry's, carried as discriminants and stated once by
--  Shape (ADR 0039).
--
--  The reader takes the string from an offset and reads, in order, the
--  polynomials and the nonces (fixed sizes), the run-length coded
--  columns and the path with its 4-byte count; Next is the offset
--  after the proof, for the reader of Section 7.5 to continue. The
--  rules of the run-length code (Section 7.4): runs alternate, full
--  field first; a run is a 4-byte little-endian size then that many
--  elements, in the full encoding of 7.2.1 or the subfield encoding of
--  7.2.2; a zero-length run only as the very first run and only once;
--  the runs cover exactly the NROW * NREQ elements, a run that
--  overshoots is an error; a run is at most 2^25 elements, the draft's
--  bound. Proof_Encoding on any violation, on a non-canonical element,
--  on a path count beyond the capacity and on bytes missing (ADR
--  0039); the record is then not to be used.
--
--  Documentation: docs/guide/05-ligero.md. Decisions: ADR 0035 (scope),
--  0038 (Gold on the rules), 0039 (sizes, the status); frame: ADR
--  0023, 0024. Index: docs/adr/README.md.
--
--  Proof status (per instance). Read is Gold on the rules, proof-only
--  (Proof_Levels): when it accepts, the columns part of the string
--  satisfies Well_Coded, the rules of 7.4 transcribed as a recursive
--  predicate over the runs, and Next is within the string. That it
--  never rejects a well-coded string is tested (ADR 0040). The
--  canonicity of the elements is the field's From_Bytes, Silver here.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0037.
--  Public data only.

pragma SPARK_Mode (On);

with Interfaces;       use Interfaces;
with Bytes;            use Bytes;
with Proof_Levels;
with SPARK.Lemmas.Integer_Arithmetic;
with Merkle;
with Ligero_Geometry;  use Ligero_Geometry;
with Verifier_Status;  use Verifier_Status;
with Sumcheck_Algebra;

generic
   with package SA is new Sumcheck_Algebra (<>);
package Ligero_Proof is

   use SA;

   subtype Element is SA.Element;

   --  Bytes per element, full and subfield encodings (Section 7.2).
   Size     : constant Positive := SA.F.Serialized_Size;
   Sub_Size : constant Positive := SA.F.Subfield_Size;

   --  The draft's bound on a run, and this unit's bound on the opened
   --  columns (ADR 0039): NROW * NREQ elements, so that every index
   --  into them is a Natural.
   Max_Run    : constant := 2**25;
   Max_Opened : constant := 2**25;

   function Fits (G : Valid_Geometry) return Boolean is
     (Long_Long_Integer (G.Total_Rows) * Long_Long_Integer (G.Num_Queries)
      <= Max_Opened);

   --  NROW * NREQ.
   function Opened (G : Valid_Geometry) return Natural is
     (G.Total_Rows * G.Num_Queries)
   with Pre => Fits (G);

   type Nonce_Array is array (Natural range <>) of Bytes_32;

   type Proof
     (Ldt_Last, Linear_Last, Low_Last, High_Last, Nonce_Last, Col_Last : Index;
      Path_Last : Merkle.Node_Index)
   is record
      Ldt_Poly    : Element_Array (0 .. Ldt_Last);
      Linear_Poly : Element_Array (0 .. Linear_Last);
      Quad_Low    : Element_Array (0 .. Low_Last);
      Quad_High   : Element_Array (0 .. High_Last);
      Nonces      : Nonce_Array (0 .. Nonce_Last);
      Columns     : Element_Array (0 .. Col_Last);
      Path        : Merkle.Digest_Array (0 .. Path_Last);
      Path_Count  : Natural := 0;
   end record
   with Dynamic_Predicate => Proof.Path_Count <= Proof.Path_Last + 1;

   --  The sizes of the geometry G.
   function Shape (P : Proof; G : Valid_Geometry) return Boolean is
     (P.Ldt_Last + 1 = G.Block_Len
      and then P.Linear_Last + 1 = G.Dblock_Len
      and then P.Low_Last + 1 = G.Num_Queries
      and then P.High_Last + 1 = G.Dblock_Len - G.Block_Len
      and then P.Nonce_Last + 1 = G.Num_Queries
      and then P.Col_Last + 1 = Opened (G)
      and then P.Path_Last + 1 = 2 * Num_Leaves (G))
   with Pre => Fits (G);

   --  The offset of row Row in the opened columns, Row * NREQ, with
   --  the room for its NREQ elements stated in 64 bits (the provers do
   --  not see that a product of bounded factors is bounded without
   --  help; the body gives it once).
   function Row_Off (G : Valid_Geometry; Row : Natural) return Natural with
     Global => null,
     Pre    => Fits (G) and then Row < G.Total_Rows,
     Post   =>
       Long_Long_Integer (Row_Off'Result)
       = Long_Long_Integer (Row) * Long_Long_Integer (G.Num_Queries)
       and then Row_Off'Result + G.Num_Queries <= Opened (G);

   --  Element J of the opened column of row Row (queried_columns
   --  [row * NREQ + j]).
   function Col
     (P : Proof; G : Valid_Geometry; Row, J : Natural) return Element
   is
     (P.Columns (Row_Off (G, Row) + J))
   with Pre => Fits (G) and then Shape (P, G)
               and then Row < G.Total_Rows and then J < G.Num_Queries;

   ----------------------------------------------------------------------
   --  The byte layout
   ----------------------------------------------------------------------

   --  The polynomials and the nonces: (BLOCK + DBLOCK + NREQ + DBLOCK -
   --  BLOCK) elements and NREQ nonces of 32 bytes.
   function Fixed_Len (G : Valid_Geometry) return Natural is
     ((2 * G.Dblock_Len + G.Num_Queries) * Size + 32 * G.Num_Queries);

   --  A 4-byte little-endian size (read_size_4bytes).
   function Size_4 (B : Byte_Array; Pos : Natural) return Unsigned_32 is
     (Unsigned_32 (B (Pos))
      or Shift_Left (Unsigned_32 (B (Pos + 1)), 8)
      or Shift_Left (Unsigned_32 (B (Pos + 2)), 16)
      or Shift_Left (Unsigned_32 (B (Pos + 3)), 24))
   with Pre => B'First = 0 and then B'Length >= 4
               and then Pos <= B'Length - 4;

   function Run_Width (Sub_Run : Boolean) return Positive is
     (if Sub_Run then Sub_Size else Size);

   --  The rules of Section 7.4 from offset Pos with Left elements still
   --  to cover, the next run being a subfield run when Sub_Run, no run
   --  read yet when First: either nothing remains, or the 4-byte size
   --  is there, at most Max_Run, at most Left, zero only for the first
   --  run, its elements are there, and the rest is well coded with the
   --  kinds alternated. Recursive, hence hidden (see Bytes.Add_Zeros);
   --  the lemmas of the body unhide it.
   function Well_Coded
     (B : Byte_Array; Pos, Left : Natural; Sub_Run, First : Boolean)
      return Boolean
   is
     (Left = 0
      or else
        (B'Length >= 4
         and then Pos <= B'Length - 4
         and then Size_4 (B, Pos) <= Max_Run
         and then Natural (Size_4 (B, Pos)) <= Left
         and then (Size_4 (B, Pos) > 0 or else First)
         and then Long_Long_Integer (Natural (Size_4 (B, Pos)))
                  * Long_Long_Integer (Run_Width (Sub_Run))
                  <= Long_Long_Integer (B'Length - Pos - 4)
         and then Well_Coded
                    (B,
                     Pos + 4 + Natural (Size_4 (B, Pos)) * Run_Width (Sub_Run),
                     Left - Natural (Size_4 (B, Pos)),
                     not Sub_Run,
                     False)))
   with Ghost              => Proof_Only,
        Annotate           =>
          (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre                => B'First = 0,
        Subprogram_Variant => (Decreases => Left,
                               Decreases => (if First then 1 else 0));

   ----------------------------------------------------------------------
   --  The reader
   ----------------------------------------------------------------------

   --  The proof at B (Off ..) for the geometry G into P, Next the
   --  offset after it. St is Ok or Proof_Encoding.
   procedure Read
     (B    : Byte_Array;
      Off  : Natural;
      G    : Valid_Geometry;
      P    : out Proof;
      Next : out Natural;
      St   : out Status)
   with
     Global => null,
     Pre    => B'First = 0 and then Off <= B'Length
               and then Fits (G)
               --  Shape (P, G) on the discriminants (a function call on
               --  an out parameter in a precondition reads it, which
               --  flow analysis rejects).
               and then P.Ldt_Last + 1 = G.Block_Len
               and then P.Linear_Last + 1 = G.Dblock_Len
               and then P.Low_Last + 1 = G.Num_Queries
               and then P.High_Last + 1 = G.Dblock_Len - G.Block_Len
               and then P.Nonce_Last + 1 = G.Num_Queries
               and then P.Col_Last + 1 = Opened (G)
               and then P.Path_Last + 1 = 2 * Num_Leaves (G),
     Post   =>
       (Proof_Only =>
          St in Ok | Proof_Encoding
          and then
            (if St = Ok then
               Next in Off .. B'Length
               and then Next - Off >= Fixed_Len (G)
               and then Well_Coded
                          (B, Off + Fixed_Len (G), Opened (G), False, True)));

end Ligero_Proof;
