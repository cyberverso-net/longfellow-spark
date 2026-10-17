--  Proof_Writer: the serialisation of a complete proof (Phase C, ADR
--  0049, 0051, 0052), the writers of Sections 7.3, 7.4 and 7.5 as the
--  inverses of the readers of stages 4 and 5 (Sumcheck_Transcript.
--  Read_Sumcheck_Proof, Ligero_Proof.Read, Zk_Verifier.Read_Proof),
--  write_sumcheck_proof, write_ligero_proof and write_zk_proof of the
--  reference (docs/specs/rust/src/sumcheck/proof.rs, ligero/proof.rs,
--  zk/proof.rs at d5e6be7). Generic over the Ligero verifier of a
--  field, which carries the algebra, the proof records and the
--  reader's rules.
--
--  Section 7.3: per layer, per round the four elements hand 0 p (0),
--  hand 1 p (0), hand 0 p (P2), hand 1 p (P2), then the two claims,
--  from the pad order of the Sumcheck_Proof record. Section 7.4: the
--  four polynomials, the nonces, then the opened columns in runs that
--  alternate from a full-field run, each a 4-byte little-endian count
--  and its elements, then the path count and the path. The reference
--  decides the runs by testing every element for membership in the
--  subfield; this writer decides them by position (ADR 0051): a row of
--  the tableau is a subfield row when the field is its own subfield
--  (P-256, where the reference's test is always true and the file
--  starts with an empty full-field run) or when it is a witness row
--  wholly below the subfield boundary; the runs are the maximal groups
--  of consecutive rows of one kind, so at most three, and the first,
--  possibly empty, is a full-field run, as the reader requires.
--
--  Documentation: docs/guide/07-prover.md.
--
--  Proof status (per instance). Silver. Gold, structural: the 7.4
--  writer produces bytes that satisfy Well_Coded of the reader at the
--  reader's offset, with the length the length functions state; the
--  fixed part of each writer (root, polynomials, nonces, path) is the
--  element-wise serialisation of the record. That Read (Write (P)) = P
--  follows from these layouts and the field-level facts (To_Bytes and
--  From_Bytes are inverses, chapters 1 and 2); it is tested on every
--  proof file of the repository (writer_kat), since the readers state
--  their structure, not the values they read, and the encodings are
--  formals of the field signature without contracts.
--
--  Constant-time discipline (ADR 0006, ADR 0051): the run structure
--  depends on the geometry and the subfield boundary, never on an
--  element's value; the element encodings are the field's.

pragma SPARK_Mode (On);

with Interfaces;       use Interfaces;
with Bytes;            use Bytes;
with Proof_Levels;
with Merkle;
with Ligero_Geometry;  use Ligero_Geometry;
with Ligero_Verifier;

generic
   with package LV is new Ligero_Verifier (<>);
package Proof_Writer is

   subtype Element is LV.ST.SA.Element;
   subtype Circuit is LV.ST.SA.Circuit;
   subtype Sumcheck_Proof is LV.ST.SV.Sumcheck_Proof;
   subtype Ligero_Part is LV.LP.Proof;

   Size     : constant Positive := LV.LP.Size;
   Sub_Size : constant Positive := LV.LP.Sub_Size;

   -------------------------------------------------------------------
   --  Section 7.3
   -------------------------------------------------------------------

   function Sumcheck_Len (C : Circuit) return Natural is
     (LV.ST.SV.Proof_Total (C) * Size)
   with Global => null;

   --  Slot K of a byte string of Size-byte elements.
   function Slot (B : Byte_Array; K : Natural) return Byte_Array is
     (B (K * Size .. K * Size + Size - 1))
   with Ghost  => Proof_Only,
        Global => null,
        Pre    => B'First = 0 and then K < B'Length / Size
                  and then B'Length <= Natural'Last / Size * Size;

   procedure Write_Sumcheck_Proof
     (C : Circuit;
      P : Sumcheck_Proof;
      B : out Byte_Array)
   with
     Global => null,
     Pre    => B'First = 0
               and then P.Last + 1 = LV.ST.SV.Proof_Total (C)
               and then B'Length = Sumcheck_Len (C);

   -------------------------------------------------------------------
   --  Section 7.4
   -------------------------------------------------------------------

   --  Row Row of the tableau is a subfield row: the field is its own
   --  subfield, or the row is a witness row (rows 3 .. 2 + NWROW) wholly
   --  below the subfield boundary Sfb (witnesses i WR .. i WR + WR - 1
   --  all below Sfb).
   function Sub_Row
     (G : Valid_Geometry; Sfb : Natural; Row : Natural) return Boolean
   is
     (Sub_Size = Size
      or else
        (Row >= 3
         and then Row < 3 + G.Num_Witness_Rows
         and then Long_Long_Integer (Row - 2)
                  * Long_Long_Integer (G.Witnesses_Per_Row)
                  <= Long_Long_Integer (Sfb)))
   with Global => null, Pre => Row < G.Total_Rows;

   --  The three groups of rows: Lead full-field rows, then Sub subfield
   --  rows, then Trail full-field rows. The witness rows below the
   --  boundary are the first witness rows, so the groups are
   --  consecutive.
   function Lead_Rows return Natural is
     (if Sub_Size = Size then 0 else 3)
   with Global => null;

   function Sub_Rows (G : Valid_Geometry; Sfb : Natural) return Natural is
     (if Sub_Size = Size then G.Total_Rows
      else Natural'Min (G.Num_Witness_Rows, Sfb / G.Witnesses_Per_Row))
   with Global => null;

   function Trail_Rows (G : Valid_Geometry; Sfb : Natural) return Natural is
     (G.Total_Rows - Lead_Rows - Sub_Rows (G, Sfb))
   with Global => null, Pre => Lead_Rows + Sub_Rows (G, Sfb) <= G.Total_Rows;

   --  Elements of N rows, N * NREQ, bounded by the opened columns.
   function Row_Elems (G : Valid_Geometry; N : Natural) return Natural with
     Global => null,
     Pre    => LV.LP.Fits (G) and then N <= G.Total_Rows,
     Post   => Long_Long_Integer (Row_Elems'Result)
               = Long_Long_Integer (N) * Long_Long_Integer (G.Num_Queries)
               and then Row_Elems'Result <= LV.LP.Opened (G);

   --  The groups never exceed the rows (Lead is at most the three random
   --  rows, Sub at most the witness rows), and their elements add up to
   --  the opened columns.
   procedure Lemma_Groups (G : Valid_Geometry; Sfb : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => LV.LP.Fits (G),
     Post   => Lead_Rows + Sub_Rows (G, Sfb) <= G.Total_Rows
               and then Row_Elems (G, Lead_Rows)
                        + Row_Elems (G, Sub_Rows (G, Sfb))
                        + Row_Elems (G, Trail_Rows (G, Sfb))
                        = LV.LP.Opened (G);

   --  The bytes of the opened columns in runs: one run per non-empty
   --  group, plus the first run even when empty; a single run of every
   --  row when there is no subfield row.
   function Runs_Len (G : Valid_Geometry; Sfb : Natural) return Natural with
     Global => null,
     Pre    => LV.LP.Fits (G),
     Post   => Runs_Len'Result <= 12 + LV.LP.Opened (G) * Size
               and then
                 (if Sub_Rows (G, Sfb) = 0 then
                    Runs_Len'Result = 4 + LV.LP.Opened (G) * Size
                  else
                    Runs_Len'Result
                    = 4 + Row_Elems (G, Lead_Rows) * Size
                      + 4 + Row_Elems (G, Sub_Rows (G, Sfb)) * Sub_Size
                      + (if Trail_Rows (G, Sfb) > 0 then
                           4 + Row_Elems (G, Trail_Rows (G, Sfb)) * Size
                         else 0));

   function Ligero_Len
     (G : Valid_Geometry; Sfb : Natural; Path_Count : Natural) return Natural
   is
     (LV.LP.Fixed_Len (G) + Runs_Len (G, Sfb) + 4 + 32 * Path_Count)
   with Global => null,
        Pre    => LV.LP.Fits (G) and then Path_Count <= 2 * Merkle.Max_Leaves;

   --  The Ligero part into B from Off (the reader's Off); the bytes
   --  before Off are unchanged.
   procedure Write_Ligero_Proof
     (G   : Valid_Geometry;
      Sfb : Natural;
      P   : Ligero_Part;
      B   : in out Byte_Array;
      Off : Natural)
   with
     Global => null,
     Pre    => B'First = 0
               and then LV.LP.Fits (G)
               and then LV.LP.Shape (P, G)
               and then Off <= B'Length
               and then B'Length - Off = Ligero_Len (G, Sfb, P.Path_Count),
     Post   =>
       (Runtime    => (for all I in B'Range =>
                         (if I < Off then B (I) = B'Old (I))),
        Proof_Only =>
          LV.LP.Well_Coded
            (B, Off + LV.LP.Fixed_Len (G), LV.LP.Opened (G), False, True));

   -------------------------------------------------------------------
   --  Section 7.5
   -------------------------------------------------------------------

   function Proof_Len
     (C : Circuit; G : Valid_Geometry; Sfb : Natural; Path_Count : Natural)
      return Natural
   is
     (32 + Sumcheck_Len (C) + Ligero_Len (G, Sfb, Path_Count))
   with Global => null,
        Pre    => LV.LP.Fits (G) and then Path_Count <= 2 * Merkle.Max_Leaves;

   procedure Write_Proof
     (C        : Circuit;
      G        : Valid_Geometry;
      Sfb      : Natural;
      Root     : Bytes_32;
      Sumcheck : Sumcheck_Proof;
      Lig      : Ligero_Part;
      B        : out Byte_Array)
   with
     Global => null,
     Pre    => B'First = 0
               and then LV.LP.Fits (G)
               and then LV.LP.Shape (Lig, G)
               and then Sumcheck.Last + 1 = LV.ST.SV.Proof_Total (C)
               and then B'Length = Proof_Len (C, G, Sfb, Lig.Path_Count),
     Post   =>
       (Runtime    => B (0 .. 31) = Root,
        Proof_Only =>
          LV.LP.Well_Coded
            (B, 32 + Sumcheck_Len (C) + LV.LP.Fixed_Len (G),
             LV.LP.Opened (G), False, True));

end Proof_Writer;
