--  Ligero_Prover: the commitment of draft Section 4.3 (Phase C, ADR
--  0049, 0050, 0051, 0052), layout_tableau and commit of the reference
--  (docs/specs/rust/src/ligero/prover.rs at d5e6be7), the Reed-Solomon
--  encoder of ligero/reed_solomon.rs on all NCOL columns and
--  commit_merkle_heap of merkle.rs. Generic over the Ligero verifier of
--  a field, which carries the transcript glue, the proof layout, the
--  Lagrange tables and the geometry, and over the sampling instance of
--  that field, which carries the randomness source.
--
--  The tableau has NROW rows of NCOL elements. Before encoding, row 0
--  is BLOCK random elements, row 1 DBLOCK random elements with the sum
--  of its witness slots subtracted from the first, row 2 DBLOCK random
--  elements with the witness slots zeroed, witness row i a prefix of
--  NREQ random elements (in the subfield when the row lies wholly below
--  the subfield boundary) followed by the witnesses i WR .. i WR + WR
--  - 1 (zero beyond NW), and the quadratic rows x, y, z the same prefix
--  followed by the triples' values; every row is encoded with the
--  Lagrange table of its length (the systematic part is the row
--  itself). Randomness is consumed in that order, the three rows x, y,
--  z of one quadratic row interleaved as the reference samples them,
--  then one 32-byte nonce per committed column (NCOL - DBLOCK of
--  them), all before any leaf is hashed. A leaf is SHA-256 of the nonce
--  and the column's elements, row by row, as To_Bytes writes them; the
--  tree is Merkle.Build, the root its node 1.
--
--  Documentation: docs/guide/07-prover.md.
--
--  Proof status (per instance). Silver with the ownership checks on
--  the heap commitment. Gold, structural (ADR 0052), on the row
--  procedures of the body: the systematic part of every encoded row is
--  the row and the parity part is Lagrange.Evaluate (Encode_Row); row R
--  of the tableau receives the encoding and the other rows are
--  untouched (Commit_Row); the witness slots of a row before encoding
--  hold the witnesses i WR .. i WR + WR - 1 and zero beyond NW, or the
--  triples' values and zero beyond NQ, or zero (Fill_Witness_Slots,
--  Fill_Quad_Slots, Zero_Slots); the witness slots of row 2 of the
--  tableau are zero (Fixed_Rows). The composition over the NROW rows
--  (the shapes of the whole tableau) is not a postcondition of Commit:
--  its proof needed frame bookkeeping over the whole tableau that the
--  provers did not complete within the budget, and it is tested slot
--  by slot by prover_kat against the reference. Commit's postcondition
--  is the shape of the commitment and Root = Heap (1) (Merkle.Build's
--  postcondition gives the tree). What the random slots hold is not
--  stated (it is the randomness). Prove (block 5) is Silver: its
--  polynomials are the reference's sums over the tableau, tested by
--  the byte identity with the upstream proofs and by the verifier's
--  acceptance (ADR 0053); its opening is Merkle.Open (Gold there).
--
--  Constant-time discipline (ADR 0051): constant time by construction.
--  The row layout branches on positions and the geometry (public) and
--  on the subfield boundary (public); the witnesses are copied by fixed
--  loops and multiplied by public Lagrange coefficients; the hashes run
--  over fixed-length data. The guarantee is scoped to builds with
--  assertions disabled (ADR 0006).

pragma SPARK_Mode (On);

with Bytes;             use Bytes;
with Proof_Levels;
with Transcript;
with Merkle;
with Ligero_Geometry;  use Ligero_Geometry;
with Ligero_Verifier;
with Sampling;

generic
   with package LV is new Ligero_Verifier (<>);
   with package SP is new Sampling (F => LV.ST.SA.F, others => <>);
package Ligero_Prover is

   use LV.ST.SA.F;

   subtype Element is LV.Element;
   subtype Element_Array is LV.Element_Array;
   subtype Index is LV.Index;
   subtype Digest is Merkle.Digest;
   subtype Lqc_Array is LV.Lqc_Array;
   subtype Lqc_Triple is LV.ST.SV.Lqc_Triple;
   subtype Table is LV.L.Table;
   subtype Nonce_Array is LV.LP.Nonce_Array;

   --  Elements of the tableau this implementation is willing to hold.
   Max_Tableau : constant := 2**26;

   --  A geometry the prover handles: the proof fits (Ligero_Proof),
   --  every column is an evaluation point, the longest row fits a
   --  Lagrange table, the parity columns fit the table's width, the
   --  tableau fits.
   function Prover_Fits (G : Valid_Geometry) return Boolean is
     (LV.LP.Fits (G)
      and then G.Encoded_Len - 1 <= LV.Max_Eval_Point
      and then G.Dblock_Len <= LV.L.Max_K
      and then G.Encoded_Len - G.Block_Len <= LV.L.Max_Columns
      and then Long_Long_Integer (G.Total_Rows)
               * Long_Long_Integer (G.Encoded_Len)
               <= Max_Tableau);

   -------------------------------------------------------------------
   --  The encoder (ligero/reed_solomon.rs)
   -------------------------------------------------------------------

   --  encode_row: the row on the first K columns (the identity part of
   --  the Lagrange matrix), the Lagrange evaluation on the others, T
   --  the table of Lagrange.Build for K and the parity columns K ..
   --  NCOL - 1.
   procedure Encode_Row
     (Row : Element_Array;
      T   : Table;
      Enc : out Element_Array)
   with
     Global => null,
     Pre    =>
       Row'First = 0 and then Row'Length in 1 .. LV.L.Max_K
       and then T'First (1) = 0 and then T'Last (1) = Row'Last
       and then T'First (2) = 0
       and then Enc'First = 0 and then Enc'Length = Row'Length + T'Length (2),
     Post   =>
       (Proof_Only =>
          (for all X in 0 .. Row'Last => Same (Enc (X), Row (X)))
          and then
          (for all X in Row'Length .. Enc'Last =>
             Same (Enc (X),
                   LV.L.Dot_Ref (LV.L.Element_Array (Row), T,
                                 X - Row'Length, Row'Length))));

   -------------------------------------------------------------------
   --  The commitment (ligero/prover.rs commit)
   -------------------------------------------------------------------

   type Tableau is array (Natural range <>, Natural range <>) of Element;

   subtype Leaf_Index is Natural range 0 .. Merkle.Max_Leaves - 1;

   --  What the prover keeps after commit for the proof (Section 4.4,
   --  block 5): the tableau, the nonces, the Merkle heap (root at node
   --  1), the two Lagrange tables over the parity columns.
   type Commitment
     (Row_Last, Col_Last      : Index;
      Leaf_Last               : Leaf_Index;
      Heap_Last               : Merkle.Node_Index;
      Block_Last, Dblock_Last : Index;
      Par_B_Last, Par_D_Last  : Index)
   is record
      Tab      : Tableau (0 .. Row_Last, 0 .. Col_Last);
      Nonces   : Nonce_Array (0 .. Leaf_Last);
      Heap     : Merkle.Digest_Array (0 .. Heap_Last);
      T_Block  : Table (0 .. Block_Last, 0 .. Par_B_Last);
      T_Dblock : Table (0 .. Dblock_Last, 0 .. Par_D_Last);
      Root     : Digest;
   end record;

   type Commitment_Access is access Commitment;

   function Com_Shape (Com : Commitment; G : Valid_Geometry) return Boolean
   is
     (Com.Row_Last + 1 = G.Total_Rows
      and then Com.Col_Last + 1 = G.Encoded_Len
      and then Com.Leaf_Last + 1 = Num_Leaves (G)
      and then Com.Heap_Last + 1 = 2 * Num_Leaves (G)
      and then Com.Block_Last + 1 = G.Block_Len
      and then Com.Dblock_Last + 1 = G.Dblock_Len
      and then Com.Par_B_Last + 1 = G.Encoded_Len - G.Block_Len
      and then Com.Par_D_Last + 1 = G.Encoded_Len - G.Dblock_Len);

   --  The witness index of hand H (x, y, z) of a triple.
   function Sel (T : Lqc_Triple; H : Natural) return Natural is
     (case H is when 0 => T.X, when 1 => T.Y, when others => T.Z)
   with Global => null;

   --  commit: W the witness vector (the private inputs, then the
   --  pads), Lqc its quadratic constraints, Sfb the subfield boundary
   --  within W (the circuit's less the public inputs). Ok is False only
   --  when a Lagrange denominator has no inverse (Lagrange.Build), and
   --  Com is then null; otherwise Com is the fresh commitment, to be
   --  released with Free.
   procedure Commit
     (G   : Valid_Geometry;
      W   : Element_Array;
      Lqc : Lqc_Array;
      Sfb : Natural;
      Com : out Commitment_Access;
      Ok  : out Boolean)
   with
     Always_Terminates => not Sampling_Rejects,
     Pre    =>
       Prover_Fits (G)
       and then W'First = 0 and then W'Length = G.Num_Witnesses
       and then Lqc'First = 0 and then Lqc'Last < Max_Quads
       and then G.Num_Quad_Rows
                = (Lqc'Length + G.Witnesses_Per_Row - 1)
                  / G.Witnesses_Per_Row
       and then LV.Lqc_In_Range (Lqc, W'Length),
     Post   =>
       (if Ok then Com /= null and then Com_Shape (Com.all, G)
                   and then Com.Root = Com.Heap (1)
        else Com = null);

   procedure Free (Com : in out Commitment_Access) with
     Global => null,
     Post   => Com = null;

   -------------------------------------------------------------------
   --  The proof (ligero/prover.rs prove, Section 4.4)
   -------------------------------------------------------------------

   subtype Proof is LV.Proof;
   subtype Terms is LV.Terms;

   --  prove: on the live transcript, after the root, the statement and
   --  the sumcheck. Writes the statement hash, draws the challenges
   --  exactly as the verifier does (Draw_Challenges), computes y_ldt
   --  (the LDT row plus u_ldt times the witness and quadratic rows, on
   --  the first BLOCK columns), a_full (Build_A_Full of the verifier),
   --  y_dot (the linear row plus, row by row, the row times the
   --  encoding of its slice of a_full, on the first DBLOCK columns),
   --  y_quad (the quadratic row plus u_quad times z - x y, on the first
   --  DBLOCK columns), absorbs the four polynomials, chooses the columns
   --  (Choose_Columns), copies their nonces, opens the tree
   --  (Merkle.Open) and copies the queried columns row by row. Ok is
   --  False only when the transcript's generator passed its bound (ADR
   --  0028), and P is then not to be used.
   procedure Prove
     (G              : Valid_Geometry;
      Com            : Commitment;
      Lqc            : Lqc_Array;
      A              : Terms;
      B              : Element_Array;
      Statement_Hash : Byte_Array;
      P              : out Proof;
      Ok             : out Boolean)
   with
     Global            => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Always_Terminates => False,
     Pre               =>
       Prover_Fits (G) and then Com_Shape (Com, G)
       and then Lqc'First = 0 and then Lqc'Last in 0 .. Max_Quads - 1
       and then G.Num_Quad_Rows
                = (Lqc'Length + G.Witnesses_Per_Row - 1)
                  / G.Witnesses_Per_Row
       and then B'First = 0 and then B'Length >= 1
       and then B'Last < Natural'Last
       and then Statement_Hash'Length <= Transcript.Max_Payload
       and then LV.Terms_In_Range (A, LV.Vector_Len (G), B'Length)
       and then LV.Lqc_In_Range (Lqc, LV.Vector_Len (G))
       and then P.Ldt_Last + 1 = G.Block_Len
       and then P.Linear_Last + 1 = G.Dblock_Len
       and then P.Low_Last + 1 = G.Num_Queries
       and then P.High_Last + 1 = G.Dblock_Len - G.Block_Len
       and then P.Nonce_Last + 1 = G.Num_Queries
       and then P.Col_Last + 1 = LV.LP.Opened (G)
       and then P.Path_Last + 1 = 2 * Num_Leaves (G),
     Post              =>
       LV.LP.Shape (P, G)
       and then (if Ok then not Transcript.Is_Exhausted);

end Ligero_Prover;
