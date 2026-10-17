--  Ligero_Verifier: the Ligero verification procedure of draft Section
--  4.5 (LigeroVerifier::verify of ligero/verifier.rs at d5e6be7), in
--  the reference's order: the statement hash absorbed, the geometry,
--  the length checks, the challenges u_ldt, alphal, alphaq, u_quad,
--  the four response polynomials absorbed as element slices, the
--  column indices chosen, then verify_merkle, verify_ldt, verify_dot
--  with its sum check, verify_quad. Generic over the stage 4 transcript
--  glue of a field (sampling, element frames), the proof record and
--  the Lagrange tables of the same field.
--
--  Each step is a visible subprogram, so that a harness can run them
--  in the reference's order and compare every intermediate value with
--  a recording of the upstream verifier (tier 3 of ADR 0040); Verify
--  composes them. The two tables of Reed-Solomon values at the queried
--  columns (dimension BLOCK for the low-degree test and the constraint
--  rows, DBLOCK for the linear and quadratic polynomials) are built
--  once (ADR 0036) and the four tests read them.
--
--  Vocabulary of algebra/blas.rs: Axpy (y += a x), Vaxpy (y += a .* x),
--  Dot (sum of a .* b), Dot1 (sum of a), executable with their
--  formulas as postconditions; the tests are stated against the
--  recursive references Ldt_Ref, Lin_Ref and Quad_Ref, which
--  transcribe the loops of verify_ldt, verify_dot and verify_quad at
--  one queried column, row by row in the reference's order.
--
--  Documentation: docs/guide/05-ligero.md. Decisions: ADR 0035
--  (scope, the order), 0036 (the tables), 0037 (Checked_Inv behind
--  Matrix_Failed), 0038 (Gold: the four tests structural, the verifier
--  Silver with proved shape), 0039 (sizes, the status); frame: ADR
--  0023, 0024, 0031. Index: docs/adr/README.md.
--
--  Proof status (per instance). Proof-only contracts (Proof_Levels).
--    Axpy, Vaxpy, Dot, Dot1 : Gold, their formulas.
--    Verify_LDT, Verify_Dot, Verify_Quad : Gold, structural (ADR 0023):
--                       the combination of the opened columns at every
--                       queried column is Same as its reference, the
--                       polynomial side is the table evaluation, the
--                       sum check is Dot1 and Dot, and the status is the
--                       comparison of the two.
--    Build_A_Full     : Silver; the constraint vector a_full of
--                       verify_dot (the terms accumulated, then the
--                       quadratic copies), tested on the recordings.
--    Draw_Challenges, Absorb_Polynomials, Choose_Columns, Verify_Merkle,
--    Build_Tables     : Silver with proved shape; Absorb_Polynomials is
--                       Gold on its frames (the four slices, as in
--                       Sumcheck_Transcript); Choose_Columns has the
--                       distinct indices below the leaf count.
--    Verify           : Silver with proved shape; the status is one of
--                       the listed values, Exhausted exactly when the
--                       generator ran out.
--  Soundness is the paper's theorem, out of scope (ADR 0035).
--
--  Sizes (ADR 0047): the working set of Verify (the challenges, the
--  chosen columns, the two Lagrange tables, the evaluation vectors of
--  the tests, the constraint vector of the linear test) is one record
--  sized by the geometry, allocated on the heap for the duration of
--  Verify under SPARK's ownership rules and freed on every path.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0037.
--  Public data only.

pragma SPARK_Mode (On);

with Bytes;            use Bytes;
with Proof_Levels;
with Transcript;
with Merkle;
with Ligero_Geometry;  use Ligero_Geometry;
with Verifier_Status;  use Verifier_Status;
with Sumcheck_Transcript;
with Ligero_Proof;
with Lagrange;

generic
   with package ST is new Sumcheck_Transcript (<>);
   with package LP is new Ligero_Proof (SA => ST.SA);
   with package L is new Lagrange (F => ST.SA.F);
package Ligero_Verifier is

   --  The field's operators, as Lagrange uses them (the algebra's are
   --  wrappers of the same functions); the algebra's array type.
   use ST.SA.F;
   use LP;
   use type L.Element_Array;
   use type ST.SA.Element_Array;

   subtype Element is ST.SA.Element;
   subtype Element_Array is ST.SA.Element_Array;
   subtype Index is ST.SA.Index;

   --  Of the field, named here because the status parameter St of the
   --  verifier hides the package ST.
   Max_Eval_Point : constant Natural := ST.SA.F.Max_Eval_Point;
   subtype Proof is LP.Proof;
   subtype Terms is ST.SV.Ligero_Terms;
   subtype Lqc_Array is ST.SV.Lqc_Array;
   subtype Column_Indices is Transcript.Index_Array;
   subtype Digest is Merkle.Digest;

   ----------------------------------------------------------------------
   --  Shapes
   ----------------------------------------------------------------------

   --  NQW * WR, the length of the constraint vector a_full: one entry
   --  per witness slot of the NQW rows.
   function Vector_Len (G : Valid_Geometry) return Natural is
     (Num_Wq_Rows (G) * G.Witnesses_Per_Row);

   --  The constraint vector has a slot for every witness.
   procedure Lemma_Vector_Len_Covers (G : Valid_Geometry) with
     Ghost, Global => null,
     Post => Vector_Len (G) >= G.Num_Witnesses;

   function Vec_Shape (V : Element_Array; N : Natural) return Boolean is
     (V'First = 0 and then V'Length = N);

   --  A table of dimension K at the NREQ queried columns.
   function Table_Shape
     (T : L.Table; K : Positive; G : Valid_Geometry) return Boolean
   is
     (T'First (1) = 0 and then T'Last (1) = K - 1
      and then T'First (2) = 0 and then T'Last (2) = G.Num_Queries - 1);

   --  NREQ distinct indices below NCOL - DBLOCK (the output of choose).
   function Columns_Shape
     (Idx : Column_Indices; G : Valid_Geometry) return Boolean
   is
     (Idx'First = 0 and then Idx'Last = G.Num_Queries - 1
      and then (for all K in Idx'Range => Idx (K) < Num_Leaves (G))
      and then
        (for all K in Idx'Range =>
           (for all K2 in Idx'Range =>
              (if K /= K2 then Idx (K) /= Idx (K2)))));

   --  Every term names a witness slot and a constraint.
   function Terms_In_Range
     (A : Terms; Slots : Natural; NL : Natural) return Boolean
   is
     (for all K in 0 .. A.Count - 1 =>
        A.Witness (K) < Slots and then A.Constraint (K) < NL);

   function Lqc_In_Range (Lqc : Lqc_Array; Slots : Natural) return Boolean is
     (for all Q in Lqc'Range =>
        Lqc (Q).X < Slots and then Lqc (Q).Y < Slots
        and then Lqc (Q).Z < Slots);

   ----------------------------------------------------------------------
   --  algebra/blas.rs
   ----------------------------------------------------------------------

   --  y (i) += a * x (i).
   procedure Axpy (Y : in out Element_Array; X : Element_Array; A : Element)
   with
     Global => null,
     Pre    => Y'Length = X'Length,
     Post   =>
       (Proof_Only =>
          (for all I in Y'Range =>
             Same (Y (I), Y'Old (I) + A * X (X'First + (I - Y'First)))));

   --  y (i) += a (i) * x (i).
   procedure Vaxpy (Y : in out Element_Array; X, A : Element_Array) with
     Global => null,
     Pre    => Y'Length = X'Length and then Y'Length = A'Length,
     Post   =>
       (Proof_Only =>
          (for all I in Y'Range =>
             Same (Y (I),
                   Y'Old (I)
                   + A (A'First + (I - Y'First))
                     * X (X'First + (I - Y'First)))));

   --  The sum over i < N of A (i) * B (i), from Zero, i ascending.
   function Dot_Ref (A, B : Element_Array; N : Natural) return Element is
     (if N = 0 then Zero
      else Dot_Ref (A, B, N - 1) + A (A'First + N - 1) * B (B'First + N - 1))
   with Ghost              => Proof_Only,
        Annotate           =>
          (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre                => A'Length = B'Length and then N <= A'Length,
        Subprogram_Variant => (Decreases => N);

   function Dot (A, B : Element_Array) return Element with
     Global => null,
     Pre    => A'Length = B'Length,
     Post   => (Proof_Only => Same (Dot'Result, Dot_Ref (A, B, A'Length)));

   --  The sum over i < N of A (i), from Zero, i ascending.
   function Sum_Ref (A : Element_Array; N : Natural) return Element is
     (if N = 0 then Zero else Sum_Ref (A, N - 1) + A (A'First + N - 1))
   with Ghost              => Proof_Only,
        Annotate           =>
          (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre                => N <= A'Length,
        Subprogram_Variant => (Decreases => N);

   function Dot1 (A : Element_Array) return Element with
     Global => null,
     Post   => (Proof_Only => Same (Dot1'Result, Sum_Ref (A, A'Length)));

   ----------------------------------------------------------------------
   --  The challenges (ligero/common.rs gen_uldt, gen_alphal,
   --  gen_alphaq, gen_uquad)
   ----------------------------------------------------------------------

   --  u_ldt: NQW draws; alphal: NL, one per linear constraint; alphaq:
   --  three per quadratic triple, triple q at 3 q .. 3 q + 2; u_quad:
   --  one per quadratic row. In that order.
   type Challenges (Ldt_Last, Alphal_Last, Alphaq_Last, Quad_Last : Index)
   is record
      U_Ldt  : Element_Array (0 .. Ldt_Last);
      Alphal : Element_Array (0 .. Alphal_Last);
      Alphaq : Element_Array (0 .. Alphaq_Last);
      U_Quad : Element_Array (0 .. Quad_Last);
   end record;

   --  (The shapes of out parameters are stated on their discriminants
   --  and attributes directly: a function call on an out parameter in
   --  a precondition reads it, which flow analysis rejects.)
   procedure Draw_Challenges
     (G  : Valid_Geometry;
      NL : Positive;
      NQ : Positive;
      Ch : out Challenges)
   with
     Global            => (In_Out => Transcript.State),
     Always_Terminates => not ST.SA.F.Sampling_Rejects,
     Pre               =>
       Num_Wq_Rows (G) >= 1 and then G.Num_Quad_Rows >= 1
       and then NQ <= Max_Quads
       and then Ch.Ldt_Last + 1 = Num_Wq_Rows (G)
       and then Ch.Alphal_Last + 1 = NL
       and then Ch.Alphaq_Last + 1 = 3 * NQ
       and then Ch.Quad_Last + 1 = G.Num_Quad_Rows,
     Post              =>
       Transcript.Is_Exhausted'Old <= Transcript.Is_Exhausted;

   --  The four polynomials, each as one element slice frame (the
   --  slice head then the elements, ST.Elements_Frame).
   function Poly_Frame (S : Byte_Seq; Es : Element_Array) return Byte_Seq is
     (ST.Elements_Frame
        (Transcript.Slice_Header (S, Es'Length), Es, Es'Length))
   with Ghost => SPARKlib_Full;

   procedure Absorb_Polynomials (G : Valid_Geometry; P : Proof) with
     Global => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Pre    => Fits (G) and then Shape (P, G),
     Post   =>
       (SPARKlib_Full =>
          Transcript.Is_Exhausted'Old <= Transcript.Is_Exhausted
          and then Byte_Seqs.Logical_Eq
            (Transcript.Absorbed,
             Poly_Frame
               (Poly_Frame
                  (Poly_Frame
                     (Poly_Frame (Transcript.Absorbed'Old, P.Ldt_Poly),
                      P.Linear_Poly),
                   P.Quad_Low),
                P.Quad_High)));

   --  choose (NCOL - DBLOCK, NREQ).
   procedure Choose_Columns (G : Valid_Geometry; Idx : out Column_Indices)
   with
     Global            => (In_Out => Transcript.State),
     Always_Terminates => False,
     Pre               => Idx'First = 0 and then Idx'Last = G.Num_Queries - 1,
     Post              =>
       Transcript.Is_Exhausted'Old <= Transcript.Is_Exhausted
       and then Columns_Shape (Idx, G);

   ----------------------------------------------------------------------
   --  verify_merkle
   ----------------------------------------------------------------------

   --  The leaf of the R-th opened column: SHA-256 of its nonce followed
   --  by its NROW elements in the full encoding.
   function Leaf_Digest
     (G : Valid_Geometry; P : Proof; R : Natural) return Digest
   with
     Global => null,
     Pre    => Fits (G) and then Shape (P, G) and then R < G.Num_Queries;

   procedure Verify_Merkle
     (G    : Valid_Geometry;
      Root : Digest;
      P    : Proof;
      Idx  : Column_Indices;
      Ok   : out Boolean)
   with
     Global => null,
     Pre    => Fits (G) and then Shape (P, G) and then Columns_Shape (Idx, G);

   ----------------------------------------------------------------------
   --  The tables
   ----------------------------------------------------------------------

   --  The queried columns of the code: DBLOCK + idx (k).
   function Query_Columns
     (G : Valid_Geometry; Idx : Column_Indices) return L.Column_Array
   with
     Global => null,
     Pre    => Columns_Shape (Idx, G),
     Post   =>
       Query_Columns'Result'First = 0
       and then Query_Columns'Result'Length = G.Num_Queries
       and then (for all K in Query_Columns'Result'Range =>
                   Query_Columns'Result (K) = G.Dblock_Len + Idx (K));

   --  Both tables; Ok is False when a denominator had no checked
   --  inverse (ADR 0037).
   procedure Build_Tables
     (G        : Valid_Geometry;
      Idx      : Column_Indices;
      T_Block  : out L.Table;
      T_Dblock : out L.Table;
      Ok       : out Boolean)
   with
     Global => null,
     Pre    =>
       Columns_Shape (Idx, G)
       and then G.Encoded_Len - 1 <= Max_Eval_Point
       and then T_Block'First (1) = 0
       and then T_Block'Last (1) = G.Block_Len - 1
       and then T_Block'First (2) = 0
       and then T_Block'Last (2) = G.Num_Queries - 1
       and then T_Dblock'First (1) = 0
       and then T_Dblock'Last (1) = G.Dblock_Len - 1
       and then T_Dblock'First (2) = 0
       and then T_Dblock'Last (2) = G.Num_Queries - 1;

   ----------------------------------------------------------------------
   --  verify_ldt
   ----------------------------------------------------------------------

   --  T [ILDT] + sum over i < N of u_ldt (i) T [IW + i], at queried
   --  column J, accumulated in the order of the axpy loop.
   function Ldt_Ref
     (P : Proof; G : Valid_Geometry; U : Element_Array; J, N : Natural)
      return Element
   is
     (if N = 0 then Col (P, G, Ldt_Row (G), J)
      else Ldt_Ref (P, G, U, J, N - 1)
           + U (N - 1) * Col (P, G, Witness_Row_Start (G) + N - 1, J))
   with Ghost              => Proof_Only,
        Annotate           =>
          (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre                => Fits (G) and then Shape (P, G)
                              and then J < G.Num_Queries
                              and then Vec_Shape (U, Num_Wq_Rows (G))
                              and then N <= Num_Wq_Rows (G),
        Subprogram_Variant => (Decreases => N);

   --  Yc the combination of the opened columns, Yp the low-degree
   --  polynomial at the queried columns; Ok their equality.
   procedure Verify_LDT
     (G       : Valid_Geometry;
      P       : Proof;
      U_Ldt   : Element_Array;
      T_Block : L.Table;
      Yc, Yp  : out Element_Array;
      Ok      : out Boolean)
   with
     Global => null,
     Pre    =>
       Fits (G) and then Shape (P, G)
       and then Vec_Shape (U_Ldt, Num_Wq_Rows (G))
       and then Table_Shape (T_Block, G.Block_Len, G)
       and then Yc'First = 0 and then Yc'Last = G.Num_Queries - 1
       and then Yp'First = 0 and then Yp'Last = G.Num_Queries - 1,
     Post   =>
       (Proof_Only =>
          (for all J in 0 .. G.Num_Queries - 1 =>
             Same (Yc (J), Ldt_Ref (P, G, U_Ldt, J, Num_Wq_Rows (G)))
             and then Same (Yp (J),
                            L.Dot_Ref (L.Element_Array (P.Ldt_Poly),
                                       T_Block, J, G.Block_Len)))
          and then Ok = (Yc = Yp));

   ----------------------------------------------------------------------
   --  verify_dot
   ----------------------------------------------------------------------

   --  The constraint vector a_full: for each term, a_full (witness) +=
   --  coeff * alphal (constraint); then for each quadratic triple q =
   --  (x, y, z) with copies at ax + q, ay + q, az + q (the three
   --  quadratic row blocks after the witness rows): a_full (ax + q) +=
   --  alphaq (3 q), a_full (x) -= alphaq (3 q), likewise y with 3 q + 1
   --  and z with 3 q + 2.
   procedure Build_A_Full
     (G      : Valid_Geometry;
      A      : Terms;
      Lqc    : Lqc_Array;
      Alphal : Element_Array;
      Alphaq : Element_Array;
      A_Full : out Element_Array)
   with
     Global => null,
     Pre    =>
       Lqc'First = 0
       and then Lqc'Last in 0 .. G.Num_Quad_Rows * G.Witnesses_Per_Row - 1
       and then Vec_Shape (Alphaq, 3 * (Lqc'Last + 1))
       and then Alphal'First = 0 and then Alphal'Length >= 1
       and then Terms_In_Range (A, Vector_Len (G), Alphal'Length)
       and then Lqc_In_Range (Lqc, Vector_Len (G))
       and then A_Full'First = 0
       and then A_Full'Last = Vector_Len (G) - 1;

   --  The offset of row I in a_full, I * WR, with the room for its WR
   --  entries (as Row_Off of the proof).
   function Slot_Off (G : Valid_Geometry; I : Natural) return Natural with
     Global => null,
     Pre    => I < Num_Wq_Rows (G),
     Post   =>
       Long_Long_Integer (Slot_Off'Result)
       = Long_Long_Integer (I) * Long_Long_Integer (G.Witnesses_Per_Row)
       and then Slot_Off'Result + G.Witnesses_Per_Row <= Vector_Len (G);

   --  Row I of a_full extended to BLOCK entries: NREQ zeros then its
   --  WR entries (a_ext of verify_dot).
   function Ext_Row
     (A_Full : Element_Array; G : Valid_Geometry; I : Natural)
      return L.Element_Array
   with
     Global => null,
     Pre    => Vec_Shape (A_Full, Vector_Len (G)) and then I < Num_Wq_Rows (G),
     Post   =>
       (Proof_Only =>
          Ext_Row'Result'First = 0
          and then Ext_Row'Result'Last = G.Block_Len - 1
          and then (for all K in 0 .. G.Num_Queries - 1 =>
                      Same (Ext_Row'Result (K), Zero))
          and then (for all K in 0 .. G.Witnesses_Per_Row - 1 =>
                      Same (Ext_Row'Result (G.Num_Queries + K),
                            A_Full (Slot_Off (G, I) + K))));

   --  The encoding of row I of a_full at queried column J.
   function Row_Encoding
     (A_Full  : Element_Array;
      G       : Valid_Geometry;
      I       : Natural;
      T_Block : L.Table;
      J       : Natural)
      return Element
   is
     (L.Evaluate (Ext_Row (A_Full, G, I), T_Block, J))
   with Pre => Vec_Shape (A_Full, Vector_Len (G)) and then I < Num_Wq_Rows (G)
               and then Table_Shape (T_Block, G.Block_Len, G)
               and then J < G.Num_Queries;

   --  T [IDOT] + sum over i < N of enc_i T [IW + i] at queried column J,
   --  in the order of the vaxpy loop.
   function Lin_Ref
     (P       : Proof;
      G       : Valid_Geometry;
      A_Full  : Element_Array;
      T_Block : L.Table;
      J, N    : Natural)
      return Element
   is
     (if N = 0 then Col (P, G, Linear_Row (G), J)
      else Lin_Ref (P, G, A_Full, T_Block, J, N - 1)
           + Row_Encoding (A_Full, G, N - 1, T_Block, J)
             * Col (P, G, Witness_Row_Start (G) + N - 1, J))
   with Ghost              => Proof_Only,
        Annotate           =>
          (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre                => Fits (G) and then Shape (P, G)
                              and then J < G.Num_Queries
                              and then Vec_Shape (A_Full, Vector_Len (G))
                              and then Table_Shape (T_Block, G.Block_Len, G)
                              and then N <= Num_Wq_Rows (G),
        Subprogram_Variant => (Decreases => N);

   --  Yc the combination, Yp the linear polynomial at the queried
   --  columns; Want_Dot = dot (b, alphal), Proof_Dot = dot1 of the WR
   --  middle entries of the linear polynomial. St is Linear_Failed when
   --  Yc /= Yp, else Linear_Sum_Failed when Proof_Dot + Want_Dot /= 0,
   --  else Ok.
   procedure Verify_Dot
     (G         : Valid_Geometry;
      B         : Element_Array;
      P         : Proof;
      A_Full    : Element_Array;
      Alphal    : Element_Array;
      T_Block   : L.Table;
      T_Dblock  : L.Table;
      Yc, Yp    : out Element_Array;
      Want_Dot  : out Element;
      Proof_Dot : out Element;
      St        : out Status)
   with
     Global => null,
     Pre    =>
       Fits (G) and then Shape (P, G)
       and then B'First = 0 and then Alphal'First = 0
       and then B'Length = Alphal'Length
       and then Vec_Shape (A_Full, Vector_Len (G))
       and then Table_Shape (T_Block, G.Block_Len, G)
       and then Table_Shape (T_Dblock, G.Dblock_Len, G)
       and then Yc'First = 0 and then Yc'Last = G.Num_Queries - 1
       and then Yp'First = 0 and then Yp'Last = G.Num_Queries - 1,
     Post   =>
       (Proof_Only =>
          (for all J in 0 .. G.Num_Queries - 1 =>
             Same (Yc (J), Lin_Ref (P, G, A_Full, T_Block, J, Num_Wq_Rows (G)))
             and then Same (Yp (J),
                            L.Dot_Ref (L.Element_Array (P.Linear_Poly),
                                       T_Dblock, J, G.Dblock_Len)))
          and then Same (Want_Dot, Dot_Ref (B, Alphal, B'Length))
          and then Same
                     (Proof_Dot,
                      Sum_Ref
                        (P.Linear_Poly
                           (G.Num_Queries
                            .. G.Num_Queries + G.Witnesses_Per_Row - 1),
                         G.Witnesses_Per_Row))
          and then St = (if Yc /= Yp then Linear_Failed
                         elsif Proof_Dot + Want_Dot /= Zero
                         then Linear_Sum_Failed
                         else Ok));

   ----------------------------------------------------------------------
   --  verify_quad
   ----------------------------------------------------------------------

   --  T [IQD] + sum over i < N of u_quad (i) (z_i - x_i y_i) at queried
   --  column J, in the order of the axpy loop.
   function Quad_Ref
     (P : Proof; G : Valid_Geometry; U : Element_Array; J, N : Natural)
      return Element
   is
     (if N = 0 then Col (P, G, Quad_Row (G), J)
      else Quad_Ref (P, G, U, J, N - 1)
           + U (N - 1)
             * (Col (P, G, Quad_Z_Row_Start (G) + N - 1, J)
                - Col (P, G, Quad_X_Row_Start (G) + N - 1, J)
                  * Col (P, G, Quad_Y_Row_Start (G) + N - 1, J)))
   with Ghost              => Proof_Only,
        Annotate           =>
          (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre                => Fits (G) and then Shape (P, G)
                              and then J < G.Num_Queries
                              and then Vec_Shape (U, G.Num_Quad_Rows)
                              and then N <= G.Num_Quad_Rows,
        Subprogram_Variant => (Decreases => N);

   --  The quadratic polynomial: quad_poly_low, WR zeros, quad_poly_high.
   function Quad_Poly (G : Valid_Geometry; P : Proof) return L.Element_Array
   with
     Global => null,
     Pre    => Fits (G) and then Shape (P, G),
     Post   =>
       (Proof_Only =>
          Quad_Poly'Result'First = 0
          and then Quad_Poly'Result'Last = G.Dblock_Len - 1
          and then (for all K in 0 .. G.Num_Queries - 1 =>
                      Same (Quad_Poly'Result (K), P.Quad_Low (K)))
          and then (for all K in G.Num_Queries .. G.Block_Len - 1 =>
                      Same (Quad_Poly'Result (K), Zero))
          and then (for all K in 0 .. G.Dblock_Len - G.Block_Len - 1 =>
                      Same (Quad_Poly'Result (G.Block_Len + K),
                            P.Quad_High (K))));

   procedure Verify_Quad
     (G        : Valid_Geometry;
      P        : Proof;
      U_Quad   : Element_Array;
      T_Dblock : L.Table;
      Yc, Yp   : out Element_Array;
      Ok       : out Boolean)
   with
     Global => null,
     Pre    =>
       Fits (G) and then Shape (P, G)
       and then Vec_Shape (U_Quad, G.Num_Quad_Rows)
       and then Table_Shape (T_Dblock, G.Dblock_Len, G)
       and then Yc'First = 0 and then Yc'Last = G.Num_Queries - 1
       and then Yp'First = 0 and then Yp'Last = G.Num_Queries - 1,
     Post   =>
       (Proof_Only =>
          (for all J in 0 .. G.Num_Queries - 1 =>
             Same (Yc (J), Quad_Ref (P, G, U_Quad, J, G.Num_Quad_Rows))
             and then Same (Yp (J),
                            L.Dot_Ref (Quad_Poly (G, P), T_Dblock, J,
                                       G.Dblock_Len)))
          and then Ok = (Yc = Yp));

   ----------------------------------------------------------------------
   --  verify
   ----------------------------------------------------------------------

   --  The whole procedure: NW the number of witnesses, B the constant
   --  vector b (one entry per linear constraint), Root the commitment,
   --  A the constraint terms, Lqc the quadratic triples. The transcript
   --  continues from its current state (the complete verifier has
   --  absorbed the root, the statement and the sumcheck). Statuses:
   --  Queried_Columns_Length and Polynomial_Lengths when P is not of
   --  the geometry's shape; Exhausted when the generator ran out during
   --  the draws; Merkle_Failed, Matrix_Failed, LDT_Failed,
   --  Linear_Failed, Linear_Sum_Failed, Quadratic_Failed from the test
   --  that failed, in order; Ok.
   procedure Verify
     (Cfg            : Config;
      NW             : Natural;
      B              : Element_Array;
      Root           : Digest;
      P              : Proof;
      A              : Terms;
      Statement_Hash : Byte_Array;
      Lqc            : Lqc_Array;
      St             : out Status)
   with
     Global            => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Always_Terminates => False,
     Pre               =>
       Valid (Cfg)
       and then NW in 1 .. Max_Witnesses
       and then Lqc'First = 0 and then Lqc'Last in 0 .. Max_Quads - 1
       and then B'First = 0 and then B'Length >= 1
       and then Statement_Hash'Length <= Transcript.Max_Payload
       and then not Transcript.Is_Exhausted
       and then Fits (Make (Cfg, NW, Lqc'Last + 1))
       and then Terms_In_Range
                  (A, Vector_Len (Make (Cfg, NW, Lqc'Last + 1)), B'Length)
       and then Lqc_In_Range
                  (Lqc, Vector_Len (Make (Cfg, NW, Lqc'Last + 1))),
     Post              =>
       St in Ok | Queried_Columns_Length | Polynomial_Lengths | Exhausted
             | Merkle_Failed | Matrix_Failed | LDT_Failed | Linear_Failed
             | Linear_Sum_Failed | Quadratic_Failed
       and then (if St = Exhausted then Transcript.Is_Exhausted)
       and then (if St in Ok | Merkle_Failed | Matrix_Failed | LDT_Failed
                       | Linear_Failed | Linear_Sum_Failed | Quadratic_Failed
                 then not Transcript.Is_Exhausted)
       and then (if St in Queried_Columns_Length | Polynomial_Lengths
                 then not Shape (P, Make (Cfg, NW, Lqc'Last + 1)));

end Ligero_Verifier;
