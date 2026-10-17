pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;
with Sha256;
with SPARK.Lemmas.Integer_Arithmetic;

package body Ligero_Verifier is

   procedure Lemma_Vector_Len_Covers (G : Valid_Geometry) is
   begin
      Lemma_Rows_Cover (G);
      SPARK.Lemmas.Integer_Arithmetic.Lemma_Mult_Is_Monotonic
        (G.Num_Witness_Rows, Num_Wq_Rows (G), G.Witnesses_Per_Row);
   end Lemma_Vector_Len_Covers;

   function Slot_Off (G : Valid_Geometry; I : Natural) return Natural is
   begin
      SPARK.Lemmas.Integer_Arithmetic.Lemma_Mult_Is_Monotonic
        (I + 1, Num_Wq_Rows (G), G.Witnesses_Per_Row);
      return I * G.Witnesses_Per_Row;
   end Slot_Off;

   function Ext_Row
     (A_Full : Element_Array; G : Valid_Geometry; I : Natural)
      return L.Element_Array
   is
      NQ   : constant Natural := G.Num_Queries;
      WR   : constant Natural := G.Witnesses_Per_Row;
      Base : constant Natural := Slot_Off (G, I);
      R    : L.Element_Array (0 .. G.Block_Len - 1) := [others => Zero];
   begin
      for K in 0 .. WR - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all K2 in 0 .. NQ - 1 => Same (R (K2), Zero))
              and then (for all K2 in 0 .. K - 1 =>
                          Same (R (NQ + K2), A_Full (Base + K2))));
         R (NQ + K) := A_Full (Base + K);
      end loop;
      return R;
   end Ext_Row;

   function Quad_Poly (G : Valid_Geometry; P : Proof) return L.Element_Array
   is
      NQ : constant Natural := G.Num_Queries;
      BL : constant Natural := G.Block_Len;
      R  : L.Element_Array (0 .. G.Dblock_Len - 1) := [others => Zero];
   begin
      for K in 0 .. NQ - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all K2 in 0 .. K - 1 => Same (R (K2), P.Quad_Low (K2)))
              and then (for all K2 in K .. R'Last => Same (R (K2), Zero)));
         R (K) := P.Quad_Low (K);
      end loop;
      for K in 0 .. G.Dblock_Len - BL - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all K2 in 0 .. NQ - 1 => Same (R (K2), P.Quad_Low (K2)))
              and then (for all K2 in NQ .. BL - 1 => Same (R (K2), Zero))
              and then (for all K2 in 0 .. K - 1 =>
                          Same (R (BL + K2), P.Quad_High (K2))));
         R (BL + K) := P.Quad_High (K);
      end loop;
      return R;
   end Quad_Poly;

   ----------------------------------------------------------------------
   --  The hidden references, one step at a time
   ----------------------------------------------------------------------

   procedure Lemma_Dot_Zero (A, B : Element_Array) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => A'Length = B'Length,
     Post   => Same (Dot_Ref (A, B, 0), Zero)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Dot_Ref);
   begin
      null;
   end Lemma_Dot_Zero;

   procedure Lemma_Dot_Step (A, B : Element_Array; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => A'Length = B'Length and then N < A'Length,
     Post   => Same (Dot_Ref (A, B, N + 1),
                     Dot_Ref (A, B, N) + A (A'First + N) * B (B'First + N))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Dot_Ref);
   begin
      null;
   end Lemma_Dot_Step;

   procedure Lemma_Sum_Zero (A : Element_Array) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (Sum_Ref (A, 0), Zero)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Sum_Ref);
   begin
      null;
   end Lemma_Sum_Zero;

   procedure Lemma_Sum_Step (A : Element_Array; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N < A'Length,
     Post   => Same (Sum_Ref (A, N + 1), Sum_Ref (A, N) + A (A'First + N))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Sum_Ref);
   begin
      null;
   end Lemma_Sum_Step;

   procedure Lemma_Ldt_Zero
     (P : Proof; G : Valid_Geometry; U : Element_Array)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Fits (G) and then Shape (P, G)
               and then Vec_Shape (U, Num_Wq_Rows (G)),
     Post   =>
       (for all J in 0 .. G.Num_Queries - 1 =>
          Same (Ldt_Ref (P, G, U, J, 0), Col (P, G, Ldt_Row (G), J)))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Ldt_Ref);
   begin
      null;
   end Lemma_Ldt_Zero;

   procedure Lemma_Ldt_Step
     (P : Proof; G : Valid_Geometry; U : Element_Array; I : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Fits (G) and then Shape (P, G)
               and then Vec_Shape (U, Num_Wq_Rows (G))
               and then I < Num_Wq_Rows (G),
     Post   =>
       (for all J in 0 .. G.Num_Queries - 1 =>
          Same (Ldt_Ref (P, G, U, J, I + 1),
                Ldt_Ref (P, G, U, J, I)
                + U (I) * Col (P, G, Witness_Row_Start (G) + I, J)))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Ldt_Ref);
   begin
      null;
   end Lemma_Ldt_Step;

   procedure Lemma_Lin_Zero
     (P       : Proof;
      G       : Valid_Geometry;
      A_Full  : Element_Array;
      T_Block : L.Table)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Fits (G) and then Shape (P, G)
               and then Vec_Shape (A_Full, Vector_Len (G))
               and then Table_Shape (T_Block, G.Block_Len, G),
     Post   =>
       (for all J in 0 .. G.Num_Queries - 1 =>
          Same (Lin_Ref (P, G, A_Full, T_Block, J, 0),
                Col (P, G, Linear_Row (G), J)))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Lin_Ref);
   begin
      null;
   end Lemma_Lin_Zero;

   procedure Lemma_Lin_Step
     (P       : Proof;
      G       : Valid_Geometry;
      A_Full  : Element_Array;
      T_Block : L.Table;
      I       : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Fits (G) and then Shape (P, G)
               and then Vec_Shape (A_Full, Vector_Len (G))
               and then Table_Shape (T_Block, G.Block_Len, G)
               and then I < Num_Wq_Rows (G),
     Post   =>
       (for all J in 0 .. G.Num_Queries - 1 =>
          Same (Lin_Ref (P, G, A_Full, T_Block, J, I + 1),
                Lin_Ref (P, G, A_Full, T_Block, J, I)
                + Row_Encoding (A_Full, G, I, T_Block, J)
                  * Col (P, G, Witness_Row_Start (G) + I, J)))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Lin_Ref);
   begin
      null;
   end Lemma_Lin_Step;

   procedure Lemma_Quad_Zero
     (P : Proof; G : Valid_Geometry; U : Element_Array)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Fits (G) and then Shape (P, G)
               and then Vec_Shape (U, G.Num_Quad_Rows),
     Post   =>
       (for all J in 0 .. G.Num_Queries - 1 =>
          Same (Quad_Ref (P, G, U, J, 0), Col (P, G, Quad_Row (G), J)))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Quad_Ref);
   begin
      null;
   end Lemma_Quad_Zero;

   procedure Lemma_Quad_Step
     (P : Proof; G : Valid_Geometry; U : Element_Array; I : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Fits (G) and then Shape (P, G)
               and then Vec_Shape (U, G.Num_Quad_Rows)
               and then I < G.Num_Quad_Rows,
     Post   =>
       (for all J in 0 .. G.Num_Queries - 1 =>
          Same (Quad_Ref (P, G, U, J, I + 1),
                Quad_Ref (P, G, U, J, I)
                + U (I)
                  * (Col (P, G, Quad_Z_Row_Start (G) + I, J)
                     - Col (P, G, Quad_X_Row_Start (G) + I, J)
                       * Col (P, G, Quad_Y_Row_Start (G) + I, J))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Quad_Ref);
   begin
      null;
   end Lemma_Quad_Step;

   ----------------------------------------------------------------------
   --  algebra/blas.rs
   ----------------------------------------------------------------------

   procedure Axpy (Y : in out Element_Array; X : Element_Array; A : Element)
   is
   begin
      for I in Y'Range loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all K in Y'First .. I - 1 =>
                 Same (Y (K),
                       Y'Loop_Entry (K) + A * X (X'First + (K - Y'First))))
              and then
                (for all K in I .. Y'Last => Same (Y (K), Y'Loop_Entry (K))));
         Y (I) := Y (I) + A * X (X'First + (I - Y'First));
      end loop;
   end Axpy;

   procedure Vaxpy (Y : in out Element_Array; X, A : Element_Array) is
   begin
      for I in Y'Range loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all K in Y'First .. I - 1 =>
                 Same (Y (K),
                       Y'Loop_Entry (K)
                       + A (A'First + (K - Y'First))
                         * X (X'First + (K - Y'First))))
              and then
                (for all K in I .. Y'Last => Same (Y (K), Y'Loop_Entry (K))));
         Y (I) := Y (I)
                  + A (A'First + (I - Y'First)) * X (X'First + (I - Y'First));
      end loop;
   end Vaxpy;

   function Dot (A, B : Element_Array) return Element is
      Sum : Element := Zero;
   begin
      Lemma_Dot_Zero (A, B);
      for N in 0 .. A'Length - 1 loop
         pragma Loop_Invariant (Proof_Only => Same (Sum, Dot_Ref (A, B, N)));
         Lemma_Dot_Step (A, B, N);
         Sum := Sum + A (A'First + N) * B (B'First + N);
      end loop;
      return Sum;
   end Dot;

   function Dot1 (A : Element_Array) return Element is
      Sum : Element := Zero;
   begin
      Lemma_Sum_Zero (A);
      for N in 0 .. A'Length - 1 loop
         pragma Loop_Invariant (Proof_Only => Same (Sum, Sum_Ref (A, N)));
         Lemma_Sum_Step (A, N);
         Sum := Sum + A (A'First + N);
      end loop;
      return Sum;
   end Dot1;

   ----------------------------------------------------------------------
   --  The challenges
   ----------------------------------------------------------------------

   procedure Draw_Challenges
     (G  : Valid_Geometry;
      NL : Positive;
      NQ : Positive;
      Ch : out Challenges)
   is
      Ex0 : constant Boolean := Transcript.Is_Exhausted with Ghost;
   begin
      Ch := (Ldt_Last    => Ch.Ldt_Last,
             Alphal_Last => Ch.Alphal_Last,
             Alphaq_Last => Ch.Alphaq_Last,
             Quad_Last   => Ch.Quad_Last,
             U_Ldt       => [others => Zero],
             Alphal      => [others => Zero],
             Alphaq      => [others => Zero],
             U_Quad      => [others => Zero]);
      for I in Ch.U_Ldt'Range loop
         pragma Loop_Invariant (Ex0 <= Transcript.Is_Exhausted);
         ST.Sample (Ch.U_Ldt (I));
      end loop;
      for I in Ch.Alphal'Range loop
         pragma Loop_Invariant (Ex0 <= Transcript.Is_Exhausted);
         ST.Sample (Ch.Alphal (I));
      end loop;
      for I in Ch.Alphaq'Range loop
         pragma Loop_Invariant (Ex0 <= Transcript.Is_Exhausted);
         ST.Sample (Ch.Alphaq (I));
      end loop;
      for I in Ch.U_Quad'Range loop
         pragma Loop_Invariant (Ex0 <= Transcript.Is_Exhausted);
         ST.Sample (Ch.U_Quad (I));
      end loop;
   end Draw_Challenges;

   procedure Absorb_Polynomials (G : Valid_Geometry; P : Proof) is
   begin
      ST.Write_Element_Slice (P.Ldt_Poly);
      ST.Write_Element_Slice (P.Linear_Poly);
      ST.Write_Element_Slice (P.Quad_Low);
      ST.Write_Element_Slice (P.Quad_High);
   end Absorb_Polynomials;

   procedure Choose_Columns (G : Valid_Geometry; Idx : out Column_Indices)
   is
   begin
      Transcript.Choose (Num_Leaves (G), G.Num_Queries, Idx);
   end Choose_Columns;

   ----------------------------------------------------------------------
   --  verify_merkle
   ----------------------------------------------------------------------

   function Leaf_Digest
     (G : Valid_Geometry; P : Proof; R : Natural) return Digest
   is
      Ctx : Sha256.Context := Sha256.Initial;
   begin
      Sha256.Update (Ctx, P.Nonces (R));
      for Row in 0 .. G.Total_Rows - 1 loop
         Sha256.Update (Ctx, ST.SA.F.To_Bytes (Col (P, G, Row, R)));
      end loop;
      return Sha256.Digest (Ctx);
   end Leaf_Digest;

   procedure Verify_Merkle
     (G    : Valid_Geometry;
      Root : Digest;
      P    : Proof;
      Idx  : Column_Indices;
      Ok   : out Boolean)
   is
      Leaves : Merkle.Digest_Array (0 .. G.Num_Queries - 1) :=
        [others => [others => 0]];
   begin
      for K in Leaves'Range loop
         Leaves (K) := Leaf_Digest (G, P, K);
      end loop;
      Merkle.Verify
        (N       => Num_Leaves (G),
         Root    => Root,
         Indices => Merkle.Index_Array (Idx),
         Leaves  => Leaves,
         Path    => P.Path (0 .. P.Path_Count - 1),
         Ok      => Ok);
   end Verify_Merkle;

   ----------------------------------------------------------------------
   --  The tables
   ----------------------------------------------------------------------

   function Query_Columns
     (G : Valid_Geometry; Idx : Column_Indices) return L.Column_Array
   is
      Cols : L.Column_Array (0 .. G.Num_Queries - 1) := [others => 0];
   begin
      for K in Cols'Range loop
         pragma Loop_Invariant
           (for all K2 in 0 .. K - 1 => Cols (K2) = G.Dblock_Len + Idx (K2));
         Cols (K) := G.Dblock_Len + Idx (K);
      end loop;
      return Cols;
   end Query_Columns;

   procedure Build_Tables
     (G        : Valid_Geometry;
      Idx      : Column_Indices;
      T_Block  : out L.Table;
      T_Dblock : out L.Table;
      Ok       : out Boolean)
   is
      Cols  : constant L.Column_Array := Query_Columns (G, Idx);
      Inv_B : L.Element_Array (0 .. G.Block_Len - 1);
      Inv_D : L.Element_Array (0 .. G.Dblock_Len - 1);
      Ok2   : Boolean;
   begin
      T_Dblock := [others => [others => Zero]];
      L.Build (G.Block_Len, Cols, T_Block, Inv_B, Ok);
      if Ok then
         L.Build (G.Dblock_Len, Cols, T_Dblock, Inv_D, Ok2);
         Ok := Ok2;
      end if;
   end Build_Tables;

   ----------------------------------------------------------------------
   --  verify_ldt
   ----------------------------------------------------------------------

   procedure Verify_LDT
     (G       : Valid_Geometry;
      P       : Proof;
      U_Ldt   : Element_Array;
      T_Block : L.Table;
      Yc, Yp  : out Element_Array;
      Ok      : out Boolean)
   is
      NQ  : constant Natural := G.Num_Queries;
      Row : Natural;
   begin
      Yc := [others => Zero];
      Yp := [others => Zero];
      for J in 0 .. NQ - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all K in 0 .. J - 1 =>
                 Same (Yc (K), Col (P, G, Ldt_Row (G), K))));
         Yc (J) := Col (P, G, Ldt_Row (G), J);
      end loop;
      Lemma_Ldt_Zero (P, G, U_Ldt);
      for I in 0 .. Num_Wq_Rows (G) - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J in 0 .. NQ - 1 =>
                 Same (Yc (J), Ldt_Ref (P, G, U_Ldt, J, I))));
         Lemma_Ldt_Step (P, G, U_Ldt, I);
         Row := Row_Off (G, Witness_Row_Start (G) + I);
         Axpy (Yc, P.Columns (Row .. Row + NQ - 1), U_Ldt (I));
      end loop;
      for J in 0 .. NQ - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all K in 0 .. J - 1 =>
                 Same (Yp (K),
                       L.Dot_Ref (L.Element_Array (P.Ldt_Poly),
                                  T_Block, K, G.Block_Len))));
         Yp (J) := L.Evaluate (L.Element_Array (P.Ldt_Poly), T_Block, J);
      end loop;
      Ok := Yc = Yp;
   end Verify_LDT;

   ----------------------------------------------------------------------
   --  verify_dot
   ----------------------------------------------------------------------

   procedure Build_A_Full
     (G      : Valid_Geometry;
      A      : Terms;
      Lqc    : Lqc_Array;
      Alphal : Element_Array;
      Alphaq : Element_Array;
      A_Full : out Element_Array)
   is
      WR : constant Natural := G.Witnesses_Per_Row;
      Ax : constant Natural := G.Num_Witness_Rows * WR;
      Ay : constant Natural := Ax + G.Num_Quad_Rows * WR;
      Az : constant Natural := Ay + G.Num_Quad_Rows * WR;
      W  : Natural;
   begin
      A_Full := [others => Zero];
      for K in 0 .. A.Count - 1 loop
         W := A.Witness (K);
         A_Full (W) := A_Full (W) + A.Coeff (K) * Alphal (A.Constraint (K));
      end loop;
      for Q in Lqc'Range loop
         A_Full (Ax + Q)     := A_Full (Ax + Q) + Alphaq (3 * Q);
         A_Full (Lqc (Q).X)  := A_Full (Lqc (Q).X) - Alphaq (3 * Q);
         A_Full (Ay + Q)     := A_Full (Ay + Q) + Alphaq (3 * Q + 1);
         A_Full (Lqc (Q).Y)  := A_Full (Lqc (Q).Y) - Alphaq (3 * Q + 1);
         A_Full (Az + Q)     := A_Full (Az + Q) + Alphaq (3 * Q + 2);
         A_Full (Lqc (Q).Z)  := A_Full (Lqc (Q).Z) - Alphaq (3 * Q + 2);
      end loop;
   end Build_A_Full;

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
   is
      NQ  : constant Natural := G.Num_Queries;
      WR  : constant Natural := G.Witnesses_Per_Row;
      A_Q : Element_Array (0 .. NQ - 1) := [others => Zero];
      Row : Natural;
   begin
      Yc := [others => Zero];
      Yp := [others => Zero];
      for J in 0 .. NQ - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all K in 0 .. J - 1 =>
                 Same (Yc (K), Col (P, G, Linear_Row (G), K))));
         Yc (J) := Col (P, G, Linear_Row (G), J);
      end loop;
      Lemma_Lin_Zero (P, G, A_Full, T_Block);
      for I in 0 .. Num_Wq_Rows (G) - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J in 0 .. NQ - 1 =>
                 Same (Yc (J), Lin_Ref (P, G, A_Full, T_Block, J, I))));
         for J in 0 .. NQ - 1 loop
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all K in 0 .. J - 1 =>
                    Same (A_Q (K), Row_Encoding (A_Full, G, I, T_Block, K))));
            A_Q (J) := Row_Encoding (A_Full, G, I, T_Block, J);
         end loop;
         Lemma_Lin_Step (P, G, A_Full, T_Block, I);
         Row := Row_Off (G, Witness_Row_Start (G) + I);
         Vaxpy (Yc, P.Columns (Row .. Row + NQ - 1), A_Q);
      end loop;
      for J in 0 .. NQ - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all K in 0 .. J - 1 =>
                 Same (Yp (K),
                       L.Dot_Ref (L.Element_Array (P.Linear_Poly),
                                  T_Dblock, K, G.Dblock_Len))));
         Yp (J) := L.Evaluate (L.Element_Array (P.Linear_Poly), T_Dblock, J);
      end loop;
      Want_Dot  := Dot (B, Alphal);
      Proof_Dot := Dot1 (P.Linear_Poly (NQ .. NQ + WR - 1));
      if Yc /= Yp then
         St := Linear_Failed;
      elsif Proof_Dot + Want_Dot /= Zero then
         St := Linear_Sum_Failed;
      else
         St := Ok;
      end if;
   end Verify_Dot;

   ----------------------------------------------------------------------
   --  verify_quad
   ----------------------------------------------------------------------

   procedure Verify_Quad
     (G        : Valid_Geometry;
      P        : Proof;
      U_Quad   : Element_Array;
      T_Dblock : L.Table;
      Yc, Yp   : out Element_Array;
      Ok       : out Boolean)
   is
      NQ  : constant Natural := G.Num_Queries;
      Tmp : Element_Array (0 .. NQ - 1) := [others => Zero];
      YQ  : constant L.Element_Array := Quad_Poly (G, P);
   begin
      Yc := [others => Zero];
      Yp := [others => Zero];
      for J in 0 .. NQ - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all K in 0 .. J - 1 =>
                 Same (Yc (K), Col (P, G, Quad_Row (G), K))));
         Yc (J) := Col (P, G, Quad_Row (G), J);
      end loop;
      Lemma_Quad_Zero (P, G, U_Quad);
      for I in 0 .. G.Num_Quad_Rows - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J in 0 .. NQ - 1 =>
                 Same (Yc (J), Quad_Ref (P, G, U_Quad, J, I))));
         for J in 0 .. NQ - 1 loop
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all K in 0 .. J - 1 =>
                    Same (Tmp (K),
                          Col (P, G, Quad_Z_Row_Start (G) + I, K)
                          - Col (P, G, Quad_X_Row_Start (G) + I, K)
                            * Col (P, G, Quad_Y_Row_Start (G) + I, K))));
            Tmp (J) := Col (P, G, Quad_Z_Row_Start (G) + I, J)
                       - Col (P, G, Quad_X_Row_Start (G) + I, J)
                         * Col (P, G, Quad_Y_Row_Start (G) + I, J);
         end loop;
         Lemma_Quad_Step (P, G, U_Quad, I);
         Axpy (Yc, Tmp, U_Quad (I));
      end loop;
      for J in 0 .. NQ - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all K in 0 .. J - 1 =>
                 Same (Yp (K),
                       L.Dot_Ref (YQ, T_Dblock, K, G.Dblock_Len))));
         Yp (J) := L.Evaluate (YQ, T_Dblock, J);
      end loop;
      Ok := Yc = Yp;
   end Verify_Quad;

   ----------------------------------------------------------------------
   --  verify
   ----------------------------------------------------------------------

   -------------------------------------------------------------------
   --  The working set of one verification, in one allocation on the
   --  heap (ADR 0047): the challenges, the chosen columns, the two
   --  Lagrange tables, the two evaluation vectors of the tests and the
   --  constraint vector of the linear test.
   -------------------------------------------------------------------

   type Work
     (Ldt_Last, Alphal_Last, Alphaq_Last, Quad_Last : Index;
      Q_Last      : Index;
      Block_Last  : Index;
      Dblock_Last : Index;
      Full_Last   : Index)
   is record
      Ch       : Challenges (Ldt_Last, Alphal_Last, Alphaq_Last, Quad_Last);
      Idx      : Column_Indices (0 .. Q_Last);
      T_Block  : L.Table (0 .. Block_Last, 0 .. Q_Last);
      T_Dblock : L.Table (0 .. Dblock_Last, 0 .. Q_Last);
      Yc, Yp   : Element_Array (0 .. Q_Last);
      A_Full   : Element_Array (0 .. Full_Last);
   end record;

   type Work_Access is access Work;

   procedure Free_Work is
     new Ada.Unchecked_Deallocation (Work, Work_Access);

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
   is
      G : constant Valid_Geometry := Make (Cfg, NW, Lqc'Last + 1);
   begin
      Transcript.Write_Bytes (Statement_Hash);
      if P.Col_Last + 1 /= Opened (G) then
         St := Queried_Columns_Length;
         return;
      end if;
      if P.Ldt_Last + 1 /= G.Block_Len
        or else P.Linear_Last + 1 /= G.Dblock_Len
        or else P.Low_Last + 1 /= G.Num_Queries
        or else P.High_Last + 1 /= G.Dblock_Len - G.Block_Len
        or else P.Nonce_Last + 1 /= G.Num_Queries
        or else P.Path_Last + 1 /= 2 * Num_Leaves (G)
      then
         St := Polynomial_Lengths;
         return;
      end if;
      --  The working set, in one allocation on the heap (ADR 0047).
      declare
         Good      : Boolean;
         Want_Dot  : Element;
         Proof_Dot : Element;
         St_Dot    : Status;
         W : Work_Access := new Work'
           (Ldt_Last    => Num_Wq_Rows (G) - 1,
            Alphal_Last => B'Length - 1,
            Alphaq_Last => 3 * Lqc'Last + 2,
            Quad_Last   => G.Num_Quad_Rows - 1,
            Q_Last      => G.Num_Queries - 1,
            Block_Last  => G.Block_Len - 1,
            Dblock_Last => G.Dblock_Len - 1,
            Full_Last   => Vector_Len (G) - 1,
            Ch          => (Ldt_Last    => Num_Wq_Rows (G) - 1,
                            Alphal_Last => B'Length - 1,
                            Alphaq_Last => 3 * Lqc'Last + 2,
                            Quad_Last   => G.Num_Quad_Rows - 1,
                            U_Ldt       => [others => Zero],
                            Alphal      => [others => Zero],
                            Alphaq      => [others => Zero],
                            U_Quad      => [others => Zero]),
            Idx         => [others => 0],
            T_Block     => [others => [others => Zero]],
            T_Dblock    => [others => [others => Zero]],
            Yc          => [others => Zero],
            Yp          => [others => Zero],
            A_Full      => [others => Zero]);
      begin
         Draw_Challenges (G, B'Length, Lqc'Last + 1, W.Ch);
         Absorb_Polynomials (G, P);
         Choose_Columns (G, W.Idx);
         if Transcript.Is_Exhausted then
            St := Exhausted;
            Free_Work (W);
            return;
         end if;
         Verify_Merkle (G, Root, P, W.Idx, Good);
         if not Good then
            St := Merkle_Failed;
            Free_Work (W);
            return;
         end if;
         if G.Encoded_Len - 1 > Max_Eval_Point then
            St := Matrix_Failed;
            Free_Work (W);
            return;
         end if;
         Build_Tables (G, W.Idx, W.T_Block, W.T_Dblock, Good);
         if not Good then
            St := Matrix_Failed;
            Free_Work (W);
            return;
         end if;
         Verify_LDT (G, P, W.Ch.U_Ldt, W.T_Block, W.Yc, W.Yp, Good);
         if not Good then
            St := LDT_Failed;
            Free_Work (W);
            return;
         end if;
         Build_A_Full (G, A, Lqc, W.Ch.Alphal, W.Ch.Alphaq, W.A_Full);
         Verify_Dot (G, B, P, W.A_Full, W.Ch.Alphal, W.T_Block, W.T_Dblock,
                     W.Yc, W.Yp, Want_Dot, Proof_Dot, St_Dot);
         if St_Dot /= Ok then
            St := St_Dot;
            Free_Work (W);
            return;
         end if;
         Verify_Quad (G, P, W.Ch.U_Quad, W.T_Dblock, W.Yc, W.Yp, Good);
         if not Good then
            St := Quadratic_Failed;
            Free_Work (W);
            return;
         end if;
         Free_Work (W);
         St := Ok;
      end;
   end Verify;

end Ligero_Verifier;
