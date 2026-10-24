pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;
with SPARK.Lemmas.Integer_Arithmetic;
with Sha256;

package body Ligero_Prover is

   -------------------------------------------------------------------
   --  Encode_Row
   -------------------------------------------------------------------

   procedure Encode_Row
     (Row : Element_Array;
      T   : Table;
      Enc : out Element_Array)
   is
      K : constant Positive := Row'Length;
   begin
      if Use_Fft then
         --  The parity part from the FFT, the systematic part written
         --  here (the same values Extend leaves there).
         Extend (Row, Enc);
         for X in 0 .. Row'Last loop
            Enc (X) := Row (X);
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all X2 in 0 .. X => Same (Enc (X2), Row (X2))));
         end loop;
         return;
      end if;
      Enc := [others => Zero];
      for X in 0 .. Row'Last loop
         Enc (X) := Row (X);
         pragma Loop_Invariant
           (Proof_Only =>
              (for all X2 in 0 .. X => Same (Enc (X2), Row (X2))));
      end loop;
      for X in K .. Enc'Last loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all X2 in 0 .. K - 1 => Same (Enc (X2), Row (X2))));
         pragma Loop_Invariant
           (Proof_Only =>
              (for all X2 in K .. X - 1 =>
                 Same (Enc (X2),
                       LV.L.Dot_Ref (LV.L.Element_Array (Row), T,
                                     X2 - K, K))));
         Enc (X) := LV.L.Evaluate (LV.L.Element_Array (Row), T, X - K);
      end loop;
   end Encode_Row;

   -------------------------------------------------------------------
   --  Heap objects
   -------------------------------------------------------------------

   procedure Free_Commitment is
     new Ada.Unchecked_Deallocation (Commitment, Commitment_Access);

   procedure Free (Com : in out Commitment_Access) is
   begin
      Free_Commitment (Com);
   end Free;

   --  Scratch rows.
   type Elems_Access is access Element_Array;

   procedure Free_Elems is
     new Ada.Unchecked_Deallocation (Element_Array, Elems_Access);

   --  The leaf digests and the Lagrange denominators.
   type Work (Block_Last, Dblock_Last : Index; Leaf_Last : Leaf_Index)
   is record
      Leaves : Merkle.Digest_Array (0 .. Leaf_Last);
      Inv_B  : LV.L.Element_Array (0 .. Block_Last);
      Inv_D  : LV.L.Element_Array (0 .. Dblock_Last);
   end record;

   type Work_Access is access Work;

   procedure Free_Work is new Ada.Unchecked_Deallocation (Work, Work_Access);

   -------------------------------------------------------------------
   --  Shapes of the arguments, and the row bounds
   -------------------------------------------------------------------

   function Tab_Shape (Tab : Tableau; G : Valid_Geometry) return Boolean is
     (Tab'First (1) = 0 and then Tab'Last (1) = G.Total_Rows - 1
      and then Tab'First (2) = 0 and then Tab'Last (2) = G.Encoded_Len - 1)
   with Global => null, Pre => Prover_Fits (G);

   --  The two tables of the Lagrange encoder; one unused element each
   --  with the FFT.
   function Block_Table (T : Table; G : Valid_Geometry) return Boolean is
     (T'First (1) = 0 and then T'First (2) = 0
      and then
      (if Use_Fft then T'Last (1) = 0 and then T'Last (2) = 0
       else T'Last (1) = G.Block_Len - 1
            and then T'Last (2) = G.Encoded_Len - G.Block_Len - 1))
   with Global => null, Pre => Prover_Fits (G);

   function Dblock_Table (T : Table; G : Valid_Geometry) return Boolean is
     (T'First (1) = 0 and then T'First (2) = 0
      and then
      (if Use_Fft then T'Last (1) = 0 and then T'Last (2) = 0
       else T'Last (1) = G.Dblock_Len - 1
            and then T'Last (2) = G.Encoded_Len - G.Dblock_Len - 1))
   with Global => null, Pre => Prover_Fits (G);

   function Row_Shape (Row : Element_Array; K : Natural) return Boolean is
     (Row'First = 0 and then Row'Length = K)
   with Global => null;

   --  Witness row I: I WR + WR <= NW + WR - 1 (Consistent).
   procedure Lemma_Witness_Row_Fits (G : Valid_Geometry; I : Natural) with
     Ghost, Global => null,
     Pre  => I < G.Num_Witness_Rows,
     Post => Long_Long_Integer (I + 1)
             * Long_Long_Integer (G.Witnesses_Per_Row)
             <= Long_Long_Integer (G.Num_Witnesses)
                + Long_Long_Integer (G.Witnesses_Per_Row) - 1
             and then I * G.Witnesses_Per_Row
                      <= Natural'Last - G.Witnesses_Per_Row
   is
   begin
      SPARK.Lemmas.Integer_Arithmetic.Lemma_Mult_Is_Monotonic
        (I + 1, G.Num_Witness_Rows, G.Witnesses_Per_Row);
   end Lemma_Witness_Row_Fits;

   --  Quadratic row I: I WR + WR <= Max_Quads + WR - 1 (Consistent).
   procedure Lemma_Quad_Row_Fits (G : Valid_Geometry; I : Natural) with
     Ghost, Global => null,
     Pre  => I < G.Num_Quad_Rows,
     Post => Long_Long_Integer (I + 1)
             * Long_Long_Integer (G.Witnesses_Per_Row)
             <= Long_Long_Integer (Max_Quads)
                + Long_Long_Integer (G.Witnesses_Per_Row) - 1
             and then I * G.Witnesses_Per_Row
                      <= Natural'Last - G.Witnesses_Per_Row
   is
   begin
      SPARK.Lemmas.Integer_Arithmetic.Lemma_Mult_Is_Monotonic
        (I + 1, G.Num_Quad_Rows, G.Witnesses_Per_Row);
   end Lemma_Quad_Row_Fits;

   --  The parity columns K .. NCOL - 1 as Lagrange.Build takes them.
   procedure Parity_Columns (K, NCOL : Natural; Cols : out LV.L.Column_Array)
   with
     Global => null,
     Pre    => K <= NCOL and then NCOL - 1 <= LV.Max_Eval_Point
               and then Cols'First = 0 and then Cols'Last = NCOL - K - 1,
     Post   => (for all C in Cols'Range => Cols (C) = K + C)
   is
   begin
      Cols := [others => 0];
      for C in Cols'Range loop
         Cols (C) := K + C;
         pragma Loop_Invariant (for all C2 in 0 .. C => Cols (C2) = K + C2);
      end loop;
   end Parity_Columns;

   -------------------------------------------------------------------
   --  The rows before encoding
   -------------------------------------------------------------------

   --  The random prefix: NREQ draws, in the subfield when Sub.
   procedure Sample_Prefix
     (Row : in out Element_Array; NREQ : Natural; Sub : Boolean)
   with
     Always_Terminates => not Sampling_Rejects,
     Pre => Row'First = 0 and then NREQ <= Row'Length
   is
   begin
      for X in 0 .. NREQ - 1 loop
         if Sub then
            SP.Sample_Subfield (Row (X));
         else
            SP.Sample_Element (Row (X));
         end if;
      end loop;
   end Sample_Prefix;

   --  The witness slots NREQ .. NREQ + WR - 1 are zeroed.
   procedure Zero_Slots (Row : in out Element_Array; NREQ, WR : Natural) with
     Global => null,
     Pre    => Row'First = 0 and then WR <= Row'Length
               and then NREQ <= Row'Length - WR,
     Post   =>
       (Proof_Only =>
          (for all J in 0 .. WR - 1 => Same (Row (NREQ + J), Zero)))
   is
   begin
      for J in 0 .. WR - 1 loop
         Row (NREQ + J) := Zero;
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J2 in 0 .. J => Same (Row (NREQ + J2), Zero)));
      end loop;
   end Zero_Slots;

   --  The witness slots receive W (Start + J), zero beyond W.
   procedure Fill_Witness_Slots
     (Row : in out Element_Array; NREQ, WR, Start : Natural; W : Element_Array)
   with
     Global => null,
     Pre    => Row'First = 0 and then WR <= Row'Length
               and then NREQ <= Row'Length - WR and then W'First = 0
               and then W'Last < Max_Witnesses
               and then Start <= Natural'Last - WR,
     Post   =>
       (Proof_Only =>
          (for all J in 0 .. WR - 1 =>
             Same (Row (NREQ + J),
                   (if Start + J <= W'Last then W (Start + J) else Zero))))
   is
   begin
      for J in 0 .. WR - 1 loop
         if Start + J <= W'Last then
            Row (NREQ + J) := W (Start + J);
         else
            Row (NREQ + J) := Zero;
         end if;
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J2 in 0 .. J =>
                 Same (Row (NREQ + J2),
                       (if Start + J2 <= W'Last then W (Start + J2)
                        else Zero))));
      end loop;
   end Fill_Witness_Slots;

   --  The value of slot P of a quadratic row of hand H: the hand of the
   --  triple P, zero beyond the triples.
   function Quad_Value
     (W : Element_Array; Lqc : Lqc_Array; H : Natural; P : Natural)
      return Element
   is
     (if P <= Lqc'Last then W (Sel (Lqc (P), H)) else Zero)
   with Ghost => Proof_Only,
        Pre   => W'First = 0 and then Lqc'First = 0 and then H <= 2
                 and then LV.Lqc_In_Range (Lqc, W'Length);

   --  The witness slots receive the hand H of the triples Start + J,
   --  zero beyond the triples.
   procedure Fill_Quad_Slots
     (Row   : in out Element_Array;
      NREQ, WR, Start : Natural;
      W     : Element_Array;
      Lqc   : Lqc_Array;
      H     : Natural)
   with
     Global => null,
     Pre    => Row'First = 0 and then WR <= Row'Length
               and then NREQ <= Row'Length - WR and then W'First = 0
               and then W'Last < Max_Witnesses
               and then Lqc'First = 0 and then Lqc'Last < Max_Quads
               and then Start <= Natural'Last - WR
               and then LV.Lqc_In_Range (Lqc, W'Length) and then H <= 2,
     Post   =>
       (Proof_Only =>
          (for all J in 0 .. WR - 1 =>
             Same (Row (NREQ + J), Quad_Value (W, Lqc, H, Start + J))))
   is
   begin
      for J in 0 .. WR - 1 loop
         if Start + J <= Lqc'Last then
            Row (NREQ + J) := W (Sel (Lqc (Start + J), H));
         else
            Row (NREQ + J) := Zero;
         end if;
         pragma Assert
           (Proof_Only =>
              Same (Row (NREQ + J), Quad_Value (W, Lqc, H, Start + J)));
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J2 in 0 .. J =>
                 Same (Row (NREQ + J2), Quad_Value (W, Lqc, H, Start + J2))));
      end loop;
   end Fill_Quad_Slots;

   -------------------------------------------------------------------
   --  A row into the tableau
   -------------------------------------------------------------------

   --  Row R of the tableau receives the encoding of Row with the table
   --  T; the other rows are untouched.
   procedure Commit_Row
     (Tab : in out Tableau;
      R   : Natural;
      Row : Element_Array;
      T   : Table)
   with
     Global => null,
     Pre    =>
       Tab'First (1) = 0 and then R <= Tab'Last (1) and then Tab'First (2) = 0
       and then Row'First = 0 and then Row'Length in 1 .. LV.L.Max_K
       and then T'First (1) = 0 and then T'First (2) = 0
       and then Tab'Last (2) < Natural'Last
       and then Tab'Length (2) <= 2**16
       and then
       (if Use_Fft then Row'Length <= Tab'Length (2)
        else T'Last (1) = Row'Last
             and then Tab'Length (2) = Row'Length + T'Length (2)),
     Post   =>
       (Proof_Only =>
          (for all X in 0 .. Row'Last => Same (Tab (R, X), Row (X)))
          and then
          (for all R2 in 0 .. Tab'Last (1) =>
             (for all X in 0 .. Tab'Last (2) =>
                (if R2 /= R then Same (Tab (R2, X), Tab'Old (R2, X))))))
   is
      Enc : Elems_Access := new Element_Array'(0 .. Tab'Last (2) => Zero);
   begin
      Encode_Row (Row, T, Enc.all);
      for X in 0 .. Tab'Last (2) loop
         Tab (R, X) := Enc (X);
         pragma Loop_Invariant
           (Proof_Only =>
              (for all X2 in 0 .. X => Same (Tab (R, X2), Enc (X2))));
         pragma Loop_Invariant
           (Proof_Only =>
              (for all R2 in 0 .. Tab'Last (1) =>
                 (for all X2 in 0 .. Tab'Last (2) =>
                    (if R2 /= R then
                       Same (Tab (R2, X2), Tab'Loop_Entry (R2, X2))))));
      end loop;
      Free_Elems (Enc);
   end Commit_Row;

   -------------------------------------------------------------------
   --  The three groups of rows
   -------------------------------------------------------------------

   --  Row 2, the quadratic row: DBLOCK random elements, the witness
   --  slots zeroed, committed with the table T_D.
   procedure Quad_Fixed_Row
     (G     : Valid_Geometry;
      Tab   : in out Tableau;
      T_D   : Table;
      Row_D : in out Element_Array)
   with
     Always_Terminates => not Sampling_Rejects,
     Pre  => Prover_Fits (G) and then Tab_Shape (Tab, G)
             and then Dblock_Table (T_D, G)
             and then Row_Shape (Row_D, G.Dblock_Len),
     Post =>
       (Proof_Only =>
          (for all J in 0 .. G.Witnesses_Per_Row - 1 =>
             Same (Tab (Quad_Row (G), G.Num_Queries + J), Zero)))
   is
      NREQ : constant Natural := G.Num_Queries;
      WR   : constant Natural := G.Witnesses_Per_Row;
   begin
      Sample_Prefix (Row_D, G.Dblock_Len, False);
      Zero_Slots (Row_D, NREQ, WR);
      Commit_Row (Tab, Quad_Row (G), Row_D, T_D);
      pragma Assert
        (Proof_Only =>
           (for all J in 0 .. WR - 1 => Same (Row_D (NREQ + J), Zero)));
      pragma Assert (NREQ + WR <= G.Dblock_Len);
      pragma Assert (Row_D'Last = G.Dblock_Len - 1);
      pragma Assert
        (Proof_Only =>
           (for all X in 0 .. Row_D'Last =>
              Same (Tab (Quad_Row (G), X), Row_D (X))));
      pragma Assert
        (Proof_Only =>
           (for all J in 0 .. WR - 1 =>
              Same (Tab (Quad_Row (G), NREQ + J), Row_D (NREQ + J))));
   end Quad_Fixed_Row;

   --  Rows 0, 1 and 2.
   procedure Fixed_Rows
     (G            : Valid_Geometry;
      Tab          : in out Tableau;
      T_B, T_D     : Table;
      Row_B, Row_D : in out Element_Array)
   with
     Always_Terminates => not Sampling_Rejects,
     Pre  => Prover_Fits (G) and then Tab_Shape (Tab, G)
             and then Block_Table (T_B, G) and then Dblock_Table (T_D, G)
             and then Row_Shape (Row_B, G.Block_Len)
             and then Row_Shape (Row_D, G.Dblock_Len),
     Post =>
       (Proof_Only =>
          (for all J in 0 .. G.Witnesses_Per_Row - 1 =>
             Same (Tab (Quad_Row (G), G.Num_Queries + J), Zero)))
   is
      NREQ : constant Natural := G.Num_Queries;
      WR   : constant Natural := G.Witnesses_Per_Row;
   begin
      --  Row 0, the LDT row: BLOCK random elements.
      Sample_Prefix (Row_B, G.Block_Len, False);
      Commit_Row (Tab, Ldt_Row (G), Row_B, T_B);
      --  Row 1, the linear row: DBLOCK random elements, the sum of the
      --  witness slots subtracted from the first of them.
      Sample_Prefix (Row_D, G.Dblock_Len, False);
      Row_D (NREQ) := Row_D (NREQ) - LV.Dot1 (Row_D (NREQ .. NREQ + WR - 1));
      Commit_Row (Tab, Linear_Row (G), Row_D, T_D);
      --  Row 2, the quadratic row.
      Quad_Fixed_Row (G, Tab, T_D, Row_D);
   end Fixed_Rows;

   --  The witness rows. Each row's witness slots are proved against W
   --  as the row is committed (the assertions in the loop); the
   --  composition over the rows is tested (see the spec).
   procedure Witness_Rows
     (G     : Valid_Geometry;
      W     : Element_Array;
      Sfb   : Natural;
      Tab   : in out Tableau;
      T_B   : Table;
      Row_B : in out Element_Array)
   with
     Always_Terminates => not Sampling_Rejects,
     Pre  => Prover_Fits (G) and then Tab_Shape (Tab, G)
             and then Block_Table (T_B, G)
             and then Row_Shape (Row_B, G.Block_Len)
             and then W'First = 0 and then W'Length = G.Num_Witnesses
   is
      NREQ : constant Natural := G.Num_Queries;
      WR   : constant Natural := G.Witnesses_Per_Row;
   begin
      for I in 0 .. G.Num_Witness_Rows - 1 loop
         Lemma_Witness_Row_Fits (G, I);
         Row_B := [others => Zero];
         Sample_Prefix
           (Row_B, NREQ,
            Long_Long_Integer (I + 1) * Long_Long_Integer (WR)
            <= Long_Long_Integer (Sfb));
         Fill_Witness_Slots (Row_B, NREQ, WR, I * WR, W);
         Commit_Row (Tab, Witness_Row_Start (G) + I, Row_B, T_B);
         pragma Assert
           (Proof_Only =>
              (for all J in 0 .. WR - 1 =>
                 Same (Tab (Witness_Row_Start (G) + I, NREQ + J),
                       (if I * WR + J <= W'Last then W (I * WR + J)
                        else Zero))));
      end loop;
   end Witness_Rows;

   --  The quadratic constraint rows: for each row index, the x, y and z
   --  rows in that order (the prefixes are drawn in that order), placed
   --  as three groups. Each row's witness slots are proved against the
   --  triples as the row is committed.
   procedure Quad_Rows
     (G     : Valid_Geometry;
      W     : Element_Array;
      Lqc   : Lqc_Array;
      Tab   : in out Tableau;
      T_B   : Table;
      Row_B : in out Element_Array)
   with
     Always_Terminates => not Sampling_Rejects,
     Pre  => Prover_Fits (G) and then Tab_Shape (Tab, G)
             and then Block_Table (T_B, G)
             and then Row_Shape (Row_B, G.Block_Len)
             and then W'First = 0 and then W'Length = G.Num_Witnesses
             and then Lqc'First = 0 and then Lqc'Last < Max_Quads
             and then G.Num_Quad_Rows
                      = (Lqc'Length + G.Witnesses_Per_Row - 1)
                        / G.Witnesses_Per_Row
             and then LV.Lqc_In_Range (Lqc, W'Length)
   is
      NREQ  : constant Natural := G.Num_Queries;
      WR    : constant Natural := G.Witnesses_Per_Row;
      QX    : constant Natural := Quad_X_Row_Start (G);
      QY    : constant Natural := Quad_Y_Row_Start (G);
      QZ    : constant Natural := Quad_Z_Row_Start (G);
   begin
      for I in 0 .. G.Num_Quad_Rows - 1 loop
         Lemma_Quad_Row_Fits (G, I);
         for H in 0 .. 2 loop
            Row_B := [others => Zero];
            Sample_Prefix (Row_B, NREQ, False);
            Fill_Quad_Slots (Row_B, NREQ, WR, I * WR, W, Lqc, H);
            Commit_Row
              (Tab,
               (case H is when 0 => QX, when 1 => QY, when others => QZ) + I,
               Row_B, T_B);
            pragma Assert
              (Proof_Only =>
                 (for all J in 0 .. WR - 1 =>
                    Same (Tab ((case H is
                                  when 0 => QX, when 1 => QY,
                                  when others => QZ) + I,
                               NREQ + J),
                          Quad_Value (W, Lqc, H, I * WR + J))));
         end loop;
      end loop;
   end Quad_Rows;

   -------------------------------------------------------------------
   --  Commit
   -------------------------------------------------------------------

   --  The fresh commitment with its Lagrange tables; null, and Ok
   --  False, when a denominator has no inverse.
   procedure Allocate
     (G : Valid_Geometry; Com : out Commitment_Access; Ok : out Boolean)
   with
     Pre  => Prover_Fits (G),
     Post => (if Ok then Com /= null and then Com_Shape (Com.all, G)
              else Com = null)
   is
      NCOL  : constant Natural := G.Encoded_Len;
      K_B   : constant Natural := G.Block_Len;
      K_D   : constant Natural := G.Dblock_Len;
      NL    : constant Natural := Num_Leaves (G);
      Wk    : Work_Access;
      Ok_B, Ok_D : Boolean;
   begin
      if Use_Fft then
         --  No table: the parity columns come from Extend.
         Com := new Commitment'
           (Row_Last    => G.Total_Rows - 1,
            Col_Last    => NCOL - 1,
            Leaf_Last   => NL - 1,
            Heap_Last   => 2 * NL - 1,
            Block_Last  => 0,
            Dblock_Last => 0,
            Par_B_Last  => 0,
            Par_D_Last  => 0,
            Tab         => [others => [others => Zero]],
            Nonces      => [others => [others => 0]],
            Heap        => [others => [others => 0]],
            T_Block     => [others => [others => Zero]],
            T_Dblock    => [others => [others => Zero]],
            Root        => [others => 0]);
         Ok := True;
         return;
      end if;
      Com := new Commitment'
        (Row_Last    => G.Total_Rows - 1,
         Col_Last    => NCOL - 1,
         Leaf_Last   => NL - 1,
         Heap_Last   => 2 * NL - 1,
         Block_Last  => K_B - 1,
         Dblock_Last => K_D - 1,
         Par_B_Last  => NCOL - K_B - 1,
         Par_D_Last  => NCOL - K_D - 1,
         Tab         => [others => [others => Zero]],
         Nonces      => [others => [others => 0]],
         Heap        => [others => [others => 0]],
         T_Block     => [others => [others => Zero]],
         T_Dblock    => [others => [others => Zero]],
         Root        => [others => 0]);
      Wk := new Work'
        (Block_Last  => K_B - 1,
         Dblock_Last => K_D - 1,
         Leaf_Last   => NL - 1,
         Leaves      => [others => [others => 0]],
         Inv_B       => [others => Zero],
         Inv_D       => [others => Zero]);
      declare
         Cols_B : LV.L.Column_Array (0 .. NCOL - K_B - 1);
         Cols_D : LV.L.Column_Array (0 .. NCOL - K_D - 1);
      begin
         Parity_Columns (K_B, NCOL, Cols_B);
         Parity_Columns (K_D, NCOL, Cols_D);
         LV.L.Build (K_B, Cols_B, Com.T_Block, Wk.Inv_B, Ok_B);
         LV.L.Build (K_D, Cols_D, Com.T_Dblock, Wk.Inv_D, Ok_D);
      end;
      Free_Work (Wk);
      Ok := Ok_B and Ok_D;
      if not Ok then
         Free_Commitment (Com);
      end if;
   end Allocate;

   --  The nonces, all before any leaf is hashed; the leaves, SHA-256 of
   --  the nonce and the committed column; the tree. The tableau is
   --  untouched.
   procedure Hash_Leaves (G : Valid_Geometry; Com : in out Commitment) with
     Pre  => Prover_Fits (G) and then Com_Shape (Com, G),
     Post => (Runtime    => Com_Shape (Com, G)
                            and then Com.Root = Com.Heap (1),
              Proof_Only =>
                (for all R in 0 .. Com.Row_Last =>
                   (for all X in 0 .. Com.Col_Last =>
                      Same (Com.Tab (R, X), Com.Tab'Old (R, X)))))
   is
      NL     : constant Natural := Num_Leaves (G);
      K_D    : constant Natural := G.Dblock_Len;
      Leaves : Merkle.Digest_Array (0 .. NL - 1);
   begin
      for J in 0 .. NL - 1 loop
         SP.Sample_Nonce (Com.Nonces (J));
      end loop;
      for J in 0 .. NL - 1 loop
         declare
            Ctx : Sha256.Context := Sha256.Initial;
         begin
            Sha256.Update (Ctx, Com.Nonces (J));
            for Row in 0 .. G.Total_Rows - 1 loop
               Sha256.Update (Ctx, To_Bytes (Com.Tab (Row, K_D + J)));
            end loop;
            Leaves (J) := Sha256.Digest (Ctx);
         end;
      end loop;
      Merkle.Build (Leaves, Com.Heap);
      Com.Root := Com.Heap (1);
   end Hash_Leaves;

   procedure Commit
     (G   : Valid_Geometry;
      W   : Element_Array;
      Lqc : Lqc_Array;
      Sfb : Natural;
      Com : out Commitment_Access;
      Ok  : out Boolean)
   is
      Row_B : Elems_Access;
      Row_D : Elems_Access;
   begin
      Allocate (G, Com, Ok);
      if not Ok then
         return;
      end if;
      Row_B := new Element_Array'(0 .. G.Block_Len - 1 => Zero);
      Row_D := new Element_Array'(0 .. G.Dblock_Len - 1 => Zero);
      Fixed_Rows (G, Com.Tab, Com.T_Block, Com.T_Dblock,
                  Row_B.all, Row_D.all);
      Witness_Rows (G, W, Sfb, Com.Tab, Com.T_Block, Row_B.all);
      Quad_Rows (G, W, Lqc, Com.Tab, Com.T_Block, Row_B.all);
      Free_Elems (Row_B);
      Free_Elems (Row_D);
      Hash_Leaves (G, Com.all);
   end Commit;

   -------------------------------------------------------------------
   --  Prove
   -------------------------------------------------------------------

   --  Row I of the a_full layout: I WR + WR <= Vector_Len.
   procedure Lemma_Wq_Row_Fits (G : Valid_Geometry; I : Natural) with
     Ghost, Global => null,
     Pre  => I < Num_Wq_Rows (G),
     Post => (I + 1) * G.Witnesses_Per_Row <= LV.Vector_Len (G)
   is
   begin
      SPARK.Lemmas.Integer_Arithmetic.Lemma_Mult_Is_Monotonic
        (I + 1, Num_Wq_Rows (G), G.Witnesses_Per_Row);
   end Lemma_Wq_Row_Fits;

   --  The quadratic rows cover the triples: NQROW WR >= NQ.
   procedure Lemma_Quads_Cover (G : Valid_Geometry; NQ : Natural) with
     Ghost, Global => null,
     Pre  => NQ <= Max_Quads
             and then G.Num_Quad_Rows
                      = (NQ + G.Witnesses_Per_Row - 1) / G.Witnesses_Per_Row,
     Post => G.Num_Quad_Rows * G.Witnesses_Per_Row >= NQ
   is
   begin
      null;
   end Lemma_Quads_Cover;

   --  The working set of the proof.
   type Proof_Work
     (Ldt_Last, Alphal_Last, Alphaq_Last, Quad_Last : Index;
      Block_Last, Dblock_Last, Col_Last, Full_Last, Q_Last : Index)
   is record
      Ch      : LV.Challenges (Ldt_Last, Alphal_Last, Alphaq_Last, Quad_Last);
      A_Full  : Element_Array (0 .. Full_Last);
      Y_Ldt   : Element_Array (0 .. Block_Last);
      Y_Dot   : Element_Array (0 .. Dblock_Last);
      Y_Quad  : Element_Array (0 .. Dblock_Last);
      Row_Buf : Element_Array (0 .. Dblock_Last);
      A_Ext   : Element_Array (0 .. Block_Last);
      A_Enc   : Element_Array (0 .. Col_Last);
      Idx     : LV.Column_Indices (0 .. Q_Last);
   end record;

   type Proof_Work_Access is access Proof_Work;

   procedure Free_Proof_Work is
     new Ada.Unchecked_Deallocation (Proof_Work, Proof_Work_Access);

   procedure Prove
     (G              : Valid_Geometry;
      Com            : Commitment;
      Lqc            : Lqc_Array;
      A              : Terms;
      B              : Element_Array;
      Statement_Hash : Byte_Array;
      P              : out Proof;
      Ok             : out Boolean)
   is
      NREQ  : constant Natural := G.Num_Queries;
      WR    : constant Natural := G.Witnesses_Per_Row;
      K_B   : constant Natural := G.Block_Len;
      K_D   : constant Natural := G.Dblock_Len;
      NL    : constant Natural := Num_Leaves (G);
      NROW  : constant Natural := G.Total_Rows;
      NWQ   : constant Natural := Num_Wq_Rows (G);
      NQROW : constant Natural := G.Num_Quad_Rows;
      QX    : constant Natural := Quad_X_Row_Start (G);
      QY    : constant Natural := Quad_Y_Row_Start (G);
      QZ    : constant Natural := Quad_Z_Row_Start (G);
      Wk    : Proof_Work_Access;
      Count : Natural;
   begin
      P := (Ldt_Last    => P.Ldt_Last,
            Linear_Last => P.Linear_Last,
            Low_Last    => P.Low_Last,
            High_Last   => P.High_Last,
            Nonce_Last  => P.Nonce_Last,
            Col_Last    => P.Col_Last,
            Path_Last   => P.Path_Last,
            Ldt_Poly    => [others => Zero],
            Linear_Poly => [others => Zero],
            Quad_Low    => [others => Zero],
            Quad_High   => [others => Zero],
            Nonces      => [others => [others => 0]],
            Columns     => [others => Zero],
            Path        => [others => [others => 0]],
            Path_Count  => 0);
      Lemma_Quads_Cover (G, Lqc'Length);
      Wk := new Proof_Work'
        (Ldt_Last    => NWQ - 1,
         Alphal_Last => B'Last,
         Alphaq_Last => 3 * Lqc'Length - 1,
         Quad_Last   => NQROW - 1,
         Block_Last  => K_B - 1,
         Dblock_Last => K_D - 1,
         Col_Last    => G.Encoded_Len - 1,
         Full_Last   => LV.Vector_Len (G) - 1,
         Q_Last      => NREQ - 1,
         Ch          => (Ldt_Last    => NWQ - 1,
                         Alphal_Last => B'Last,
                         Alphaq_Last => 3 * Lqc'Length - 1,
                         Quad_Last   => NQROW - 1,
                         U_Ldt       => [others => Zero],
                         Alphal      => [others => Zero],
                         Alphaq      => [others => Zero],
                         U_Quad      => [others => Zero]),
         A_Full      => [others => Zero],
         Y_Ldt       => [others => Zero],
         Y_Dot       => [others => Zero],
         Y_Quad      => [others => Zero],
         Row_Buf     => [others => Zero],
         A_Ext       => [others => Zero],
         A_Enc       => [others => Zero],
         Idx         => [others => 0]);

      Transcript.Write_Bytes (Statement_Hash);
      LV.Draw_Challenges (G, B'Length, Lqc'Length, Wk.Ch);

      --  y_ldt
      for X in 0 .. K_B - 1 loop
         Wk.Y_Ldt (X) := Com.Tab (Ldt_Row (G), X);
      end loop;
      for I in 0 .. NWQ - 1 loop
         for X in 0 .. K_B - 1 loop
            Wk.Row_Buf (X) := Com.Tab (Witness_Row_Start (G) + I, X);
         end loop;
         LV.Axpy (Wk.Y_Ldt, Wk.Row_Buf (0 .. K_B - 1), Wk.Ch.U_Ldt (I));
      end loop;

      --  a_full, then y_dot
      LV.Build_A_Full (G, A, Lqc, Wk.Ch.Alphal, Wk.Ch.Alphaq, Wk.A_Full);
      for X in 0 .. K_D - 1 loop
         Wk.Y_Dot (X) := Com.Tab (Linear_Row (G), X);
      end loop;
      for I in 0 .. NWQ - 1 loop
         Lemma_Wq_Row_Fits (G, I);
         Wk.A_Ext := [others => Zero];
         for J in 0 .. WR - 1 loop
            Wk.A_Ext (NREQ + J) := Wk.A_Full (I * WR + J);
         end loop;
         --  Only the first dblock columns enter y_dot: the FFT extends
         --  to them alone (prover.rs, dot_proof; ADR 0070).
         if Use_Fft then
            Encode_Row (Wk.A_Ext, Com.T_Block, Wk.A_Enc (0 .. K_D - 1));
         else
            Encode_Row (Wk.A_Ext, Com.T_Block, Wk.A_Enc);
         end if;
         for X in 0 .. K_D - 1 loop
            Wk.Row_Buf (X) := Com.Tab (Witness_Row_Start (G) + I, X);
         end loop;
         LV.Vaxpy (Wk.Y_Dot, Wk.Row_Buf, Wk.A_Enc (0 .. K_D - 1));
      end loop;

      --  y_quad
      for X in 0 .. K_D - 1 loop
         Wk.Y_Quad (X) := Com.Tab (Quad_Row (G), X);
      end loop;
      for I in 0 .. NQROW - 1 loop
         for X in 0 .. K_D - 1 loop
            Wk.Row_Buf (X) :=
              Com.Tab (QZ + I, X) - Com.Tab (QX + I, X) * Com.Tab (QY + I, X);
         end loop;
         LV.Axpy (Wk.Y_Quad, Wk.Row_Buf, Wk.Ch.U_Quad (I));
      end loop;

      P.Ldt_Poly    := Wk.Y_Ldt;
      P.Linear_Poly := Wk.Y_Dot;
      P.Quad_Low    := Wk.Y_Quad (0 .. NREQ - 1);
      P.Quad_High   := Wk.Y_Quad (K_B .. K_D - 1);
      LV.Absorb_Polynomials (G, P);
      LV.Choose_Columns (G, Wk.Idx);
      if Transcript.Is_Exhausted then
         Free_Proof_Work (Wk);
         Ok := False;
         return;
      end if;

      --  The nonces, the opening and the queried columns.
      for K in 0 .. NREQ - 1 loop
         P.Nonces (K) := Com.Nonces (Wk.Idx (K));
      end loop;
      Merkle.Open (NL, Com.Heap, Merkle.Index_Array (Wk.Idx), P.Path, Count);
      P.Path_Count := Count;
      for Row in 0 .. NROW - 1 loop
         for K in 0 .. NREQ - 1 loop
            P.Columns (LV.LP.Row_Off (G, Row) + K) :=
              Com.Tab (Row, K_D + Wk.Idx (K));
         end loop;
      end loop;
      Free_Proof_Work (Wk);
      Ok := True;
   end Prove;

end Ligero_Prover;
