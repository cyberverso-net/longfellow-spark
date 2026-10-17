pragma SPARK_Mode (On);

with SPARK.Lemmas.Integer_Arithmetic;

package body Proof_Writer is

   use LV.ST.SA.F;

   -------------------------------------------------------------------
   --  Pieces
   -------------------------------------------------------------------

   --  The Size bytes of E at Pos; nothing else changes.
   procedure Put_Element
     (B : in out Byte_Array; Pos : Natural; E : Element)
   with
     Global => null,
     Pre    => B'First = 0 and then Pos <= B'Length - Size,
     Post   => B (Pos .. Pos + Size - 1) = To_Bytes (E)
               and then (for all I in B'Range =>
                           (if I < Pos or else I >= Pos + Size
                            then B (I) = B'Old (I)));

   procedure Put_Element
     (B : in out Byte_Array; Pos : Natural; E : Element)
   is
      Enc : constant Byte_Array := To_Bytes (E);
   begin
      B (Pos .. Pos + Size - 1) := Enc;
   end Put_Element;

   --  The Sub_Size bytes of E in the subfield encoding at Pos.
   procedure Put_Sub_Element
     (B : in out Byte_Array; Pos : Natural; E : Element)
   with
     Global => null,
     Pre    => B'First = 0 and then Pos <= B'Length - Sub_Size,
     Post   => (for all I in B'Range =>
                  (if I < Pos or else I >= Pos + Sub_Size
                   then B (I) = B'Old (I)));

   procedure Put_Sub_Element
     (B : in out Byte_Array; Pos : Natural; E : Element)
   is
      Enc : constant Byte_Array := To_Subfield_Bytes (E);
   begin
      B (Pos .. Pos + Sub_Size - 1) := Enc;
   end Put_Sub_Element;

   --  32 bytes at Pos.
   procedure Put_32 (B : in out Byte_Array; Pos : Natural; D : Bytes_32)
   with
     Global => null,
     Pre    => B'First = 0 and then Pos <= B'Length - 32,
     Post   => B (Pos .. Pos + 31) = D
               and then (for all I in B'Range =>
                           (if I < Pos or else I >= Pos + 32
                            then B (I) = B'Old (I)));

   procedure Put_32 (B : in out Byte_Array; Pos : Natural; D : Bytes_32) is
   begin
      B (Pos .. Pos + 31) := D;
   end Put_32;

   --  A 4-byte little-endian size at Pos (write_size_4bytes).
   procedure Put_Size_4 (B : in out Byte_Array; Pos : Natural; N : Natural)
   with
     Global => null,
     Pre    => B'First = 0 and then B'Length >= 4
               and then Pos <= B'Length - 4,
     Post   => LV.LP.Size_4 (B, Pos) = Unsigned_32 (N)
               and then (for all I in B'Range =>
                           (if I < Pos or else I >= Pos + 4
                            then B (I) = B'Old (I)));

   procedure Put_Size_4 (B : in out Byte_Array; Pos : Natural; N : Natural)
   is
      V : constant Unsigned_32 := Unsigned_32 (N);
   begin
      B (Pos)     := Unsigned_8 (V and 16#FF#);
      B (Pos + 1) := Unsigned_8 (Shift_Right (V, 8) and 16#FF#);
      B (Pos + 2) := Unsigned_8 (Shift_Right (V, 16) and 16#FF#);
      B (Pos + 3) := Unsigned_8 (Shift_Right (V, 24) and 16#FF#);
   end Put_Size_4;

   -------------------------------------------------------------------
   --  Section 7.3
   -------------------------------------------------------------------

   --  The offsets of the padded proof, as the reader has them: the
   --  hidden recursion unfolded one step, and the bound on the total.
   procedure Lemma_Proof_Step (C : Circuit; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => J <= C.Last_Layer,
     Post   => LV.ST.SV.Proof_Off (C, J + 1)
               = LV.ST.SV.Proof_Off (C, J) + LV.ST.SV.Proof_Size (C, J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         LV.ST.SV.Proof_Off);
   begin
      null;
   end Lemma_Proof_Step;

   procedure Lemma_Proof_Mono (C : Circuit; I, J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => I <= J and then J <= C.Last_Layer + 1,
     Post   => LV.ST.SV.Proof_Off (C, I) <= LV.ST.SV.Proof_Off (C, J),
     Subprogram_Variant => (Decreases => J)
   is
   begin
      if J > I then
         Lemma_Proof_Step (C, J - 1);
         Lemma_Proof_Mono (C, I, J - 1);
      end if;
   end Lemma_Proof_Mono;

   --  Layer J's elements lie within the total.
   procedure Lemma_Layer_Fits (C : Circuit; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => J <= C.Last_Layer,
     Post   => LV.ST.SV.Proof_Off (C, J) + LV.ST.SV.Proof_Size (C, J)
               <= LV.ST.SV.Proof_Total (C)
   is
   begin
      Lemma_Proof_Step (C, J);
      Lemma_Proof_Mono (C, J + 1, C.Last_Layer + 1);
   end Lemma_Layer_Fits;

   --  Element E into slot K of a string of Total slots.
   procedure Put_Slot
     (B : in out Byte_Array; Total : Natural; K : Natural; E : Element)
   with
     Global => null,
     Pre    => B'First = 0 and then Total <= Natural'Last / Size
               and then B'Length = Total * Size
               and then K < Total,
     Post   => (Proof_Only => Slot (B, K) = To_Bytes (E),
                Runtime    => (for all I in B'Range =>
                                 (if I < K * Size or else I >= K * Size + Size
                                  then B (I) = B'Old (I))));

   procedure Put_Slot
     (B : in out Byte_Array; Total : Natural; K : Natural; E : Element)
   is
   begin
      SPARK.Lemmas.Integer_Arithmetic.Lemma_Mult_Is_Monotonic
        (K + 1, Total, Size);
      Put_Element (B, K * Size, E);
   end Put_Slot;

   procedure Write_Sumcheck_Proof
     (C : Circuit;
      P : Sumcheck_Proof;
      B : out Byte_Array)
   is
      Total : constant Natural := LV.ST.SV.Proof_Total (C);
      Off   : Natural;
      Logw  : LV.ST.SA.Logw_Type;
      K     : Natural := 0;

   begin
      B := [others => 0];
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant (K = LV.ST.SV.Proof_Off (C, J));
         Lemma_Layer_Fits (C, J);
         Off  := LV.ST.SV.Proof_Off (C, J);
         Logw := C.Layers (J).Logw;
         for R in 0 .. Logw - 1 loop
            pragma Loop_Invariant
              (Off = LV.ST.SV.Proof_Off (C, J)
               and then Logw = C.Layers (J).Logw
               and then Off + LV.ST.SV.Proof_Size (C, J) <= Total);
            pragma Loop_Invariant (K = Off + 4 * R);
            --  l (P0), r (P0), l (P2), r (P2): slots 0, 2, 1, 3 of the
            --  pad order (Read_Sumcheck_Proof).
            Put_Slot (B, Total, K, P.Evals (Off + 4 * R));
            Put_Slot (B, Total, K + 1, P.Evals (Off + 4 * R + 2));
            Put_Slot (B, Total, K + 2, P.Evals (Off + 4 * R + 1));
            Put_Slot (B, Total, K + 3, P.Evals (Off + 4 * R + 3));
            K := K + 4;
         end loop;
         Put_Slot (B, Total, K, P.Evals (Off + 4 * Logw));
         Put_Slot (B, Total, K + 1, P.Evals (Off + 4 * Logw + 1));
         K := K + 2;
         Lemma_Proof_Step (C, J);
      end loop;
   end Write_Sumcheck_Proof;

   -------------------------------------------------------------------
   --  Section 7.4
   -------------------------------------------------------------------

   function Row_Elems (G : Valid_Geometry; N : Natural) return Natural is
   begin
      SPARK.Lemmas.Integer_Arithmetic.Lemma_Mult_Is_Monotonic
        (N, G.Total_Rows, G.Num_Queries);
      return N * G.Num_Queries;
   end Row_Elems;

   procedure Lemma_Groups (G : Valid_Geometry; Sfb : Natural) is
      Lead  : constant Natural := Lead_Rows;
      Sub   : constant Natural := Sub_Rows (G, Sfb);
   begin
      --  Three random rows precede the witness rows; the subfield rows
      --  are witness rows; the field's own subfield takes every row.
      pragma Assert (G.Total_Rows = 3 + G.Num_Witness_Rows
                                    + 3 * G.Num_Quad_Rows);
      pragma Assert (Lead + Sub <= G.Total_Rows);
      declare
         Trail : constant Natural := Trail_Rows (G, Sfb);
         EL : constant Natural := Row_Elems (G, Lead);
         ES : constant Natural := Row_Elems (G, Sub);
         ET : constant Natural := Row_Elems (G, Trail);
      begin
         pragma Assert
           (Long_Long_Integer (EL) + Long_Long_Integer (ES)
            + Long_Long_Integer (ET)
            = Long_Long_Integer (Lead + Sub + Trail)
              * Long_Long_Integer (G.Num_Queries));
         pragma Assert (Lead + Sub + Trail = G.Total_Rows);
         pragma Assert
           (Long_Long_Integer (LV.LP.Opened (G))
            = Long_Long_Integer (G.Total_Rows)
              * Long_Long_Integer (G.Num_Queries));
      end;
   end Lemma_Groups;

   function Runs_Len (G : Valid_Geometry; Sfb : Natural) return Natural is
      Lead  : constant Natural := Lead_Rows;
      Sub   : constant Natural := Sub_Rows (G, Sfb);
      L     : Natural;
   begin
      Lemma_Groups (G, Sfb);
      declare
         Trail : constant Natural := Trail_Rows (G, Sfb);
         EL : constant Natural := Row_Elems (G, Lead);
         ES : constant Natural := Row_Elems (G, Sub);
         ET : constant Natural := Row_Elems (G, Trail);
         Op : constant Natural := LV.LP.Opened (G);
      begin
         --  Each product is bounded by Opened * Size <= 2^25 * 32.
         pragma Assert (Op <= LV.LP.Max_Opened);
         pragma Assert (EL + ES + ET = Op);
         if Sub = 0 then
            L := 4 + Op * Size;
         else
            L := 4 + EL * Size + 4 + ES * Sub_Size;
            if Trail > 0 then
               L := L + 4 + ET * Size;
            end if;
            pragma Assert (EL * Size + ES * Sub_Size + ET * Size
                           <= Op * Size);
         end if;
      end;
      return L;
   end Runs_Len;

   --  One run: the count, then the elements of Rows rows from First_Row
   --  in the width of Sub. Pos advances past it. The bytes before Pos
   --  are unchanged.
   procedure Write_Run
     (G         : Valid_Geometry;
      P         : Ligero_Part;
      First_Row : Natural;
      Rows      : Natural;
      Sub       : Boolean;
      B         : in out Byte_Array;
      Pos       : in out Natural)
   with
     Global => null,
     Pre    => B'First = 0
               and then LV.LP.Fits (G)
               and then LV.LP.Shape (P, G)
               and then Rows <= G.Total_Rows
               and then First_Row <= G.Total_Rows - Rows
               and then Pos <= B'Length - 4
               and then Long_Long_Integer (Row_Elems (G, Rows))
                        * Long_Long_Integer (LV.LP.Run_Width (Sub))
                        <= Long_Long_Integer (B'Length - Pos - 4),
     Post   => Pos = Pos'Old + 4
                     + Row_Elems (G, Rows) * LV.LP.Run_Width (Sub)
               and then LV.LP.Size_4 (B, Pos'Old)
                        = Unsigned_32 (Row_Elems (G, Rows))
               and then (for all I in B'Range =>
                           (if I < Pos'Old then B (I) = B'Old (I)));

   procedure Write_Run
     (G         : Valid_Geometry;
      P         : Ligero_Part;
      First_Row : Natural;
      Rows      : Natural;
      Sub       : Boolean;
      B         : in out Byte_Array;
      Pos       : in out Natural)
   is
      W     : constant Positive := LV.LP.Run_Width (Sub);
      Count : constant Natural := Row_Elems (G, Rows);
      Start : constant Natural := Pos with Ghost;
      Q     : Natural;
   begin
      Put_Size_4 (B, Pos, Count);
      Pos := Pos + 4;
      for Row in First_Row .. First_Row + Rows - 1 loop
         pragma Loop_Invariant
           (Pos = Start + 4 + Row_Elems (G, Row - First_Row) * W);
         pragma Loop_Invariant
           (LV.LP.Size_4 (B, Start) = Unsigned_32 (Count));
         pragma Loop_Invariant
           (for all I in B'Range =>
              (if I < Start then B (I) = B'Loop_Entry (I)));
         Q := LV.LP.Row_Off (G, Row);
         for J in 0 .. G.Num_Queries - 1 loop
            pragma Loop_Invariant
              (Pos = Start + 4 + (Row_Elems (G, Row - First_Row) + J) * W);
            pragma Loop_Invariant
              (LV.LP.Size_4 (B, Start) = Unsigned_32 (Count));
            pragma Loop_Invariant
              (for all I in B'Range =>
                 (if I < Start then B (I) = B'Loop_Entry (I)));
            if Sub then
               Put_Sub_Element (B, Pos, P.Columns (Q + J));
            else
               Put_Element (B, Pos, P.Columns (Q + J));
            end if;
            Pos := Pos + W;
         end loop;
      end loop;
   end Write_Run;

   --  Well_Coded of the run just written, from Well_Coded of what
   --  follows: the reader's rule unfolded one step.
   procedure Lemma_Run_Coded
     (B     : Byte_Array;
      Pos   : Natural;
      Left  : Natural;
      Sub   : Boolean;
      First : Boolean;
      Count : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => B'First = 0 and then Left > 0
               and then B'Length >= 4 and then Pos <= B'Length - 4
               and then Count <= LV.LP.Max_Run
               and then Count <= Left
               and then (Count > 0 or else First)
               and then LV.LP.Size_4 (B, Pos) = Unsigned_32 (Count)
               and then Long_Long_Integer (Count)
                        * Long_Long_Integer (LV.LP.Run_Width (Sub))
                        <= Long_Long_Integer (B'Length - Pos - 4)
               and then LV.LP.Well_Coded
                          (B, Pos + 4 + Count * LV.LP.Run_Width (Sub),
                           Left - Count, not Sub, False),
     Post   => LV.LP.Well_Coded (B, Pos, Left, Sub, First)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         LV.LP.Well_Coded);
   begin
      null;
   end Lemma_Run_Coded;

   procedure Lemma_Runs_Done
     (B : Byte_Array; Pos : Natural; Sub, First : Boolean)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => B'First = 0,
     Post   => LV.LP.Well_Coded (B, Pos, 0, Sub, First)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         LV.LP.Well_Coded);
   begin
      null;
   end Lemma_Runs_Done;

   procedure Write_Ligero_Proof
     (G   : Valid_Geometry;
      Sfb : Natural;
      P   : Ligero_Part;
      B   : in out Byte_Array;
      Off : Natural)
   is
      Pos   : Natural := Off;
      Lead  : constant Natural := Lead_Rows;
      Sub   : constant Natural := Sub_Rows (G, Sfb);
      Total : constant Natural := LV.LP.Opened (G);
      Fixed : constant Natural := LV.LP.Fixed_Len (G);
      RL    : constant Natural := Runs_Len (G, Sfb);
      Q0    : constant Natural := Off + Fixed;
      --  The positions of the runs, from the lengths.
      Q1     : Natural with Ghost => Proof_Only;
      Q2, Q3 : Natural := 0 with Ghost => Proof_Only;
   begin
      Lemma_Groups (G, Sfb);

      --  The four polynomials and the nonces.
      for I in P.Ldt_Poly'Range loop
         pragma Loop_Invariant (Pos = Off + I * Size);
         pragma Loop_Invariant
           (for all K in B'Range =>
              (if K < Off then B (K) = B'Loop_Entry (K)));
         Put_Element (B, Pos, P.Ldt_Poly (I));
         Pos := Pos + Size;
      end loop;
      for I in P.Linear_Poly'Range loop
         pragma Loop_Invariant (Pos = Off + (G.Block_Len + I) * Size);
         pragma Loop_Invariant
           (for all K in B'Range =>
              (if K < Off then B (K) = B'Loop_Entry (K)));
         Put_Element (B, Pos, P.Linear_Poly (I));
         Pos := Pos + Size;
      end loop;
      for I in P.Quad_Low'Range loop
         pragma Loop_Invariant
           (Pos = Off + (G.Block_Len + G.Dblock_Len + I) * Size);
         pragma Loop_Invariant
           (for all K in B'Range =>
              (if K < Off then B (K) = B'Loop_Entry (K)));
         Put_Element (B, Pos, P.Quad_Low (I));
         Pos := Pos + Size;
      end loop;
      for I in P.Quad_High'Range loop
         pragma Loop_Invariant
           (Pos = Off + (G.Block_Len + G.Dblock_Len + G.Num_Queries + I)
                        * Size);
         pragma Loop_Invariant
           (for all K in B'Range =>
              (if K < Off then B (K) = B'Loop_Entry (K)));
         Put_Element (B, Pos, P.Quad_High (I));
         Pos := Pos + Size;
      end loop;
      for I in P.Nonces'Range loop
         pragma Loop_Invariant
           (Pos = Off + (2 * G.Dblock_Len + G.Num_Queries) * Size + 32 * I);
         pragma Loop_Invariant
           (for all K in B'Range =>
              (if K < Off then B (K) = B'Loop_Entry (K)));
         Put_32 (B, Pos, P.Nonces (I));
         Pos := Pos + 32;
      end loop;
      pragma Assert (Proof_Only => Pos = Q0);
      pragma Assert (Proof_Only => B'Length = Q0 + RL + 4 + 32 * P.Path_Count);

      --  The opened columns, in runs by row kind (ADR 0051).
      if Sub = 0 then
         pragma Assert (Proof_Only => RL = 4 + Total * Size);
         Write_Run (G, P, 0, G.Total_Rows, False, B, Pos);
         Q1 := Pos;
         pragma Assert (Proof_Only => Q1 = Q0 + RL);
      else
         declare
            Trail : constant Natural := Trail_Rows (G, Sfb);
            EL : constant Natural := Row_Elems (G, Lead);
            ES : constant Natural := Row_Elems (G, Sub);
            ET : constant Natural := Row_Elems (G, Trail);
         begin
            pragma Assert (EL + ES + ET = Total);
            pragma Assert
              (Proof_Only => RL >= 4 + EL * Size + 4 + ES * Sub_Size);
            Write_Run (G, P, 0, Lead, False, B, Pos);
            Q1 := Pos;
            pragma Assert (Proof_Only => Q1 = Q0 + 4 + EL * Size);
            Write_Run (G, P, Lead, Sub, True, B, Pos);
            Q2 := Pos;
            pragma Assert (Proof_Only => Q2 = Q1 + 4 + ES * Sub_Size);
            if Trail > 0 then
               pragma Assert
                 (Proof_Only => RL = Q2 - Q0 + 4 + ET * Size);
               Write_Run (G, P, Lead + Sub, Trail, False, B, Pos);
            end if;
            Q3 := Pos;
            pragma Assert (Proof_Only => Q3 = Q0 + RL);
         end;
      end if;

      --  The path.
      pragma Assert (Proof_Only => Pos = Q0 + RL);
      Put_Size_4 (B, Pos, P.Path_Count);
      Pos := Pos + 4;
      for I in 0 .. P.Path_Count - 1 loop
         pragma Loop_Invariant (Pos = Q0 + RL + 4 + 32 * I);
         pragma Loop_Invariant
           (for all K in B'Range =>
              (if K < Q0 + RL + 4 then B (K) = B'Loop_Entry (K)));
         Put_32 (B, Pos, P.Path (I));
         Pos := Pos + 32;
      end loop;

      --  Well_Coded, run by run from the end.
      if Sub = 0 then
         Lemma_Runs_Done (B, Q1, True, False);
         Lemma_Run_Coded (B, Q0, Total, False, True, Total);
      else
         declare
            Trail : constant Natural := Trail_Rows (G, Sfb);
            EL : constant Natural := Row_Elems (G, Lead);
            ES : constant Natural := Row_Elems (G, Sub);
            ET : constant Natural := Row_Elems (G, Trail);
         begin
            if Trail > 0 then
               Lemma_Runs_Done (B, Q3, True, False);
               Lemma_Run_Coded (B, Q2, ET, False, False, ET);
            else
               Lemma_Runs_Done (B, Q2, False, False);
            end if;
            Lemma_Run_Coded (B, Q1, ES + ET, True, False, ES);
            Lemma_Run_Coded (B, Q0, Total, False, True, EL);
         end;
      end if;
   end Write_Ligero_Proof;

   -------------------------------------------------------------------
   --  Section 7.5
   -------------------------------------------------------------------

   procedure Write_Proof
     (C        : Circuit;
      G        : Valid_Geometry;
      Sfb      : Natural;
      Root     : Bytes_32;
      Sumcheck : Sumcheck_Proof;
      Lig      : Ligero_Part;
      B        : out Byte_Array)
   is
      SL : constant Natural := Sumcheck_Len (C);
   begin
      B := [others => 0];
      B (0 .. 31) := Root;
      declare
         SB : Byte_Array (0 .. SL - 1);
      begin
         Write_Sumcheck_Proof (C, Sumcheck, SB);
         B (32 .. 32 + SL - 1) := SB;
      end;
      Write_Ligero_Proof (G, Sfb, Lig, B, 32 + SL);
   end Write_Proof;

end Proof_Writer;
