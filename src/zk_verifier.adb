pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;
with Merkle;

package body Zk_Verifier is

   use LV.ST.SA.F;
   use type LV.ST.SA.Term_Array;

   function Shape_Of (P : Packed_Circuit) return Shape is
   begin
      PH.PC.Lemma_Shape_Of (P);
      return PH.PC.Shape_Of (P);
   end Shape_Of;

   procedure Read_Proof
     (B        : Byte_Array;
      S        : Shape;
      G        : Valid_Geometry;
      Root     : out Bytes_32;
      Sumcheck : out Sumcheck_Proof;
      Lig      : out Ligero_Part;
      St       : out Status)
   is
      SL   : constant Natural := Sumcheck_Len (S);
      Next : Natural;
      St2  : LV.ST.Status;
      St3  : Status;
      use type LV.ST.Status;
   begin
      Root     := [others => 0];
      Sumcheck := (Last => Sumcheck.Last, Evals => [others => Zero]);
      Lig := (Ldt_Last    => Lig.Ldt_Last,
              Linear_Last => Lig.Linear_Last,
              Low_Last    => Lig.Low_Last,
              High_Last   => Lig.High_Last,
              Nonce_Last  => Lig.Nonce_Last,
              Col_Last    => Lig.Col_Last,
              Path_Last   => Lig.Path_Last,
              Ldt_Poly    => [others => Zero],
              Linear_Poly => [others => Zero],
              Quad_Low    => [others => Zero],
              Quad_High   => [others => Zero],
              Nonces      => [others => [others => 0]],
              Columns     => [others => Zero],
              Path        => [others => [others => 0]],
              Path_Count  => 0);
      St := Proof_Encoding;
      if B'Length < 32 + SL then
         return;
      end if;
      Root := B (0 .. 31);
      declare
         SB : constant Byte_Array (0 .. SL - 1) := B (32 .. 32 + SL - 1);
      begin
         LV.ST.Read_Sumcheck_Proof (SB, S, Sumcheck, St2);
      end;
      if St2 /= LV.ST.Ok then
         return;
      end if;
      LV.LP.Read (B, 32 + SL, G, Lig, Next, St3);
      if St3 /= Ok then
         return;
      end if;
      if Next /= B'Length then
         return;
      end if;
      St := Ok;
   end Read_Proof;

   -------------------------------------------------------------------
   --  The bound quads, from the packed circuit. The body is the one of
   --  Sumcheck_Verifier.Bound_Quads with the packed kernels in place of
   --  Bind_Quad and Eval_Bound_Quad; the kernels state their result on
   --  the layer of the expansion, Layer_Of (P, J), and Lemma_BQ_Ref_From
   --  takes it to BQ_Ref on the expansion C, where that layer is
   --  Layer_Terms (C, J).
   -------------------------------------------------------------------

   procedure Bound_Quads
     (P  : Packed_Circuit;
      S  : Shape;
      Ch : LV.ST.SV.Challenges;
      BQ : out Element_Array)
   is
      use LV.ST.SV;
      C      : constant Circuit := PH.PC.Expand (P) with Ghost => Proof_Only;
      Logv   : Natural := Ceil_Lg2 (S.Noutput);
      G0, G1 : Challenge_Vector := Ch.G;
   begin
      LV.ST.SA.Lemma_Shape_Of (C);
      pragma Assert (Proof_Only => LV.ST.SA.Shape_Of (C) = S);
      PH.PC.Lemma_Valid (P);
      BQ := [others => Zero];
      declare
         --  The shape of the expansion, for the proof: the lemmas of the
         --  sumcheck speak of Shape_Of (C), the executable statements
         --  read S, and Lemma_Chal_Off_Eq joins the two at the offset of
         --  each layer.
         SC : constant Shape := LV.ST.SA.Shape_Of (C)
           with Ghost => Proof_Only;
      begin
         for J in 0 .. S.Last_Layer loop
            pragma Loop_Invariant (Logv <= LV.ST.SA.Max_Logw);
            pragma Loop_Invariant
              (Proof_Only =>
                 Logv = Layer_Logv (SC, J)
                 and then (for all R in 0 .. Logv - 1 =>
                             Same (G0 (R), Layer_G (SC, Ch, J, 0) (R))
                             and then
                             Same (G1 (R), Layer_G (SC, Ch, J, 1) (R)))
                 and then (for all J2 in 0 .. J - 1 =>
                             Same (BQ (J2), BQ_Ref (C, Ch, J2))));
            Lemma_Chal_Step (S, J);
            Lemma_Chal_Mono (S, J + 1, S.Last_Layer + 1);
            Lemma_Chal_Off_Eq (S, SC, J);
            declare
               Logw : constant LV.ST.SA.Logw_Type := S.Layers (J).Logw;
               CO   : constant Natural := Chal_Off (S, J);
               HC0  : Challenge_Vector := [others => Zero];
               HC1  : Challenge_Vector := [others => Zero];
               V    : Element;
            begin
               pragma Assert
                 (Proof_Only =>
                    CO = Chal_Off (SC, J)
                    and then Logw = SC.Layers (J).Logw);
               for R in 0 .. Logw - 1 loop
                  HC0 (R) := Ch.Layer (CO + 2 + 2 * R);
                  HC1 (R) := Ch.Layer (CO + 2 + 2 * R + 1);
                  pragma Loop_Invariant
                    (for all R2 in 0 .. R =>
                       Same (HC0 (R2), Ch.Layer (CO + 2 + 2 * R2))
                       and then
                       Same (HC1 (R2), Ch.Layer (CO + 2 + 2 * R2 + 1)));
               end loop;
               if Logv <= LV.ST.SA.Max_Bindeq_Log
                 and then Logw <= LV.ST.SA.Max_Bindeq_Log
               then
                  PH.Bind_Quad_Packed
                    (P, J, Logv, G0, G1, HC0, HC1, Logw,
                     Ch.Layer (CO), Ch.Layer (CO + 1), V);
               else
                  PH.Eval_Bound_Quad_Packed
                    (P, J, Logv, G0, G1, HC0, HC1, Logw,
                     Ch.Layer (CO), Ch.Layer (CO + 1), V);
               end if;
               --  The layer of the expansion under its two names.
               pragma Assert
                 (Proof_Only =>
                    PH.Layer_Of (P, J) = LV.ST.SA.Layer_Terms (C, J));
               pragma Assert
                 (Proof_Only =>
                    PH.PC.Layer_Len (P, J)
                    = LV.ST.SA.Layer_Terms (C, J)'Length);
               Lemma_BQ_Ref_From (C, Ch, J, Logv, G0, G1, HC0, HC1, V);
               Lemma_Hand_Chal (SC, Ch, J, 0, HC0);
               Lemma_Hand_Chal (SC, Ch, J, 1, HC1);
               BQ (J) := V;
               Logv := Logw;
               G0 := HC0;
               G1 := HC1;
            end;
         end loop;
      end;
   end Bound_Quads;

   -------------------------------------------------------------------
   --  The working set of one verification, in one allocation on the
   --  heap (ADR 0047): the padded sumcheck proof, the Ligero part, the
   --  challenges, the constraint terms, the constants b and the
   --  quadratic triples, each sized by the circuit or the geometry
   --  through a discriminant.
   -------------------------------------------------------------------

   subtype Index is LV.ST.SA.Index;
   subtype Merkle_Node_Index is Merkle.Node_Index;

   type Work
     (Sum_Last    : Index;
      Ldt_Last    : Index;
      Linear_Last : Index;
      Low_Last    : Index;
      High_Last   : Index;
      Nonce_Last  : Index;
      Col_Last    : Index;
      Path_Last   : Merkle_Node_Index;
      Ch_Last     : Index;
      A_Max       : Index;
      B_Last      : Index;
      Lqc_Last    : Index)
   is record
      Sumcheck : Sumcheck_Proof (Sum_Last);
      Lig      : Ligero_Part (Ldt_Last, Linear_Last, Low_Last, High_Last,
                              Nonce_Last, Col_Last, Path_Last);
      Ch       : LV.ST.SV.Challenges (Ch_Last);
      A        : LV.ST.SV.Ligero_Terms (A_Max);
      B_Vec    : Element_Array (0 .. B_Last);
      Lqc      : LV.ST.SV.Lqc_Array (0 .. Lqc_Last);
      BQ       : Element_Array (0 .. Lqc_Last);
   end record;

   type Work_Access is access Work;

   procedure Free_Work is
     new Ada.Unchecked_Deallocation (Work, Work_Access);

   procedure Verify
     (Label : Byte_Array;
      Id    : Bytes_32;
      Cfg   : Config;
      P     : Packed_Circuit;
      Pub   : Element_Array;
      B     : Byte_Array;
      St    : out Status)
   is
      use type LV.ST.Status;
      S  : constant Shape := Shape_Of (P);
      NW : constant Natural := Witness_Count (S);
      G  : constant Valid_Geometry := Geometry_Of (Cfg, S);
   begin
      pragma Assert
        (S.Npublic = P.Npublic and then S.Last_Layer = P.Last_Layer);
      if Pub'Length /= P.Npublic then
         St := Public_Input_Length;
         return;
      end if;
      if P.Npublic > 0 and then Pub (0) /= LV.ST.SA.One then
         St := Public_Input_Not_One;
         return;
      end if;
      pragma Assert
        (Pub'Length = P.Npublic
         and then (P.Npublic = 0 or else Pub (0) = LV.ST.SA.One));
      if not LV.LP.Fits (G) then
         St := Proof_Encoding;
         return;
      end if;
      declare
         Root : Bytes_32;
         St2  : LV.ST.Status;
         W    : Work_Access := new Work'
           (Sum_Last    => LV.ST.SV.Proof_Total (S) - 1,
            Ldt_Last    => G.Block_Len - 1,
            Linear_Last => G.Dblock_Len - 1,
            Low_Last    => G.Num_Queries - 1,
            High_Last   => G.Dblock_Len - G.Block_Len - 1,
            Nonce_Last  => G.Num_Queries - 1,
            Col_Last    => LV.LP.Opened (G) - 1,
            Path_Last   => 2 * Num_Leaves (G) - 1,
            Ch_Last     => LV.ST.SV.Chal_Total (S) - 1,
            A_Max       => LV.ST.SV.A_Bound (S),
            B_Last      => S.Last_Layer + 1,
            Lqc_Last    => S.Last_Layer,
            Sumcheck    => (Last  => LV.ST.SV.Proof_Total (S) - 1,
                            Evals => [others => Zero]),
            Lig         => (Ldt_Last    => G.Block_Len - 1,
                            Linear_Last => G.Dblock_Len - 1,
                            Low_Last    => G.Num_Queries - 1,
                            High_Last   => G.Dblock_Len - G.Block_Len - 1,
                            Nonce_Last  => G.Num_Queries - 1,
                            Col_Last    => LV.LP.Opened (G) - 1,
                            Path_Last   => 2 * Num_Leaves (G) - 1,
                            Ldt_Poly    => [others => Zero],
                            Linear_Poly => [others => Zero],
                            Quad_Low    => [others => Zero],
                            Quad_High   => [others => Zero],
                            Nonces      => [others => [others => 0]],
                            Columns     => [others => Zero],
                            Path        => [others => [others => 0]],
                            Path_Count  => 0),
            Ch          => (Last        => LV.ST.SV.Chal_Total (S) - 1,
                            G           => [others => Zero],
                            Layer       => [others => Zero],
                            Alpha_Input => Zero),
            A           => (Max        => LV.ST.SV.A_Bound (S),
                            Count      => 0,
                            Coeff      => [others => Zero],
                            Constraint => [others => 0],
                            Witness    => [others => 0]),
            B_Vec       => [others => Zero],
            Lqc         => [others => (X => 0, Y => 0, Z => 0)],
            BQ          => [others => Zero]);
      begin
         Read_Proof (B, S, G, Root, W.Sumcheck, W.Lig, St);
         if St /= Ok then
            Free_Work (W);
            return;
         end if;
         LV.ST.Replay_Challenges
           (Label, Root, Id, S, Pub, W.Sumcheck, W.Ch, St2);
         if St2 /= LV.ST.Ok then
            St := Exhausted;
            Free_Work (W);
            return;
         end if;
         Bound_Quads (P, S, W.Ch, W.BQ);
         --  The bound quads the core receives are those of the
         --  challenges (ADR 0071), computed from the packed circuit; the
         --  core reads the shape only.
         pragma Assert
           (Proof_Only =>
              (for all J in 0 .. S.Last_Layer =>
                 Same (W.BQ (J),
                       LV.ST.SV.BQ_Ref (PH.PC.Expand (P), W.Ch, J))));
         LV.ST.SV.Verifier_Core
           (S, Pub, W.Sumcheck, W.Ch, W.BQ, W.A, W.B_Vec, W.Lqc);
         --  The terms and triples of the core lie below the slots of
         --  the constraint vector: Witness_Count <= NWROW * WR <= the
         --  vector's length, and every pad of layer J ends below
         --  Witness_Count.
         LV.Lemma_Vector_Len_Covers (G);
         LV.ST.SV.Lemma_Pads_Below (S);
         LV.Verify (Cfg, NW, W.B_Vec, Root, W.Lig, W.A,
                    Default_Statement_Hash, W.Lqc, St);
         pragma Assert
           (St not in Queried_Columns_Length | Polynomial_Lengths);
         Free_Work (W);
      end;
   end Verify;

end Zk_Verifier;
