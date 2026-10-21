pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;
with Merkle;

package body Zk_Verifier is

   use LV.ST.SA.F;

   procedure Read_Proof
     (B        : Byte_Array;
      C        : Circuit;
      G        : Valid_Geometry;
      Root     : out Bytes_32;
      Sumcheck : out Sumcheck_Proof;
      Lig      : out Ligero_Part;
      St       : out Status)
   is
      SL   : constant Natural := Sumcheck_Len (C);
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
         LV.ST.Read_Sumcheck_Proof (SB, C, Sumcheck, St2);
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
      Lqc_Last    : Natural)
   is record
      Sumcheck : Sumcheck_Proof (Sum_Last);
      Lig      : Ligero_Part (Ldt_Last, Linear_Last, Low_Last, High_Last,
                              Nonce_Last, Col_Last, Path_Last);
      Ch       : LV.ST.SV.Challenges (Ch_Last);
      A        : LV.ST.SV.Ligero_Terms (A_Max);
      B_Vec    : Element_Array (0 .. B_Last);
      Lqc      : LV.ST.SV.Lqc_Array (0 .. Lqc_Last);
   end record;

   type Work_Access is access Work;

   procedure Free_Work is
     new Ada.Unchecked_Deallocation (Work, Work_Access);

   procedure Verify
     (Label : Byte_Array;
      Id    : Bytes_32;
      Cfg   : Config;
      C     : Circuit;
      Pub   : Element_Array;
      B     : Byte_Array;
      St    : out Status)
   is
      use type LV.ST.Status;
      NW : constant Natural := Witness_Count (C);
      G  : constant Valid_Geometry := Geometry_Of (Cfg, C);
   begin
      if Pub'Length /= C.Npublic then
         St := Public_Input_Length;
         return;
      end if;
      if C.Npublic > 0 and then Pub (0) /= LV.ST.SA.One then
         St := Public_Input_Not_One;
         return;
      end if;
      if not LV.LP.Fits (G) then
         St := Proof_Encoding;
         return;
      end if;
      declare
         Root : Bytes_32;
         St2  : LV.ST.Status;
         W    : Work_Access := new Work'
           (Sum_Last    => LV.ST.SV.Proof_Total (C) - 1,
            Ldt_Last    => G.Block_Len - 1,
            Linear_Last => G.Dblock_Len - 1,
            Low_Last    => G.Num_Queries - 1,
            High_Last   => G.Dblock_Len - G.Block_Len - 1,
            Nonce_Last  => G.Num_Queries - 1,
            Col_Last    => LV.LP.Opened (G) - 1,
            Path_Last   => 2 * Num_Leaves (G) - 1,
            Ch_Last     => LV.ST.SV.Chal_Total (C) - 1,
            A_Max       => LV.ST.SV.A_Bound (C),
            B_Last      => C.Last_Layer + 1,
            Lqc_Last    => C.Last_Layer,
            Sumcheck    => (Last  => LV.ST.SV.Proof_Total (C) - 1,
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
            Ch          => (Last        => LV.ST.SV.Chal_Total (C) - 1,
                            G           => [others => Zero],
                            Layer       => [others => Zero],
                            Alpha_Input => Zero),
            A           => (Max        => LV.ST.SV.A_Bound (C),
                            Count      => 0,
                            Coeff      => [others => Zero],
                            Constraint => [others => 0],
                            Witness    => [others => 0]),
            B_Vec       => [others => Zero],
            Lqc         => [others => (X => 0, Y => 0, Z => 0)]);
      begin
         Read_Proof (B, C, G, Root, W.Sumcheck, W.Lig, St);
         if St /= Ok then
            Free_Work (W);
            return;
         end if;
         LV.ST.Replay_Challenges
           (Label, Root, Id, C, Pub, W.Sumcheck, W.Ch, St2);
         if St2 /= LV.ST.Ok then
            St := Exhausted;
            Free_Work (W);
            return;
         end if;
         LV.ST.SV.Verifier_Core
           (C, Pub, W.Sumcheck, W.Ch, W.A, W.B_Vec, W.Lqc);
         --  The terms and triples of the core lie below the slots of
         --  the constraint vector: Witness_Count <= NWROW * WR <= the
         --  vector's length, and every pad of layer J ends below
         --  Witness_Count.
         LV.Lemma_Vector_Len_Covers (G);
         LV.ST.SV.Lemma_Pads_Below (C);
         LV.Verify (Cfg, NW, W.B_Vec, Root, W.Lig, W.A,
                    Default_Statement_Hash, W.Lqc, St);
         Free_Work (W);
      end;
   end Verify;

end Zk_Verifier;
