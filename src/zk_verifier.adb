pragma SPARK_Mode (On);

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
      if not LV.LP.Fits (G) then
         St := Proof_Encoding;
         return;
      end if;
      declare
         Root     : Bytes_32;
         Sumcheck : Sumcheck_Proof (Last => LV.ST.SV.Proof_Total (C) - 1);
         Lig      : Ligero_Part
           (Ldt_Last    => G.Block_Len - 1,
            Linear_Last => G.Dblock_Len - 1,
            Low_Last    => G.Num_Queries - 1,
            High_Last   => G.Dblock_Len - G.Block_Len - 1,
            Nonce_Last  => G.Num_Queries - 1,
            Col_Last    => LV.LP.Opened (G) - 1,
            Path_Last   => 2 * Num_Leaves (G) - 1);
         Ch       : LV.ST.SV.Challenges
           (Last => LV.ST.SV.Chal_Total (C) - 1);
         A        : LV.ST.SV.Ligero_Terms (Max => LV.ST.SV.A_Bound (C));
         B_Vec    : Element_Array (0 .. C.Last_Layer + 1);
         Lqc      : LV.ST.SV.Lqc_Array (0 .. C.Last_Layer);
         St2      : LV.ST.Status;
      begin
         Read_Proof (B, C, G, Root, Sumcheck, Lig, St);
         if St /= Ok then
            return;
         end if;
         LV.ST.Replay_Challenges (Label, Root, Id, C, Pub, Sumcheck, Ch, St2);
         if St2 /= LV.ST.Ok then
            St := Exhausted;
            return;
         end if;
         LV.ST.SV.Verifier_Core (C, Pub, Sumcheck, Ch, A, B_Vec, Lqc);
         --  The terms and triples of the core lie below the slots of
         --  the constraint vector: Witness_Count <= NWROW * WR <= the
         --  vector's length, and every pad of layer J ends below
         --  Witness_Count.
         LV.Lemma_Vector_Len_Covers (G);
         LV.ST.SV.Lemma_Pads_Below (C);
         LV.Verify (Cfg, NW, B_Vec, Root, Lig, A, Default_Statement_Hash,
                    Lqc, St);
      end;
   end Verify;

end Zk_Verifier;
