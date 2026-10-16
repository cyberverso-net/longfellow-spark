pragma SPARK_Mode (On);

package body Ligero_Geometry is

   function Make (C : Config; NW : Natural; NQ : Natural) return Valid_Geometry
   is
      Block  : constant Natural := Block_Of (C);
      Dblock : constant Natural := 2 * Block - 1;
      WR     : constant Natural := Block - C.Num_Queries;
      NWROW  : constant Natural := (NW + WR - 1) / WR;
      NQT    : constant Natural := (NQ + WR - 1) / WR;
   begin
      return (Num_Witnesses     => NW,
              Block_Len         => Block,
              Encoded_Len       => C.Encoded_Len,
              Dblock_Len        => Dblock,
              Num_Queries       => C.Num_Queries,
              Witnesses_Per_Row => WR,
              Num_Witness_Rows  => NWROW,
              Num_Quad_Rows     => NQT,
              Total_Rows        => 3 + NWROW + 3 * NQT);
   end Make;

   procedure Lemma_Rows_Cover (G : Valid_Geometry) is
   begin
      null;
   end Lemma_Rows_Cover;

end Ligero_Geometry;
