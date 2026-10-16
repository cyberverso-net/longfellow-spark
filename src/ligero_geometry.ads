--  Ligero_Geometry: the parameters and the tableau layout of draft
--  Section 4.2 and 4.3 (LigeroConfig, LigeroGeometry::new and its row
--  indices in ligero/common.rs of the reference at d5e6be7). Pure
--  arithmetic, no field.
--
--  Documentation: docs/guide/05-ligero.md. Decisions: ADR 0035 (scope),
--  0038 (Gold: the inequalities of 4.2.1 as postconditions, every row
--  index in range), 0039 (sizes); frame: ADR 0003, 0020. Index:
--  docs/adr/README.md.
--
--  Proof status. Make : Gold, the fields of the geometry are the
--  formulas of LigeroGeometry::new and satisfy the constraints of
--  Section 4.2.1, stated once as the predicate Consistent of the
--  subtype Valid_Geometry, so that every unit taking a Valid_Geometry
--  has them. The row index functions are Gold trivially (below
--  Total_Rows). Valid is the executable form of 4.2.1 on a
--  configuration; a configuration that fails it is the caller's error,
--  checked before anything is sized.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0037.

pragma SPARK_Mode (On);

package Ligero_Geometry is

   --  Bounds (ADR 0039): the encoded length (NCOL) is also the range
   --  of the Reed-Solomon evaluation points, below 2^16 on GF(2^128);
   --  Max_Witnesses covers Max_Wires of stage 3 plus the pads.
   Max_Encoded_Len : constant := 2**16;
   Max_Queries     : constant := 2**12;
   Max_Rate_Inv    : constant := 2**16;
   Max_Witnesses   : constant := 2**25;
   Max_Quads       : constant := 2**20;

   --  Section 4.2: rate, number of opened columns, encoded length.
   type Config is record
      Rate_Inv    : Positive;
      Num_Queries : Positive;
      Encoded_Len : Positive;
   end record;

   --  BLOCK = (NCOL + 1) / (2 + RATE_INV).
   function Block_Of (C : Config) return Natural is
     ((C.Encoded_Len + 1) / (2 + C.Rate_Inv))
   with Pre => C.Encoded_Len <= Max_Encoded_Len
               and then C.Rate_Inv <= Max_Rate_Inv;

   --  Section 4.2.1 on a configuration: BLOCK > 0, NCOL >= DBLOCK,
   --  NCOL - DBLOCK >= NREQ, BLOCK > NREQ (hence WR > 0).
   function Valid (C : Config) return Boolean is
     (C.Encoded_Len <= Max_Encoded_Len
      and then C.Rate_Inv <= Max_Rate_Inv
      and then C.Num_Queries <= Max_Queries
      and then Block_Of (C) > 0
      and then C.Encoded_Len >= 2 * Block_Of (C) - 1
      and then C.Encoded_Len - (2 * Block_Of (C) - 1) >= C.Num_Queries
      and then Block_Of (C) > C.Num_Queries);

   type Geometry is record
      Num_Witnesses     : Natural;
      Block_Len         : Natural;
      Encoded_Len       : Natural;
      Dblock_Len        : Natural;
      Num_Queries       : Natural;
      Witnesses_Per_Row : Natural;
      Num_Witness_Rows  : Natural;
      Num_Quad_Rows     : Natural;
      Total_Rows        : Natural;
   end record;

   --  What Make establishes, and what every user of a geometry may
   --  assume: the formulas of LigeroGeometry::new and the constraints
   --  of 4.2.1.
   function Consistent (G : Geometry) return Boolean is
     (G.Encoded_Len <= Max_Encoded_Len
      and then G.Block_Len <= Max_Encoded_Len
      and then G.Num_Queries in 1 .. Max_Queries
      and then G.Num_Witnesses <= Max_Witnesses
      and then G.Block_Len > G.Num_Queries
      and then G.Dblock_Len = 2 * G.Block_Len - 1
      and then G.Encoded_Len >= G.Dblock_Len
      and then G.Encoded_Len - G.Dblock_Len >= G.Num_Queries
      and then G.Witnesses_Per_Row = G.Block_Len - G.Num_Queries
      and then G.Num_Witness_Rows
               = (G.Num_Witnesses + G.Witnesses_Per_Row - 1)
                 / G.Witnesses_Per_Row
      and then G.Num_Quad_Rows <= Max_Quads
      and then G.Total_Rows
               = 3 + G.Num_Witness_Rows + 3 * G.Num_Quad_Rows);

   subtype Valid_Geometry is Geometry with
     Dynamic_Predicate => Consistent (Valid_Geometry);

   --  LigeroGeometry::new (C, NW, NQ).
   function Make (C : Config; NW : Natural; NQ : Natural) return Valid_Geometry
   with
     Global => null,
     Pre    => Valid (C) and then NW <= Max_Witnesses and then NQ <= Max_Quads,
     Post   =>
       Make'Result.Num_Witnesses = NW
       and then Make'Result.Encoded_Len = C.Encoded_Len
       and then Make'Result.Num_Queries = C.Num_Queries
       and then Make'Result.Block_Len = Block_Of (C)
       and then Make'Result.Num_Quad_Rows
                = (NQ + Make'Result.Witnesses_Per_Row - 1)
                  / Make'Result.Witnesses_Per_Row;

   --  Section 4.3: the rows of the tableau.
   function Ldt_Row (G : Valid_Geometry) return Natural is (0);
   function Linear_Row (G : Valid_Geometry) return Natural is (1);
   function Quad_Row (G : Valid_Geometry) return Natural is (2);
   function Witness_Row_Start (G : Valid_Geometry) return Natural is (3);

   function Quad_X_Row_Start (G : Valid_Geometry) return Natural is
     (3 + G.Num_Witness_Rows);

   function Quad_Y_Row_Start (G : Valid_Geometry) return Natural is
     (3 + G.Num_Witness_Rows + G.Num_Quad_Rows);

   function Quad_Z_Row_Start (G : Valid_Geometry) return Natural is
     (3 + G.Num_Witness_Rows + 2 * G.Num_Quad_Rows);

   --  The committed columns: NCOL - DBLOCK leaves of the Merkle tree.
   function Num_Leaves (G : Valid_Geometry) return Natural is
     (G.Encoded_Len - G.Dblock_Len)
   with Post => Num_Leaves'Result >= G.Num_Queries;

   --  Rows NQW = NROW - 3 of the low-degree test (witness and quadratic).
   function Num_Wq_Rows (G : Valid_Geometry) return Natural is
     (G.Num_Witness_Rows + 3 * G.Num_Quad_Rows);

end Ligero_Geometry;
