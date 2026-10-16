--  Lagrange: the Reed-Solomon code of the Ligero commitment by Lagrange
--  interpolation (ADR 0036), as lagrange_matrix and encode_row of the
--  reference (docs/specs/rust/src/algebra/interpolation.rs and
--  ligero/reed_solomon.rs at d5e6be7), restricted to the columns the
--  verifier reads. Generic over a field.
--
--  The code of length n and dimension k interpolates k values at the
--  evaluation points Pt (0) .. Pt (k - 1) and evaluates the polynomial
--  at Pt (x) for every column x < n. The matrix entry L (i, x) is the
--  identity block for x < k, otherwise the product over j /= i of
--  (Pt (x) - Pt (j)) times the inverse of the product over j /= i of
--  (Pt (i) - Pt (j)), products from One in the order j = 0 .. k - 1.
--  encode_row (c) (x) is the sum over i of c (i) L (i, x), from Zero
--  in the order i = 0 .. k - 1. The verifier needs L at the NREQ
--  queried columns only, all at or beyond DBLOCK >= k, so the identity
--  block never enters: Build fills a table of k rows and one column
--  per queried column x >= k, once per geometry, and Evaluate is
--  encode_row at one of those columns. (The identity block of the
--  reference's matrix exists in the test generator, where the
--  interpolation property is checked.)
--
--  Documentation: docs/guide/05-ligero.md. Decisions: ADR 0036, 0037
--  (Checked_Inv for the denominators), 0038 (structural Gold), 0039
--  (sizes); frame: ADR 0023, 0024. Index: docs/adr/README.md.
--
--  Proof status (per instance). Diff_Product, Build and Evaluate are
--  Gold, structural (ADR 0023): equal, through Same, to the ghost
--  references Diff_Product_Ref and Dot_Ref, which transcribe the
--  reference's loops; the inverses of Build satisfy Inv_D (i) times
--  the denominator = One by Checked_Inv. The interpolation property
--  (the code agrees with its input at the first k points) is tested
--  (ADR 0040), not proved.
--
--  The structural contracts are proof-only: they sit at the project's
--  assertion level Proof_Only (Proof_Levels), proved for all inputs
--  and never compiled, because the assertion-enabled test build could
--  not afford them (at the time every P-256 multiplication executed
--  its big-integer postcondition, since moved to the same level by
--  ADR 0044, and a recursive reference in a loop invariant is
--  recomputed at every iteration: a table of dimension 10 on P-256
--  took over ten minutes). What the test build checks of this package
--  is its output against the vectors. Preconditions stay executable.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0037.

pragma SPARK_Mode (On);

with Proof_Levels;
with Field_Signature;

generic
   with package F is new Field_Signature (<>);
package Lagrange is

   use F;

   subtype Element is F.Element;

   type Element_Array is array (Natural range <>) of Element;

   --  Column positions x of the code, as the verifier queries them.
   type Column_Array is array (Natural range <>) of Natural;

   --  Row i (a coefficient index below k), column c (a queried column).
   type Table is array (Natural range <>, Natural range <>) of Element;

   --  Bounds (ADR 0039): k is at most DBLOCK < NCOL, the number of
   --  queried columns at most Max_Queries of the geometry.
   Max_K       : constant := 2**16 - 1;
   Max_Columns : constant := 2**12;

   --  The evaluation point of column X (reed_solomon_eval_point).
   function Pt (X : Natural) return Element is (F.Eval_Point (X))
   with Pre => X <= F.Max_Eval_Point;

   --  The product over j in 0 .. N - 1, j /= I, of Pt (A) - Pt (j),
   --  from One, j ascending: the denominator of row I when A = I, the
   --  numerator of entry (I, x) when A = x. Recursive, hence hidden
   --  (see Bytes.Add_Zeros); the step lemmas of the body unhide it.
   function Diff_Product_Ref (A, I, N : Natural) return Element is
     (if N = 0 then One
      elsif N - 1 = I then Diff_Product_Ref (A, I, N - 1)
      else Diff_Product_Ref (A, I, N - 1) * (Pt (A) - Pt (N - 1)))
   with Ghost => Proof_Only,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => A <= F.Max_Eval_Point and then N <= Max_K
               and then (N = 0 or else N - 1 <= F.Max_Eval_Point),
        Subprogram_Variant => (Decreases => N);

   function Diff_Product (A, I, N : Natural) return Element with
     Global => null,
     Pre    => A <= F.Max_Eval_Point and then N <= Max_K
               and then (N = 0 or else N - 1 <= F.Max_Eval_Point),
     Post   =>
       (Proof_Only => Same (Diff_Product'Result, Diff_Product_Ref (A, I, N)));

   --  The table for dimension K at the columns Cols, all at or beyond
   --  K: T (i, c) is L (i, Cols (c)); Inv_D (i) the checked inverse of
   --  the denominator of row i. Ok is False, with the outputs
   --  unspecified, when a denominator could not be inverted (ADR
   --  0037), which does not happen on a correct field since the points
   --  are distinct.
   procedure Build
     (K     : Positive;
      Cols  : Column_Array;
      T     : out Table;
      Inv_D : out Element_Array;
      Ok    : out Boolean)
   with
     Global => null,
     Pre    =>
       K <= Max_K and then K - 1 <= F.Max_Eval_Point
       and then Cols'First = 0 and then Cols'Length <= Max_Columns
       and then (for all C in Cols'Range =>
                   Cols (C) in K .. F.Max_Eval_Point)
       and then T'First (1) = 0 and then T'Last (1) = K - 1
       and then T'First (2) = 0 and then T'Last (2) = Cols'Last
       and then Inv_D'First = 0 and then Inv_D'Last = K - 1,
     Post   =>
       (Proof_Only =>
          (if Ok then
             (for all I in 0 .. K - 1 =>
                Inv_D (I) * Diff_Product_Ref (I, I, K) = One)
             and then
               (for all I in 0 .. K - 1 =>
                  (for all C in Cols'Range =>
                     Same (T (I, C),
                           Diff_Product_Ref (Cols (C), I, K) * Inv_D (I))))));

   --  The sum over i in 0 .. N - 1 of Coeffs (i) * T (i, C), from
   --  Zero, i ascending (encode_row at column C). Recursive, hidden.
   function Dot_Ref
     (Coeffs : Element_Array; T : Table; C : Natural; N : Natural)
      return Element
   is
     (if N = 0 then Zero
      else Dot_Ref (Coeffs, T, C, N - 1)
           + Coeffs (N - 1) * T (N - 1, C))
   with Ghost => Proof_Only,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => Coeffs'First = 0 and then T'First (1) = 0
               and then Coeffs'Length = T'Length (1)
               and then Coeffs'Length <= Max_K
               and then N <= Coeffs'Length
               and then C in T'Range (2),
        Subprogram_Variant => (Decreases => N);

   --  encode_row (Coeffs) at the queried column C of T.
   function Evaluate
     (Coeffs : Element_Array; T : Table; C : Natural) return Element
   with
     Global => null,
     Pre    => Coeffs'First = 0 and then T'First (1) = 0
               and then Coeffs'Length = T'Length (1)
               and then Coeffs'Length <= Max_K
               and then C in T'Range (2),
     Post   =>
       (Proof_Only =>
          Same (Evaluate'Result, Dot_Ref (Coeffs, T, C, Coeffs'Length)));

end Lagrange;
