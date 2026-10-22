pragma SPARK_Mode (On);

package body Lagrange is

   ----------------------------------------------------------------------
   --  One step of each hidden reference
   ----------------------------------------------------------------------

   procedure Lemma_Diff_Step (A, I, N : Natural) with
     Ghost => Proof_Only,
     Global => null,
     Pre    => A <= F.Max_Eval_Point and then N < Max_K
               and then N <= F.Max_Eval_Point,
     Post   =>
       (if N = I then
          Same (Diff_Product_Ref (A, I, N + 1), Diff_Product_Ref (A, I, N))
        else
          Same (Diff_Product_Ref (A, I, N + 1),
                Diff_Product_Ref (A, I, N) * (Pt (A) - Pt (N))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         Diff_Product_Ref);
   begin
      null;
   end Lemma_Diff_Step;

   procedure Lemma_Dot_Step
     (Coeffs : Element_Array; T : Table; C : Natural; N : Natural)
   with
     Ghost => Proof_Only,
     Global => null,
     Pre    => Coeffs'First = 0 and then T'First (1) = 0
               and then Coeffs'Length = T'Length (1)
               and then Coeffs'Length <= Max_K
               and then N < Coeffs'Length
               and then C in T'Range (2),
     Post   =>
       Same (Dot_Ref (Coeffs, T, C, N + 1),
             Dot_Ref (Coeffs, T, C, N) + Coeffs (N) * T (N, C))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Dot_Ref);
   begin
      null;
   end Lemma_Dot_Step;

   procedure Lemma_Diff_Zero (A, I : Natural) with
     Ghost => Proof_Only,
     Global => null,
     Pre    => A <= F.Max_Eval_Point,
     Post   => Same (Diff_Product_Ref (A, I, 0), One)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         Diff_Product_Ref);
   begin
      null;
   end Lemma_Diff_Zero;

   --  The product over j in L .. N - 1 of Pt (A) - Pt (j), folded from
   --  the right, the last factor alone: with N = K, the suffix of row
   --  L - 1 at the column A (ADR 0066). Recursive, hidden.
   function Seg_Ref (A, L, N : Natural) return Element is
     (if L + 1 >= N then Pt (A) - Pt (L)
      else (Pt (A) - Pt (L)) * Seg_Ref (A, L + 1, N))
   with Ghost => Proof_Only,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => A <= F.Max_Eval_Point and then N <= Max_K
               and then N - 1 <= F.Max_Eval_Point and then L < N,
        Subprogram_Variant => (Decreases => N - L);

   procedure Lemma_Seg_Last (A, N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => A <= F.Max_Eval_Point and then N <= Max_K and then N >= 1
               and then N - 1 <= F.Max_Eval_Point,
     Post   => Same (Seg_Ref (A, N - 1, N), Pt (A) - Pt (N - 1))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Seg_Ref);
   begin
      null;
   end Lemma_Seg_Last;

   procedure Lemma_Seg_Step (A, L, N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => A <= F.Max_Eval_Point and then N <= Max_K
               and then N - 1 <= F.Max_Eval_Point and then L < N - 1,
     Post   =>
       Same (Seg_Ref (A, L, N), (Pt (A) - Pt (L)) * Seg_Ref (A, L + 1, N))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Seg_Ref);
   begin
      null;
   end Lemma_Seg_Step;

   --  Below the skipped index the product does not depend on it.
   procedure Lemma_Diff_Late (A, I1, I2, N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => A <= F.Max_Eval_Point and then N <= Max_K
               and then (N = 0 or else N - 1 <= F.Max_Eval_Point)
               and then N <= I1 and then N <= I2,
     Post   =>
       Same (Diff_Product_Ref (A, I1, N), Diff_Product_Ref (A, I2, N)),
     Subprogram_Variant => (Decreases => N)
   is
   begin
      if N = 0 then
         Lemma_Diff_Zero (A, I1);
         Lemma_Diff_Zero (A, I2);
      else
         Lemma_Diff_Late (A, I1, I2, N - 1);
         Lemma_Diff_Step (A, I1, N - 1);
         Lemma_Diff_Step (A, I2, N - 1);
      end if;
   end Lemma_Diff_Late;

   --  The product of row I is its prefix up to L times the suffix from
   --  L, for every L between I and K: associativity, step by step.
   procedure Lemma_Split (A, I, L, K : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => A <= F.Max_Eval_Point and then K <= Max_K
               and then K - 1 <= F.Max_Eval_Point
               and then I < L and then L < K,
     Post   =>
       Same (Diff_Product_Ref (A, I, K),
             Diff_Product_Ref (A, I, L) * Seg_Ref (A, L, K)),
     Subprogram_Variant => (Decreases => K - L)
   is
   begin
      if L = K - 1 then
         Lemma_Seg_Last (A, K);
         Lemma_Diff_Step (A, I, K - 1);
      else
         Lemma_Split (A, I, L + 1, K);
         Lemma_Seg_Step (A, L, K);
         Lemma_Diff_Step (A, I, L);
         F.Lemma_Mul_Assoc
           (Diff_Product_Ref (A, I, L), Pt (A) - Pt (L),
            Seg_Ref (A, L + 1, K));
      end if;
   end Lemma_Split;

   procedure Lemma_Dot_Zero
     (Coeffs : Element_Array; T : Table; C : Natural)
   with
     Ghost => Proof_Only,
     Global => null,
     Pre    => Coeffs'First = 0 and then T'First (1) = 0
               and then Coeffs'Length = T'Length (1)
               and then Coeffs'Length <= Max_K
               and then C in T'Range (2),
     Post   => Same (Dot_Ref (Coeffs, T, C, 0), Zero)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Dot_Ref);
   begin
      null;
   end Lemma_Dot_Zero;

   ----------------------------------------------------------------------
   --  The code
   ----------------------------------------------------------------------

   function Diff_Product (A, I, N : Natural) return Element is
      P : Element := One;
   begin
      Lemma_Diff_Zero (A, I);
      for J in 0 .. N - 1 loop
         pragma Loop_Invariant
           (Proof_Only => Same (P, Diff_Product_Ref (A, I, J)));
         Lemma_Diff_Step (A, I, J);
         if J /= I then
            P := P * (Pt (A) - Pt (J));
         end if;
      end loop;
      return P;
   end Diff_Product;

   --  Column C of the table (ADR 0066): a backward pass leaves the
   --  suffix of row I in T (I, C) for every row but the last, a forward
   --  pass carries the prefix P and writes prefix times suffix times the
   --  row's inverse (the last row has no suffix). The other columns stay.
   procedure Fill_Column
     (K     : Positive;
      C     : Natural;
      Cols  : Column_Array;
      Inv_D : Element_Array;
      T     : in out Table)
   with
     Global => null,
     Pre    =>
       K <= Max_K and then K - 1 <= F.Max_Eval_Point
       and then Cols'First = 0 and then Cols'Length <= Max_Columns
       and then C in Cols'Range
       and then (for all C2 in Cols'Range =>
                   Cols (C2) in K .. F.Max_Eval_Point)
       and then Inv_D'First = 0 and then Inv_D'Last = K - 1
       and then T'First (1) = 0 and then T'Last (1) = K - 1
       and then T'First (2) = 0 and then T'Last (2) = Cols'Last,
     Post   =>
       (Proof_Only =>
          (for all I in 0 .. K - 1 =>
             Same (T (I, C), Diff_Product_Ref (Cols (C), I, K) * Inv_D (I)))
          and then
            (for all I2 in T'Range (1) =>
               (for all C2 in T'Range (2) =>
                  (if C2 /= C then Same (T (I2, C2), T'Old (I2, C2))))))
   is
      A : constant Natural := Cols (C);
      X : constant Element := Pt (A);
      P : Element := One;
   begin
      for I in reverse 0 .. K - 2 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all I2 in I + 1 .. K - 2 =>
                 Same (T (I2, C), Seg_Ref (A, I2 + 1, K)))
              and then
                (for all I2 in T'Range (1) =>
                   (for all C2 in T'Range (2) =>
                      (if C2 /= C
                       then Same (T (I2, C2), T'Loop_Entry (I2, C2))))));
         if I = K - 2 then
            Lemma_Seg_Last (A, K);
            T (I, C) := X - Pt (I + 1);
         else
            Lemma_Seg_Step (A, I + 1, K);
            T (I, C) := (X - Pt (I + 1)) * T (I + 1, C);
         end if;
      end loop;
      Lemma_Diff_Zero (A, K);
      for I in 0 .. K - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              Same (P, Diff_Product_Ref (A, K, I))
              and then
                (for all I2 in 0 .. I - 1 =>
                   Same (T (I2, C), Diff_Product_Ref (A, I2, K) * Inv_D (I2)))
              and then
                (for all I2 in I .. K - 2 =>
                   Same (T (I2, C), Seg_Ref (A, I2 + 1, K)))
              and then
                (for all I2 in T'Range (1) =>
                   (for all C2 in T'Range (2) =>
                      (if C2 /= C
                       then Same (T (I2, C2), T'Loop_Entry (I2, C2))))));
         Lemma_Diff_Step (A, I, I);
         Lemma_Diff_Late (A, I, K, I);
         Lemma_Diff_Step (A, K, I);
         if I = K - 1 then
            T (I, C) := P * Inv_D (I);
         else
            Lemma_Split (A, I, I + 1, K);
            T (I, C) := (P * T (I, C)) * Inv_D (I);
         end if;
         P := P * (X - Pt (I));
      end loop;
   end Fill_Column;

   procedure Build
     (K     : Positive;
      Cols  : Column_Array;
      T     : out Table;
      Inv_D : out Element_Array;
      Ok    : out Boolean)
   is
      D   : Element;
      Acc : Boolean;
   begin
      T     := [others => [others => Zero]];
      Inv_D := [others => Zero];
      Ok    := True;
      --  The inverses of the k denominators, each checked (ADR 0037).
      for I in 0 .. K - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all I2 in 0 .. I - 1 =>
                 Inv_D (I2) * Diff_Product_Ref (I2, I2, K) = One));
         D := Diff_Product (I, I, K);
         F.Checked_Inv (D, Inv_D (I), Acc);
         if not Acc then
            Ok := False;
            return;
         end if;
      end loop;
      --  The entries at the queried columns, column by column.
      for C in Cols'Range loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all I2 in 0 .. K - 1 =>
                 (for all C2 in 0 .. C - 1 =>
                    Same (T (I2, C2),
                          Diff_Product_Ref (Cols (C2), I2, K) * Inv_D (I2)))));
         Fill_Column (K, C, Cols, Inv_D, T);
      end loop;
   end Build;

   function Evaluate
     (Coeffs : Element_Array; T : Table; C : Natural) return Element
   is
      Sum : Element := Zero;
   begin
      Lemma_Dot_Zero (Coeffs, T, C);
      for N in 0 .. Coeffs'Length - 1 loop
         pragma Loop_Invariant
           (Proof_Only => Same (Sum, Dot_Ref (Coeffs, T, C, N)));
         Lemma_Dot_Step (Coeffs, T, C, N);
         Sum := Sum + Coeffs (N) * T (N, C);
      end loop;
      return Sum;
   end Evaluate;

end Lagrange;
