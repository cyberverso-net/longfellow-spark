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

   --  Row I of the table: the numerator times the row's inverse at
   --  every queried column. The other rows stay.
   procedure Fill_Row
     (K     : Positive;
      I     : Natural;
      Cols  : Column_Array;
      Inv_I : Element;
      T     : in out Table)
   with
     Global => null,
     Pre    =>
       K <= Max_K and then K - 1 <= F.Max_Eval_Point and then I < K
       and then Cols'First = 0 and then Cols'Length <= Max_Columns
       and then (for all C in Cols'Range => Cols (C) in K .. F.Max_Eval_Point)
       and then T'First (1) = 0 and then T'Last (1) = K - 1
       and then T'First (2) = 0 and then T'Last (2) = Cols'Last,
     Post   =>
       (Proof_Only =>
          (for all C in Cols'Range =>
             Same (T (I, C), Diff_Product_Ref (Cols (C), I, K) * Inv_I))
          and then
            (for all I2 in T'Range (1) =>
               (if I2 /= I then
                  (for all C in T'Range (2) =>
                     Same (T (I2, C), T'Old (I2, C))))))
   is
   begin
      for C in Cols'Range loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all C2 in 0 .. C - 1 =>
                 Same (T (I, C2), Diff_Product_Ref (Cols (C2), I, K) * Inv_I))
              and then
                (for all I2 in T'Range (1) =>
                   (if I2 /= I then
                      (for all C2 in T'Range (2) =>
                         Same (T (I2, C2), T'Loop_Entry (I2, C2))))));
         T (I, C) := Diff_Product (Cols (C), I, K) * Inv_I;
      end loop;
   end Fill_Row;

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
      --  The entries at the queried columns, row by row.
      for I in 0 .. K - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all I2 in 0 .. I - 1 =>
                 (for all C in Cols'Range =>
                    Same (T (I2, C),
                          Diff_Product_Ref (Cols (C), I2, K) * Inv_D (I2)))));
         Fill_Row (K, I, Cols, Inv_D (I), T);
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
