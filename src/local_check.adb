pragma SPARK_Mode (On);

with Field_GF2_128.Laws;

package body Local_Check is

   function "+" (A, B : Element) return Element is (Add (A, B));
   function "*" (A, B : Element) return Element is (Mul (A, B));

   ----------------------------------------------------------------------
   --  The laws of the wrappers: the only places that look inside them.
   ----------------------------------------------------------------------

   --  The laws are stated with Same, the logical equality of
   --  Field_GF2_128 (ADR 0066): the provers rewrite with it, which they
   --  do not do with the predefined "=" of the record.

   --  The additive laws, from those of Field_GF2_128.
   procedure Lemma_Add_Assoc (A, B, C : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same ((A + B) + C, A + (B + C))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", "+");
   begin
      Field_GF2_128.Lemma_Add_Assoc (A, B, C);
   end Lemma_Add_Assoc;

   procedure Lemma_Add_Comm (A, B : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (A + B, B + A)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", "+");
   begin
      Field_GF2_128.Lemma_Add_Comm (A, B);
   end Lemma_Add_Comm;

   procedure Lemma_Add_Zero (A : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (A + Zero, A) and then Same (Zero + A, A)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", "+");
   begin
      Field_GF2_128.Lemma_Add_Zero (A);
      Field_GF2_128.Lemma_Add_Comm (Zero, A);
   end Lemma_Add_Zero;

   --  Characteristic 2: every element is its own opposite.
   procedure Lemma_Add_Self (A : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (A + A, Zero)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", "+");
   begin
      --  A + (-A) = 0, and -A is A.
      Field_GF2_128.Lemma_Add_Neg (A);
      Field_GF2_128.Laws.Lemma_Same (Neg (A), A);
   end Lemma_Add_Self;

   --  The multiplicative laws, from those of Field_GF2_128.
   procedure Lemma_Mul_Assoc (A, B, C : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same ((A * B) * C, A * (B * C))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", "*");
   begin
      Field_GF2_128.Lemma_Mul_Assoc (A, B, C);
   end Lemma_Mul_Assoc;

   procedure Lemma_Mul_Comm (A, B : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (A * B, B * A)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", "*");
   begin
      Field_GF2_128.Lemma_Mul_Comm (A, B);
   end Lemma_Mul_Comm;

   procedure Lemma_Mul_Distrib (A, B, C : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (A * (B + C), A * B + A * C)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", "*");
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", "+");
   begin
      Field_GF2_128.Lemma_Mul_Distrib (A, B, C);
   end Lemma_Mul_Distrib;

   ----------------------------------------------------------------------
   --  Consequences, from the laws only.
   ----------------------------------------------------------------------

   --  A 0 = 0: z = A 0 = A (0 + 0) = z + z, and z + z = 0.
   procedure Lemma_Mul_Zero (A : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (A * Zero, Zero) and then Same (Zero * A, Zero)
   is
      Z : constant Element := A * Zero with Ghost => Proof_Only;
   begin
      Lemma_Add_Zero (Zero);
      Lemma_Mul_Distrib (A, Zero, Zero);
      pragma Assert (Same (Z, Z + Z));
      Lemma_Add_Self (Z);
      Lemma_Mul_Comm (Zero, A);
   end Lemma_Mul_Zero;

   --  (A + B) C = A C + B C.
   procedure Lemma_Distrib_Right (A, B, C : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same ((A + B) * C, A * C + B * C)
   is
   begin
      Lemma_Mul_Comm (A + B, C);
      Lemma_Mul_Distrib (C, A, B);
      Lemma_Mul_Comm (C, A);
      Lemma_Mul_Comm (C, B);
   end Lemma_Distrib_Right;

   --  ((A + D) X) Y = (A X) Y + (D X) Y.
   procedure Lemma_Distrib_Term (A, D, X, Y : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (((A + D) * X) * Y, (A * X) * Y + (D * X) * Y)
   is
   begin
      Lemma_Distrib_Right (A, D, X);
      Lemma_Distrib_Right (A * X, D * X, Y);
   end Lemma_Distrib_Term;

   --  ((Ca Cb) Va) Vb = (Ca Va) (Cb Vb).
   procedure Lemma_Rearrange (Ca, Cb, Va, Vb : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same (((Ca * Cb) * Va) * Vb, (Ca * Va) * (Cb * Vb))
   is
   begin
      --  (Ca Cb) Va = Ca (Cb Va) = Ca (Va Cb) = (Ca Va) Cb
      Lemma_Mul_Assoc (Ca, Cb, Va);
      Lemma_Mul_Comm (Cb, Va);
      Lemma_Mul_Assoc (Ca, Va, Cb);
      pragma Assert (Same ((Ca * Cb) * Va, (Ca * Va) * Cb));
      --  ((Ca Va) Cb) Vb = (Ca Va) (Cb Vb)
      Lemma_Mul_Assoc (Ca * Va, Cb, Vb);
   end Lemma_Rearrange;

   --  (D Y) X = (D X) Y.
   procedure Lemma_Swap (D, X, Y : Element) with
     Ghost => Proof_Only, Global => null,
     Post  => Same ((D * Y) * X, (D * X) * Y)
   is
   begin
      Lemma_Mul_Assoc (D, Y, X);
      Lemma_Mul_Comm (Y, X);
      Lemma_Mul_Assoc (D, X, Y);
   end Lemma_Swap;

   ----------------------------------------------------------------------
   --  The expansion of A * B.
   ----------------------------------------------------------------------

   --  The expansion's value, pairs taken row by row, as Collected takes
   --  them.
   function Expand_Sum
     (A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      I : Form_Count; J : Form_Count; V : Values) return Element
   is (if I = 0 then Zero
       elsif J = 0 then Expand_Sum (A, NA, B, NB, I - 1, NB, V)
       else Expand_Sum (A, NA, B, NB, I, J - 1, V)
            + ((A (I).C * B (J).C) * V (A (I).W)) * V (B (J).W))
   with Ghost => Proof_Only, Global => null,
        Pre => J <= NB and then I <= NA
               and then Form_In (A, NA, V) and then Form_In (B, NB, V),
        Subprogram_Variant => (Decreases => I, Decreases => J);

   --  Row I of the expansion, up to column J: the rows before it, plus
   --  (Ca Va) times the first J entries of B.
   procedure Lemma_Row
     (A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      I : Form_Index; J : Form_Count; V : Values)
   with Ghost => Proof_Only, Global => null,
        Pre  => I <= NA and then J <= NB
                and then Form_In (A, NA, V) and then Form_In (B, NB, V),
        Post => Same (Expand_Sum (A, NA, B, NB, I, J, V),
                      Expand_Sum (A, NA, B, NB, I - 1, NB, V)
                      + (A (I).C * V (A (I).W)) * Sum_Form (B, J, V)),
        Subprogram_Variant => (Decreases => J)
   is
      X : constant Element := A (I).C * V (A (I).W)
        with Ghost => Proof_Only;
   begin
      if J = 0 then
         Lemma_Mul_Zero (X);
         Lemma_Add_Zero (Expand_Sum (A, NA, B, NB, I - 1, NB, V));
      else
         Lemma_Row (A, NA, B, NB, I, J - 1, V);
         Lemma_Rearrange (A (I).C, B (J).C, V (A (I).W), V (B (J).W));
         Lemma_Mul_Distrib
           (X, Sum_Form (B, J - 1, V), B (J).C * V (B (J).W));
         Lemma_Add_Assoc
           (Expand_Sum (A, NA, B, NB, I - 1, NB, V),
            X * Sum_Form (B, J - 1, V),
            X * (B (J).C * V (B (J).W)));
      end if;
   end Lemma_Row;

   --  The whole expansion up to row I: the first I entries of A times B.
   procedure Lemma_Expand
     (A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      I : Form_Count; V : Values)
   with Ghost => Proof_Only, Global => null,
        Pre  => I <= NA
                and then Form_In (A, NA, V) and then Form_In (B, NB, V),
        Post => Same (Expand_Sum (A, NA, B, NB, I, NB, V),
                      Sum_Form (A, I, V) * Sum_Form (B, NB, V)),
        Subprogram_Variant => (Decreases => I)
   is
   begin
      if I = 0 then
         Lemma_Mul_Zero (Sum_Form (B, NB, V));
      else
         Lemma_Expand (A, NA, B, NB, I - 1, V);
         Lemma_Row (A, NA, B, NB, I, NB, V);
         Lemma_Distrib_Right
           (Sum_Form (A, I - 1, V), A (I).C * V (A (I).W),
            Sum_Form (B, NB, V));
      end if;
   end Lemma_Expand;

   ----------------------------------------------------------------------
   --  The regrouping of the expansion into the wire's terms.
   ----------------------------------------------------------------------

   --  The terms with their coefficients replaced by what the expansion
   --  collects there up to the pair (I, J).
   function Sum_Collected
     (T : Term_Array; N : Term_Count;
      A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      M : Pair_Map; I : Form_Count; J : Form_Count; V : Values)
      return Element
   is (if N = 0 then Zero
       else Sum_Collected (T, N - 1, A, NA, B, NB, M, I, J, V)
            + (Collected (A, NA, B, NB, M, N, I, J) * V (T (N).H0))
              * V (T (N).H1))
   with Ghost => Proof_Only, Global => null,
        Pre => J <= NB and then Wires_In (T, N, V),
        Subprogram_Variant => (Decreases => N);

   --  Nothing collected: the sum is zero.
   procedure Lemma_Collected_Zero
     (T : Term_Array; N : Term_Count;
      A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      M : Pair_Map; J : Form_Count; V : Values)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= NB and then Wires_In (T, N, V),
        Post => Same (Sum_Collected (T, N, A, NA, B, NB, M, 0, J, V), Zero),
        Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Collected_Zero (T, N - 1, A, NA, B, NB, M, J, V);
         pragma Assert (Same (Collected (A, NA, B, NB, M, N, 0, J), Zero));
         Lemma_Mul_Zero (V (T (N).H0));
         Lemma_Mul_Zero (V (T (N).H1));
         Lemma_Add_Zero (Zero);
      end if;
   end Lemma_Collected_Zero;

   --  The terms before the one the pair is mapped to do not change.
   procedure Lemma_Collected_Unchanged
     (T : Term_Array; N : Term_Count;
      A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      M : Pair_Map; I : Form_Index; J : Form_Index; V : Values)
   with Ghost => Proof_Only, Global => null,
        Pre  => I <= NA and then J <= NB and then Wires_In (T, N, V)
                and then M (I, J) > N,
        Post => Same (Sum_Collected (T, N, A, NA, B, NB, M, I, J, V),
                      Sum_Collected (T, N, A, NA, B, NB, M, I, J - 1, V)),
        Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Collected_Unchanged (T, N - 1, A, NA, B, NB, M, I, J, V);
         Lemma_Add_Zero (Collected (A, NA, B, NB, M, N, I, J - 1));
         pragma Assert (Same (Collected (A, NA, B, NB, M, N, I, J),
                              Collected (A, NA, B, NB, M, N, I, J - 1)));
      end if;
   end Lemma_Collected_Unchanged;

   --  One pair more: the sum over the terms grows by the pair's
   --  coefficient times the monomial of the term it is mapped to.
   procedure Lemma_Collected_Step
     (T : Term_Array; N : Term_Count;
      A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      M : Pair_Map; I : Form_Index; J : Form_Index; V : Values)
   with Ghost => Proof_Only, Global => null,
        Pre  => I <= NA and then J <= NB and then Wires_In (T, N, V)
                and then M (I, J) <= N,
        Post => Same (Sum_Collected (T, N, A, NA, B, NB, M, I, J, V),
                      Sum_Collected (T, N, A, NA, B, NB, M, I, J - 1, V)
                      + ((A (I).C * B (J).C) * V (T (M (I, J)).H0))
                        * V (T (M (I, J)).H1)),
        Subprogram_Variant => (Decreases => N)
   is
      D  : constant Element := A (I).C * B (J).C
        with Ghost => Proof_Only;
      --  The terms before N, the term N before the pair, and the pair's
      --  contribution.
      S  : constant Element :=
        Sum_Collected (T, N - 1, A, NA, B, NB, M, I, J - 1, V)
        with Ghost => Proof_Only;
      C0 : constant Element :=
        (Collected (A, NA, B, NB, M, N, I, J - 1) * V (T (N).H0))
        * V (T (N).H1)
        with Ghost => Proof_Only;
      P  : constant Element :=
        (D * V (T (M (I, J)).H0)) * V (T (M (I, J)).H1)
        with Ghost => Proof_Only;
   begin
      if N = M (I, J) then
         --  The term N takes the pair; the terms before it do not.
         Lemma_Collected_Unchanged (T, N - 1, A, NA, B, NB, M, I, J, V);
         pragma Assert (Same (Collected (A, NA, B, NB, M, N, I, J),
                              Collected (A, NA, B, NB, M, N, I, J - 1) + D));
         Lemma_Distrib_Term
           (Collected (A, NA, B, NB, M, N, I, J - 1), D,
            V (T (N).H0), V (T (N).H1));
         Lemma_Add_Assoc (S, C0, P);
      else
         --  The pair goes to an earlier term; the term N does not change.
         Lemma_Collected_Step (T, N - 1, A, NA, B, NB, M, I, J, V);
         Lemma_Add_Zero (Collected (A, NA, B, NB, M, N, I, J - 1));
         pragma Assert (Same (Collected (A, NA, B, NB, M, N, I, J),
                              Collected (A, NA, B, NB, M, N, I, J - 1)));
         --  (S + P) + C0 = S + (P + C0) = S + (C0 + P) = (S + C0) + P
         Lemma_Add_Assoc (S, P, C0);
         Lemma_Add_Comm (P, C0);
         Lemma_Add_Assoc (S, C0, P);
      end if;
   end Lemma_Collected_Step;

   --  Column 0 of row I is the end of row I - 1, for Sum_Collected as
   --  for Collected.
   procedure Lemma_Same_Rows
     (T : Term_Array; N : Term_Count;
      A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      M : Pair_Map; I : Form_Index; V : Values)
   with Ghost => Proof_Only, Global => null,
        Pre  => I <= NA and then Wires_In (T, N, V),
        Post => Same (Sum_Collected (T, N, A, NA, B, NB, M, I, 0, V),
                      Sum_Collected (T, N, A, NA, B, NB, M, I - 1, NB, V)),
        Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Same_Rows (T, N - 1, A, NA, B, NB, M, I, V);
      end if;
   end Lemma_Same_Rows;

   --  The pairs up to (I, J), collected into the terms, sum to the
   --  expansion up to (I, J).
   procedure Lemma_Regroup
     (T : Term_Array; NT : Term_Count;
      A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      M : Pair_Map; I : Form_Count; J : Form_Count; V : Values)
   with Ghost => Proof_Only, Global => null,
        Pre  => I <= NA and then J <= NB and then Wires_In (T, NT, V)
                and then Form_In (A, NA, V) and then Form_In (B, NB, V)
                and then Check_Product (T, NT, A, NA, B, NB, M),
        Post => Same (Sum_Collected (T, NT, A, NA, B, NB, M, I, J, V),
                      Expand_Sum (A, NA, B, NB, I, J, V)),
        Subprogram_Variant => (Decreases => I, Decreases => J)
   is
   begin
      if I = 0 then
         Lemma_Collected_Zero (T, NT, A, NA, B, NB, M, J, V);
      elsif J = 0 then
         Lemma_Regroup (T, NT, A, NA, B, NB, M, I - 1, NB, V);
         Lemma_Same_Rows (T, NT, A, NA, B, NB, M, I, V);
      else
         Lemma_Regroup (T, NT, A, NA, B, NB, M, I, J - 1, V);
         --  The certificate maps the pair to a term of its monomial.
         pragma Assert
           (M (I, J) <= NT
            and then Same_Monomial (A (I).W, B (J).W, T (M (I, J))));
         Lemma_Collected_Step (T, NT, A, NA, B, NB, M, I, J, V);
         --  In one order or the other, the monomial is the pair's.
         Lemma_Swap (A (I).C * B (J).C, V (A (I).W), V (B (J).W));
      end if;
   end Lemma_Regroup;

   --  At the end, what is collected is each term's coefficient.
   procedure Lemma_Final
     (T : Term_Array; N : Term_Count; NT : Term_Count;
      A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      M : Pair_Map; V : Values)
   with Ghost => Proof_Only, Global => null,
        Pre  => N <= NT and then Wires_In (T, NT, V)
                and then Check_Product (T, NT, A, NA, B, NB, M),
        Post => Same (Sum_Collected (T, N, A, NA, B, NB, M, NA, NB, V),
                      Sum_Terms (T, N, V)),
        Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Final (T, N - 1, NT, A, NA, B, NB, M, V);
         --  The check compares with the predefined "=": to Same.
         Field_GF2_128.Laws.Lemma_Same
           (T (N).K, Collected (A, NA, B, NB, M, N, NA, NB));
      end if;
   end Lemma_Final;

   procedure Lemma_Product
     (T : Term_Array; NT : Term_Count;
      A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      M : Pair_Map; V : Values)
   is
   begin
      Lemma_Regroup (T, NT, A, NA, B, NB, M, NA, NB, V);
      Lemma_Final (T, NT, NT, A, NA, B, NB, M, V);
      Lemma_Expand (A, NA, B, NB, NA, V);
   end Lemma_Product;

end Local_Check;
