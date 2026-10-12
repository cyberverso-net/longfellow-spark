pragma SPARK_Mode (On);

package body Sumcheck_Expression is

   ----------------------------------------------------------------------
   --  Find
   ----------------------------------------------------------------------

   function Find (E : Expression; V : Natural) return Natural is
   begin
      for I in 1 .. E.Length loop
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 => E.Terms (J).V /= V);
         if E.Terms (I).V = V then
            return I;
         end if;
      end loop;
      return 0;
   end Find;

   ----------------------------------------------------------------------
   --  Lemmas on Find: two expressions with the same variables at the
   --  same positions have the same Find; inserting a variable at Pos
   --  shifts the positions above it by one.
   ----------------------------------------------------------------------

   procedure Lemma_Find_Equiv (E, F : Expression) with
     Ghost, Global => null,
     Pre  => E.Length = F.Length
       and then (for all I in 1 .. E.Length => E.Terms (I).V = F.Terms (I).V),
     Post => (for all W in Natural => Find (E, W) = Find (F, W));

   procedure Lemma_Find_Equiv (E, F : Expression) is
   begin
      null;
   end Lemma_Find_Equiv;

   procedure Lemma_Find_Insert (E, R : Expression; Pos, V : Natural) with
     Ghost, Global => null,
     Pre  => Find (E, V) = 0
       and then Pos in 1 .. E.Length + 1
       and then R.Length = E.Length + 1
       and then R.Terms (Pos).V = V
       and then (for all J in 1 .. Pos - 1 => R.Terms (J).V = E.Terms (J).V)
       and then (for all J in Pos + 1 .. R.Length =>
                   R.Terms (J).V = E.Terms (J - 1).V),
     Post => Find (R, V) = Pos
       and then (for all W in Natural =>
                   (if W /= V then
                      Find (R, W)
                      = (if Find (E, W) = 0 then 0
                         elsif Find (E, W) < Pos then Find (E, W)
                         else Find (E, W) + 1)));

   procedure Lemma_Find_Insert (E, R : Expression; Pos, V : Natural) is
   begin
      null;
   end Lemma_Find_Insert;

   ----------------------------------------------------------------------
   --  Constructors
   ----------------------------------------------------------------------

   function From_Constant (K : Element; Capacity : Capacity_Type)
                           return Expression
   is
   begin
      return (Capacity => Capacity, Length => 0, Known => K,
              Terms => [others => (V => 0, C => Zero)]);
   end From_Constant;

   function Var (I : Natural; Capacity : Capacity_Type) return Expression is
      T : Pair_Array (1 .. Capacity) := [others => (V => 0, C => Zero)];
   begin
      T (1) := (V => I, C => One);
      return (Capacity => Capacity, Length => 1, Known => Zero, Terms => T);
   end Var;

   ----------------------------------------------------------------------
   --  Add_Term and Sub_Term share one body.
   ----------------------------------------------------------------------

   function Combine (E : Expression; V : Natural; K : Element;
                     Subtract : Boolean) return Expression
   with
     Global => null,
     Pre  => Has (E, V) or else E.Length < E.Capacity,
     Post => Combine'Result.Capacity = E.Capacity
       and then Combine'Result.Length
                = (if Has (E, V) then E.Length else E.Length + 1)
       and then Same (Combine'Result.Known, E.Known)
       and then (for all W in Natural =>
                   Has (Combine'Result, W) = (Has (E, W) or else W = V))
       and then (for all W in Natural =>
                   (if W /= V then
                      Same (Coef (Combine'Result, W), Coef (E, W))))
       and then (if Subtract then
                   Same (Coef (Combine'Result, V), Coef (E, V) - K)
                 else
                   Same (Coef (Combine'Result, V), Coef (E, V) + K));

   function Combine (E : Expression; V : Natural; K : Element;
                     Subtract : Boolean) return Expression
   is
      P   : constant Natural := Find (E, V);
      T   : Pair_Array (1 .. E.Capacity) := E.Terms;
      Len : Natural;
   begin
      if P /= 0 then
         T (P).C :=
           (if Subtract then E.Terms (P).C - K else E.Terms (P).C + K);
         Len := E.Length;
         pragma Assert
           (for all J in 1 .. E.Length => T (J).V = E.Terms (J).V);
         pragma Assert
           (for all J in 1 .. E.Length =>
              (if J /= P then Same (T (J).C, E.Terms (J).C)));
         declare
            R : constant Expression :=
              (Capacity => E.Capacity, Length => Len, Known => E.Known,
               Terms => T);
         begin
            Lemma_Find_Equiv (E, R);
            return R;
         end;
      else
         declare
            Pos : Natural := 1;
         begin
            --  Insertion point: the first pair whose variable exceeds V.
            while Pos <= E.Length and then E.Terms (Pos).V < V loop
               pragma Loop_Invariant (Pos in 1 .. E.Length);
               pragma Loop_Invariant
                 (for all I in 1 .. Pos - 1 => E.Terms (I).V < V);
               pragma Loop_Variant (Increases => Pos);
               Pos := Pos + 1;
            end loop;
            pragma Assert (for all I in 1 .. Pos - 1 => E.Terms (I).V < V);
            pragma Assert (for all I in Pos .. E.Length => E.Terms (I).V > V);
            --  Shift the tail up by one, highest first.
            for I in reverse Pos .. E.Length loop
               T (I + 1) := E.Terms (I);
               pragma Loop_Invariant
                 (for all J in I .. E.Length =>
                    T (J + 1).V = E.Terms (J).V
                    and then Same (T (J + 1).C, E.Terms (J).C));
               pragma Loop_Invariant
                 (for all J in 1 .. I - 1 =>
                    T (J).V = E.Terms (J).V
                    and then Same (T (J).C, E.Terms (J).C));
            end loop;
            T (Pos) := (V => V,
                        C => (if Subtract then Zero - K else Zero + K));
            Len := E.Length + 1;
            pragma Assert
              (for all J in 1 .. Pos - 1 =>
                 T (J).V = E.Terms (J).V
                 and then Same (T (J).C, E.Terms (J).C));
            pragma Assert
              (for all J in Pos + 1 .. E.Length + 1 =>
                 T (J).V = E.Terms (J - 1).V
                 and then Same (T (J).C, E.Terms (J - 1).C));
            pragma Assert (for all J in 1 .. Pos - 1 => T (J).V < V);
            pragma Assert
              (for all J in Pos + 1 .. E.Length + 1 => T (J).V > V);
            pragma Assert (Sorted (T, Len));
            declare
               R : constant Expression :=
                 (Capacity => E.Capacity, Length => Len, Known => E.Known,
                  Terms => T);
            begin
               Lemma_Find_Insert (E, R, Pos, V);
               return R;
            end;
         end;
      end if;
   end Combine;

   function Add_Term (E : Expression; V : Natural; K : Element)
                      return Expression
   is
   begin
      return Combine (E, V, K, Subtract => False);
   end Add_Term;

   function Sub_Term (E : Expression; V : Natural; K : Element)
                      return Expression
   is
   begin
      return Combine (E, V, K, Subtract => True);
   end Sub_Term;

   ----------------------------------------------------------------------
   --  Add and Sub: fold the pairs of F into E.
   ----------------------------------------------------------------------

   function Fold (E, F : Expression; Subtract : Boolean) return Expression
   with
     Global => null,
     Pre  => E.Capacity = F.Capacity
       and then E.Length + F.Length <= E.Capacity,
     Post => Fold'Result.Capacity = E.Capacity
       and then Fold'Result.Length = E.Length + New_Count (E, F, F.Length)
       and then Same (Fold'Result.Known, E.Known)
       and then (for all W in Natural =>
                   Has (Fold'Result, W) = (Has (E, W) or else Has (F, W)))
       and then (for all W in Natural =>
                   (if Has (F, W) then
                      (if Subtract then
                         Same (Coef (Fold'Result, W),
                               Coef (E, W) - Coef (F, W))
                       else
                         Same (Coef (Fold'Result, W),
                               Coef (E, W) + Coef (F, W)))
                    else
                      Same (Coef (Fold'Result, W), Coef (E, W))));

   function Fold (E, F : Expression; Subtract : Boolean) return Expression
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", New_Count);
      R : Expression := E;
   begin
      for I in 1 .. F.Length loop
         pragma Loop_Invariant (R.Capacity = E.Capacity);
         pragma Loop_Invariant (R.Length = E.Length + New_Count (E, F, I - 1));
         pragma Loop_Invariant (Same (R.Known, E.Known));
         pragma Loop_Invariant
           (for all W in Natural =>
              Has (R, W) = (Has (E, W) or else Find (F, W) in 1 .. I - 1));
         pragma Loop_Invariant
           (for all W in Natural =>
              (if Find (F, W) in 1 .. I - 1 then
                 (if Subtract then
                    Same (Coef (R, W), Coef (E, W) - Coef (F, W))
                  else
                    Same (Coef (R, W), Coef (E, W) + Coef (F, W)))
               else
                 Same (Coef (R, W), Coef (E, W))));
         pragma Assert (Find (F, F.Terms (I).V) = I);
         R := Combine (R, F.Terms (I).V, F.Terms (I).C, Subtract);
      end loop;
      return R;
   end Fold;

   function Add (E, F : Expression) return Expression is
      R : Expression := Fold (E, F, Subtract => False);
   begin
      R.Known := E.Known + F.Known;
      return R;
   end Add;

   function Sub (E, F : Expression) return Expression is
      R : Expression := Fold (E, F, Subtract => True);
   begin
      R.Known := E.Known - F.Known;
      return R;
   end Sub;

   ----------------------------------------------------------------------
   --  Scale, Add_Constant, Sub_Constant
   ----------------------------------------------------------------------

   function Scale (E : Expression; S : Element) return Expression is
      T : Pair_Array (1 .. E.Capacity) := E.Terms;
   begin
      for I in 1 .. E.Length loop
         T (I).C := E.Terms (I).C * S;
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              T (J).V = E.Terms (J).V
              and then Same (T (J).C, E.Terms (J).C * S));
         pragma Loop_Invariant
           (for all J in I + 1 .. E.Capacity =>
              T (J).V = E.Terms (J).V
              and then Same (T (J).C, E.Terms (J).C));
      end loop;
      declare
         R : constant Expression :=
           (Capacity => E.Capacity, Length => E.Length,
            Known => E.Known * S, Terms => T);
      begin
         Lemma_Find_Equiv (E, R);
         return R;
      end;
   end Scale;

   function Add_Constant (E : Expression; K : Element) return Expression is
      R : Expression := E;
   begin
      R.Known := E.Known + K;
      Lemma_Find_Equiv (E, R);
      return R;
   end Add_Constant;

   function Sub_Constant (E : Expression; K : Element) return Expression is
      R : Expression := E;
   begin
      R.Known := E.Known - K;
      Lemma_Find_Equiv (E, R);
      return R;
   end Sub_Constant;

   ----------------------------------------------------------------------
   --  Lemmas
   ----------------------------------------------------------------------

   procedure Lemma_NC_Shared_Rec (E, F : Expression; V : Natural;
                                  N : Natural)
   with
     Ghost, Global => null,
     Pre  => Has (E, V) and then Has (F, V) and then N <= F.Length,
     Post => New_Count (E, F, N)
             <= N - (if Find (F, V) in 1 .. N then 1 else 0),
     Subprogram_Variant => (Decreases => N);

   procedure Lemma_NC_Shared_Rec (E, F : Expression; V : Natural;
                                  N : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", New_Count);
   begin
      if N > 0 then
         Lemma_NC_Shared_Rec (E, F, V, N - 1);
      end if;
   end Lemma_NC_Shared_Rec;

   procedure Lemma_New_Count_Shared (E, F : Expression; V : Natural) is
   begin
      Lemma_NC_Shared_Rec (E, F, V, F.Length);
   end Lemma_New_Count_Shared;

   procedure Lemma_NC_Disjoint_Rec (E, F : Expression; N : Natural) with
     Ghost, Global => null,
     Pre  => N <= F.Length
       and then (for all I in 1 .. F.Length => not Has (E, F.Terms (I).V)),
     Post => New_Count (E, F, N) = N,
     Subprogram_Variant => (Decreases => N);

   procedure Lemma_NC_Disjoint_Rec (E, F : Expression; N : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", New_Count);
   begin
      if N > 0 then
         Lemma_NC_Disjoint_Rec (E, F, N - 1);
      end if;
   end Lemma_NC_Disjoint_Rec;

   procedure Lemma_New_Count_Disjoint (E, F : Expression) is
   begin
      Lemma_NC_Disjoint_Rec (E, F, F.Length);
   end Lemma_New_Count_Disjoint;

end Sumcheck_Expression;
