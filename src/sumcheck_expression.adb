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
   --  Lemma on Find: inserting a variable at Pos shifts the positions
   --  above it by one and leaves the other variables where they were.
   ----------------------------------------------------------------------

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
       and then (for all J in 1 .. E.Length =>
                   Find (R, E.Terms (J).V) = (if J < Pos then J else J + 1))
       and then (for all J in 1 .. R.Length =>
                   R.Terms (J).V = V or else Has (E, R.Terms (J).V));

   procedure Lemma_Find_Insert (E, R : Expression; Pos, V : Natural) is
   begin
      null;
   end Lemma_Find_Insert;

   --  Two expressions with the same variables at the same positions:
   --  Find agrees on every variable of E.
   procedure Lemma_Find_Equiv (E, F : Expression) with
     Ghost, Global => null,
     Pre  => E.Length = F.Length
       and then (for all I in 1 .. E.Length => E.Terms (I).V = F.Terms (I).V),
     Post => (for all I in 1 .. E.Length => Find (F, E.Terms (I).V) = I)
       and then (for all I in 1 .. E.Length => Find (E, E.Terms (I).V) = I);

   procedure Lemma_Find_Equiv (E, F : Expression) is
   begin
      null;
   end Lemma_Find_Equiv;

   --  Combine leaves the coefficient of every other variable of E where
   --  it was: read through Find for one variable W.
   procedure Lemma_Coef_Kept (E, R : Expression; V, W : Natural) with
     Ghost, Global => null,
     Pre  => Has (E, W) and then W /= V
       and then (for all I in 1 .. E.Length =>
                   (if E.Terms (I).V /= V then
                      Same (Coef (R, E.Terms (I).V), E.Terms (I).C))),
     Post => Same (Coef (R, W), Coef (E, W));

   procedure Lemma_Coef_Kept (E, R : Expression; V, W : Natural) is
   begin
      pragma Assert (E.Terms (Find (E, W)).V = W);
   end Lemma_Coef_Kept;

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
       and then Has (Combine'Result, V)
       and then (if Subtract then
                   Same (Coef (Combine'Result, V), Coef (E, V) - K)
                 else
                   Same (Coef (Combine'Result, V), Coef (E, V) + K))
       and then (for all I in 1 .. E.Length =>
                   Has (Combine'Result, E.Terms (I).V))
       and then (for all I in 1 .. E.Length =>
                   (if E.Terms (I).V /= V then
                      Same (Coef (Combine'Result, E.Terms (I).V),
                            E.Terms (I).C)))
       and then (for all I in 1 .. Combine'Result.Length =>
                   Combine'Result.Terms (I).V = V
                   or else Has (E, Combine'Result.Terms (I).V));

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
       and then (for all I in 1 .. E.Length =>
                   Has (Fold'Result, E.Terms (I).V))
       and then (for all I in 1 .. F.Length =>
                   Has (Fold'Result, F.Terms (I).V))
       and then (for all I in 1 .. Fold'Result.Length =>
                   Has (E, Fold'Result.Terms (I).V)
                   or else Has (F, Fold'Result.Terms (I).V))
       and then (for all I in 1 .. F.Length =>
                   (if Subtract then
                      Same (Coef (Fold'Result, F.Terms (I).V),
                            Coef (E, F.Terms (I).V) - F.Terms (I).C)
                    else
                      Same (Coef (Fold'Result, F.Terms (I).V),
                            Coef (E, F.Terms (I).V) + F.Terms (I).C)))
       and then (for all I in 1 .. E.Length =>
                   (if not Has (F, E.Terms (I).V) then
                      Same (Coef (Fold'Result, E.Terms (I).V),
                            E.Terms (I).C)));

   function Fold (E, F : Expression; Subtract : Boolean) return Expression
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", New_Count);
      R : Expression := E;
   begin
      Lemma_Find_Equiv (E, E);
      Lemma_Find_Equiv (F, F);
      for I in 1 .. F.Length loop
         pragma Loop_Invariant (R.Capacity = E.Capacity);
         pragma Loop_Invariant (R.Length = E.Length + New_Count (E, F, I - 1));
         pragma Loop_Invariant (Same (R.Known, E.Known));
         pragma Loop_Invariant
           (for all J in 1 .. E.Length => Has (R, E.Terms (J).V));
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 => Has (R, F.Terms (J).V));
         pragma Loop_Invariant
           (for all J in 1 .. R.Length =>
              Has (E, R.Terms (J).V)
              or else Find (F, R.Terms (J).V) in 1 .. I - 1);
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 =>
              (if Subtract then
                 Same (Coef (R, F.Terms (J).V),
                       Coef (E, F.Terms (J).V) - F.Terms (J).C)
               else
                 Same (Coef (R, F.Terms (J).V),
                       Coef (E, F.Terms (J).V) + F.Terms (J).C)));
         pragma Loop_Invariant
           (for all J in 1 .. E.Length =>
              (if Find (F, E.Terms (J).V) not in 1 .. I - 1 then
                 Same (Coef (R, E.Terms (J).V), E.Terms (J).C)));
         pragma Assert (Find (F, F.Terms (I).V) = I);
         pragma Assert
           (if Has (R, F.Terms (I).V) then
              R.Terms (Find (R, F.Terms (I).V)).V = F.Terms (I).V);
         pragma Assert
           (if Has (R, F.Terms (I).V) then Has (E, F.Terms (I).V));
         pragma Assert
           (if Has (E, F.Terms (I).V) then
              E.Terms (Find (E, F.Terms (I).V)).V = F.Terms (I).V);
         pragma Assert
           (if Has (E, F.Terms (I).V) then Has (R, F.Terms (I).V));
         declare
            Prev : constant Expression := R with Ghost;
         begin
            R := Combine (R, F.Terms (I).V, F.Terms (I).C, Subtract);
            --  The coefficients of the variables of F already folded, and
            --  of the variables of E outside F, are untouched.
            for J in 1 .. I - 1 loop
               pragma Loop_Invariant
                 (for all J2 in 1 .. J - 1 =>
                    Same (Coef (R, F.Terms (J2).V),
                          Coef (Prev, F.Terms (J2).V)));
               Lemma_Coef_Kept (Prev, R, F.Terms (I).V, F.Terms (J).V);
            end loop;
            for J in 1 .. E.Length loop
               pragma Loop_Invariant
                 (for all J2 in 1 .. J - 1 =>
                    (if E.Terms (J2).V /= F.Terms (I).V then
                       Same (Coef (R, E.Terms (J2).V),
                             Coef (Prev, E.Terms (J2).V))));
               if E.Terms (J).V /= F.Terms (I).V then
                  Lemma_Coef_Kept (Prev, R, F.Terms (I).V, E.Terms (J).V);
               end if;
            end loop;
            --  Every variable of the new R is F.Terms (I).V or a variable
            --  of the previous R, hence of E or of F at a position below I.
            pragma Assert
              (for all J in 1 .. R.Length =>
                 R.Terms (J).V = F.Terms (I).V
                 or else Has (Prev, R.Terms (J).V));
            pragma Assert
              (for all J in 1 .. R.Length =>
                 (if Has (Prev, R.Terms (J).V) then
                    Has (E, R.Terms (J).V)
                    or else Find (F, R.Terms (J).V) in 1 .. I - 1));
         end;
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
      return (Capacity => E.Capacity, Length => E.Length,
              Known => E.Known * S, Terms => T);
   end Scale;

   function Add_Constant (E : Expression; K : Element) return Expression is
      R : Expression := E;
   begin
      R.Known := E.Known + K;
      return R;
   end Add_Constant;

   function Sub_Constant (E : Expression; K : Element) return Expression is
      R : Expression := E;
   begin
      R.Known := E.Known - K;
      return R;
   end Sub_Constant;

   ----------------------------------------------------------------------
   --  Lemmas on Below
   ----------------------------------------------------------------------

   procedure Lemma_Has_Below (E : Expression; W, Bound : Natural) is
   begin
      pragma Assert (E.Terms (Find (E, W)).V = W);
   end Lemma_Has_Below;

   procedure Lemma_Below_Union (E, F, R : Expression; Bound : Natural) is
   begin
      for I in 1 .. R.Length loop
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 => R.Terms (J).V < Bound);
         if Has (E, R.Terms (I).V) then
            Lemma_Has_Below (E, R.Terms (I).V, Bound);
         else
            Lemma_Has_Below (F, R.Terms (I).V, Bound);
         end if;
      end loop;
   end Lemma_Below_Union;

   procedure Lemma_Below_Insert (E, R : Expression; V, Bound : Natural) is
   begin
      for I in 1 .. R.Length loop
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 => R.Terms (J).V < Bound);
         if R.Terms (I).V /= V then
            Lemma_Has_Below (E, R.Terms (I).V, Bound);
         end if;
      end loop;
   end Lemma_Below_Insert;

   ----------------------------------------------------------------------
   --  Lemmas on New_Count
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
