--  Sumcheck_Expression: sparse affine expressions over the combined
--  witness, k + SUM_i a[i] * Var (i), for the symbolic sumcheck verifier
--  (draft-03 Section 6.7; zk/expression.rs of the reference). Generic
--  over an instance of Sumcheck_Algebra, from which it takes the field
--  (ADR 0024) and the logical equality Same (ADR 0023).
--
--  Documentation: docs/guide/03-sumcheck.md. Decision: ADR 0026.
--
--  Representation: a discriminated record with a Capacity, a Length, a
--  sorted array of (variable, coefficient) pairs with no duplicate
--  variable (type predicate), and a Known constant term. Zero
--  coefficients are kept (ADR 0026): a stored coefficient is what the
--  field operations produced, never dropped by a test on its value.
--
--  Proof status (per instance). Every operation is Gold against the
--  coefficient model: Find gives the position of a variable, Has and
--  Coef (ghost) read the model, and each postcondition states which
--  variables are present in the result (every variable of the operands,
--  and nothing else) and what their coefficients are, with Same, in the
--  association the body computes (ADR 0023). The quantifiers range over
--  the positions of the stored pairs, never over all variables, so that
--  the contracts execute in the assertion-enabled test build in time
--  quadratic in the number of terms. The convention "absent means Zero"
--  is made explicit by case splits: where the reference would read
--  Zero + K the body computes Zero + K. Lengths are exact: Add and Sub
--  state the number of variables of F that are new to E (New_Count),
--  which is what the capacity bound of the symbolic core rests on.
--
--  Cost: Find is a linear scan and insertion shifts the tail; the
--  expressions of the verifier core hold at most a few hundred terms
--  per layer, and the input constraint ninput - npublic terms. A dense
--  path for large circuits is a phase B concern.

pragma SPARK_Mode (On);

with Sumcheck_Algebra;

generic
   with package SA is new Sumcheck_Algebra (<>);
package Sumcheck_Expression is

   use SA;

   subtype Element is SA.Element;

   --  Enough for ninput - npublic + 2 at Max_Wires inputs.
   Max_Capacity : constant := Max_Wires + 8;
   subtype Capacity_Type is Natural range 0 .. Max_Capacity;

   type Pair is record
      V : Natural := 0;
      C : Element := Zero;
   end record;

   type Pair_Array is array (Positive range <>) of Pair;

   --  Strictly increasing variables over the first Length pairs: no
   --  duplicate, and a variable has at most one position.
   function Sorted (T : Pair_Array; Length : Natural) return Boolean is
     (Length <= T'Length
      and then (for all I in 1 .. Length =>
                  (for all J in 1 .. Length =>
                     (if I < J then T (I).V < T (J).V))))
   with Global => null, Pre => T'First = 1;

   type Expression (Capacity : Capacity_Type) is record
      Length : Natural := 0;
      Known  : Element := Zero;
      Terms  : Pair_Array (1 .. Capacity);
   end record
   with Dynamic_Predicate =>
     Expression.Length <= Expression.Capacity
     and then Sorted (Expression.Terms, Expression.Length);

   --  Position of V among the stored pairs, 0 if absent.
   function Find (E : Expression; V : Natural) return Natural with
     Global => null,
     Post => (if Find'Result = 0 then
                (for all I in 1 .. E.Length => E.Terms (I).V /= V)
              else Find'Result in 1 .. E.Length
                and then (for all I in 1 .. E.Length =>
                            (E.Terms (I).V = V) = (I = Find'Result)));

   --  The coefficient model.
   function Has (E : Expression; V : Natural) return Boolean is
     (Find (E, V) /= 0)
   with Ghost, Global => null;

   function Coef (E : Expression; V : Natural) return Element is
     (if Find (E, V) = 0 then Zero else E.Terms (Find (E, V)).C)
   with Ghost, Global => null;

   --  Number of variables among the first N pairs of F that are absent
   --  from E.
   function New_Count (E, F : Expression; N : Natural) return Natural is
     (if N = 0 then 0
      else New_Count (E, F, N - 1)
             + (if Has (E, F.Terms (N).V) then 0 else 1))
   with Ghost, Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => N <= F.Length,
        Post => New_Count'Result <= N,
        Subprogram_Variant => (Decreases => N);

   -------------------------------------------------------------------
   --  Constructors.
   -------------------------------------------------------------------

   function From_Constant (K : Element; Capacity : Capacity_Type)
                           return Expression
   with
     Global => null,
     Post => From_Constant'Result.Capacity = Capacity
       and then From_Constant'Result.Length = 0
       and then Same (From_Constant'Result.Known, K);

   --  One * Var (I).
   function Var (I : Natural; Capacity : Capacity_Type) return Expression
   with
     Global => null,
     Pre  => Capacity >= 1,
     Post => Var'Result.Capacity = Capacity
       and then Var'Result.Length = 1
       and then Same (Var'Result.Known, Zero)
       and then Var'Result.Terms (1).V = I
       and then Same (Var'Result.Terms (1).C, One);

   -------------------------------------------------------------------
   --  Operations. Every result has the capacity of its first operand.
   --  "Every variable of E is in the result and every variable of the
   --  result comes from the operands" is stated over the positions.
   -------------------------------------------------------------------

   --  E + K * Var (V); the stored coefficient of V becomes
   --  Coef (E, V) + K, computed as such (Zero + K when V was absent).
   function Add_Term (E : Expression; V : Natural; K : Element)
                      return Expression
   with
     Global => null,
     Pre  => Has (E, V) or else E.Length < E.Capacity,
     Post => Add_Term'Result.Capacity = E.Capacity
       and then Add_Term'Result.Length
                = (if Has (E, V) then E.Length else E.Length + 1)
       and then Same (Add_Term'Result.Known, E.Known)
       and then Has (Add_Term'Result, V)
       and then Same (Coef (Add_Term'Result, V), Coef (E, V) + K)
       and then (for all I in 1 .. E.Length =>
                   Has (Add_Term'Result, E.Terms (I).V))
       and then (for all I in 1 .. E.Length =>
                   (if E.Terms (I).V /= V then
                      Same (Coef (Add_Term'Result, E.Terms (I).V),
                            E.Terms (I).C)))
       and then (for all I in 1 .. Add_Term'Result.Length =>
                   Add_Term'Result.Terms (I).V = V
                   or else Has (E, Add_Term'Result.Terms (I).V));

   --  E - K * Var (V), likewise with Coef (E, V) - K.
   function Sub_Term (E : Expression; V : Natural; K : Element)
                      return Expression
   with
     Global => null,
     Pre  => Has (E, V) or else E.Length < E.Capacity,
     Post => Sub_Term'Result.Capacity = E.Capacity
       and then Sub_Term'Result.Length
                = (if Has (E, V) then E.Length else E.Length + 1)
       and then Same (Sub_Term'Result.Known, E.Known)
       and then Has (Sub_Term'Result, V)
       and then Same (Coef (Sub_Term'Result, V), Coef (E, V) - K)
       and then (for all I in 1 .. E.Length =>
                   Has (Sub_Term'Result, E.Terms (I).V))
       and then (for all I in 1 .. E.Length =>
                   (if E.Terms (I).V /= V then
                      Same (Coef (Sub_Term'Result, E.Terms (I).V),
                            E.Terms (I).C)))
       and then (for all I in 1 .. Sub_Term'Result.Length =>
                   Sub_Term'Result.Terms (I).V = V
                   or else Has (E, Sub_Term'Result.Terms (I).V));

   --  E + F: a variable of F gets Coef (E, W) + Coef (F, W), a variable
   --  only in E keeps its coefficient.
   function Add (E, F : Expression) return Expression with
     Global => null,
     Pre  => E.Capacity = F.Capacity
       and then E.Length + F.Length <= E.Capacity,
     Post => Add'Result.Capacity = E.Capacity
       and then Add'Result.Length = E.Length + New_Count (E, F, F.Length)
       and then Same (Add'Result.Known, E.Known + F.Known)
       and then (for all I in 1 .. E.Length => Has (Add'Result, E.Terms (I).V))
       and then (for all I in 1 .. F.Length => Has (Add'Result, F.Terms (I).V))
       and then (for all I in 1 .. Add'Result.Length =>
                   Has (E, Add'Result.Terms (I).V)
                   or else Has (F, Add'Result.Terms (I).V))
       and then (for all I in 1 .. F.Length =>
                   Same (Coef (Add'Result, F.Terms (I).V),
                         Coef (E, F.Terms (I).V) + F.Terms (I).C))
       and then (for all I in 1 .. E.Length =>
                   (if not Has (F, E.Terms (I).V) then
                      Same (Coef (Add'Result, E.Terms (I).V), E.Terms (I).C)));

   --  E - F, likewise with Coef (E, W) - Coef (F, W).
   function Sub (E, F : Expression) return Expression with
     Global => null,
     Pre  => E.Capacity = F.Capacity
       and then E.Length + F.Length <= E.Capacity,
     Post => Sub'Result.Capacity = E.Capacity
       and then Sub'Result.Length = E.Length + New_Count (E, F, F.Length)
       and then Same (Sub'Result.Known, E.Known - F.Known)
       and then (for all I in 1 .. E.Length => Has (Sub'Result, E.Terms (I).V))
       and then (for all I in 1 .. F.Length => Has (Sub'Result, F.Terms (I).V))
       and then (for all I in 1 .. Sub'Result.Length =>
                   Has (E, Sub'Result.Terms (I).V)
                   or else Has (F, Sub'Result.Terms (I).V))
       and then (for all I in 1 .. F.Length =>
                   Same (Coef (Sub'Result, F.Terms (I).V),
                         Coef (E, F.Terms (I).V) - F.Terms (I).C))
       and then (for all I in 1 .. E.Length =>
                   (if not Has (F, E.Terms (I).V) then
                      Same (Coef (Sub'Result, E.Terms (I).V), E.Terms (I).C)));

   --  E * S: the same variables at the same positions, every
   --  coefficient and Known multiplied by S.
   function Scale (E : Expression; S : Element) return Expression with
     Global => null,
     Post => Scale'Result.Capacity = E.Capacity
       and then Scale'Result.Length = E.Length
       and then Same (Scale'Result.Known, E.Known * S)
       and then (for all I in 1 .. E.Length =>
                   Scale'Result.Terms (I).V = E.Terms (I).V
                   and then Same (Scale'Result.Terms (I).C,
                                  E.Terms (I).C * S));

   function Add_Constant (E : Expression; K : Element) return Expression
   with
     Global => null,
     Post => Add_Constant'Result.Capacity = E.Capacity
       and then Add_Constant'Result.Length = E.Length
       and then Same (Add_Constant'Result.Known, E.Known + K)
       and then (for all I in 1 .. E.Length =>
                   Add_Constant'Result.Terms (I).V = E.Terms (I).V
                   and then Same (Add_Constant'Result.Terms (I).C,
                                  E.Terms (I).C));

   function Sub_Constant (E : Expression; K : Element) return Expression
   with
     Global => null,
     Post => Sub_Constant'Result.Capacity = E.Capacity
       and then Sub_Constant'Result.Length = E.Length
       and then Same (Sub_Constant'Result.Known, E.Known - K)
       and then (for all I in 1 .. E.Length =>
                   Sub_Constant'Result.Terms (I).V = E.Terms (I).V
                   and then Same (Sub_Constant'Result.Terms (I).C,
                                  E.Terms (I).C));

   -------------------------------------------------------------------
   --  Variables below a bound: the claim expressions of the verifier
   --  only ever name pad variables already assigned (ADR 0026).
   -------------------------------------------------------------------

   function Below (E : Expression; Bound : Natural) return Boolean is
     (for all I in 1 .. E.Length => E.Terms (I).V < Bound)
   with Ghost, Global => null;

   --  A present variable of an expression below Bound is below Bound.
   procedure Lemma_Has_Below (E : Expression; W, Bound : Natural) with
     Ghost, Global => null,
     Pre  => Has (E, W) and then Below (E, Bound),
     Post => W < Bound;

   --  R draws its variables from E and F: it is below their bound.
   procedure Lemma_Below_Union (E, F, R : Expression; Bound : Natural) with
     Ghost, Global => null,
     Pre  => Below (E, Bound) and then Below (F, Bound)
       and then (for all I in 1 .. R.Length =>
                   Has (E, R.Terms (I).V) or else Has (F, R.Terms (I).V)),
     Post => Below (R, Bound);

   --  R draws its variables from E and V: likewise.
   procedure Lemma_Below_Insert (E, R : Expression; V, Bound : Natural) with
     Ghost, Global => null,
     Pre  => Below (E, Bound) and then V < Bound
       and then (for all I in 1 .. R.Length =>
                   R.Terms (I).V = V or else Has (E, R.Terms (I).V)),
     Post => Below (R, Bound);

   -------------------------------------------------------------------
   --  Lemmas on New_Count for the capacity accounting of the core.
   -------------------------------------------------------------------

   --  A variable present in both E and F is not counted.
   procedure Lemma_New_Count_Shared (E, F : Expression; V : Natural) with
     Ghost, Global => null,
     Pre  => Has (E, V) and then Has (F, V),
     Post => New_Count (E, F, F.Length) <= F.Length - 1;

   --  When no variable of F is in E, all of them are counted.
   procedure Lemma_New_Count_Disjoint (E, F : Expression) with
     Ghost, Global => null,
     Pre  => (for all I in 1 .. F.Length => not Has (E, F.Terms (I).V)),
     Post => New_Count (E, F, F.Length) = F.Length;

end Sumcheck_Expression;
