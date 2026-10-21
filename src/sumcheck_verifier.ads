--  Sumcheck_Verifier: the symbolic sumcheck verifier core of draft-03
--  Section 6.7 (zk/symbolic_sumcheck_verifier.rs of the reference),
--  challenges as input (ADR 0022). Generic over an instance of
--  Sumcheck_Algebra and the matching instance of Sumcheck_Expression.
--
--  Documentation: docs/guide/03-sumcheck.md. Decisions: ADR 0022 (scope,
--  the Challenges record, index names), 0023 (structural Gold), 0026
--  (expressions); frame: ADR 0011, 0020, 0024, 0025.
--
--  What it computes. Given a circuit, its public inputs, the padded
--  sumcheck proof and every verifier challenge, the core replays the
--  verifier of Section 6.7 on symbolic witnesses and emits the
--  constraints that the Ligero layer checks: one linear constraint per
--  layer and one after the input layer (A * W + b = 0, A as sparse
--  Ligero_Term triples, b as a vector), and one quadratic triple per
--  layer (W [c0] * W [c1] = W [cr], generate_lqc_triples). It never
--  touches a transcript: the challenges come from stage 4.
--
--  Layouts (ADR 0022). Challenges.G holds the MAX_LOGW output-binding
--  challenges; the core reads the first Ceil_Lg2 (noutput). For layer J,
--  Challenges.Layer holds, from Chal_Off (C, J): alpha, beta, then one
--  challenge per round r and hand h at 2 + 2 r + h. Sumcheck_Proof.Evals
--  holds, from Proof_Off (C, J): the padded p (0) and p (P2) of hand h
--  in round r at 4 r + 2 h and 4 r + 2 h + 1, then the two padded
--  claims. The pad variables of layer J start at Pad_Off (C, J, Base):
--  the same 4 r + 2 h + k for the round pads, then c0, c1, cr (Section
--  6.5); Base is ninput - npublic (zk/verifier.rs).
--
--  Sizes and memory. The claim expressions of a layer hold at most
--  4 logw + 5 variables (ADR 0026) and are allocated with
--  Layer_Capacity = 4 * Max_Logw + 5 pairs each, on the stack. The input
--  constraint is not an Expression (ADR 0056): Input_Constraint writes
--  one term per private input straight into the Ligero terms, its
--  coefficient computed on the spot, then the few terms of the claims
--  through Input_Tail. It takes time linear in the inputs and no stack
--  in proportion to them, so circuits of the mDoc size fit the default
--  stack.
--
--  Proof status (per instance). Symbolic_Round is Gold by definition:
--  an expression function that is the formula next = p0 l0 + p1 l1 +
--  p2 l2, p1 = claim - p0, written with the Gold operations of
--  Sumcheck_Expression. Input_Constraint is Gold against the formula
--  of Section 6.7 (ADR 0056): term W has witness W and coefficient
--  In_Coef (npublic + W), eq2 read from the bindeq tables (Phase D,
--  M1), the public inputs fold into the constant as
--  Pub_Binding_Ref in input order, and the claims come last as the
--  terms of Input_Tail, built with the Gold operations of
--  Sumcheck_Expression. Verify_Layer and Verifier_Core are Silver with
--  postconditions on the sizes emitted and on the pad indices of the
--  quadratic triples (Gold trivially);
--  every claim expression keeps its variables below the current pad
--  pointer, which is what bounds the expression lengths by 4 logw + 5
--  (ADR 0026). Agreement with the upstream verifier on the emitted
--  constraints is tested on recorded runs (ADR 0027).
--
--  Errors as status (ADR 0022): sizes are checked by preconditions on
--  the records; nothing is raised. Public data only; no constant-time
--  requirement.

pragma SPARK_Mode (On);

with Proof_Levels;
with Sumcheck_Algebra;
with Sumcheck_Expression;

generic
   with package SA is new Sumcheck_Algebra (<>);
   with package SE is new Sumcheck_Expression (SA => SA);
package Sumcheck_Verifier is

   use SA;
   use SE;

   subtype Element is SA.Element;

   -------------------------------------------------------------------
   --  Per-layer block sizes and offsets.
   -------------------------------------------------------------------

   Max_Chal_Size  : constant := 2 * Max_Logw + 2;
   Max_Proof_Size : constant := 4 * Max_Logw + 2;
   Max_Pad_Size   : constant := 4 * Max_Logw + 3;

   function Chal_Size (C : Circuit; J : Natural) return Natural is
     (2 * C.Layers (J).Logw + 2)
   with Global => null, Pre => J <= C.Last_Layer;

   function Proof_Size (C : Circuit; J : Natural) return Natural is
     (4 * C.Layers (J).Logw + 2)
   with Global => null, Pre => J <= C.Last_Layer;

   function Pad_Size (C : Circuit; J : Natural) return Natural is
     (4 * C.Layers (J).Logw + 3)
   with Global => null, Pre => J <= C.Last_Layer;

   function Chal_Off (C : Circuit; J : Natural) return Natural is
     (if J = 0 then 0 else Chal_Off (C, J - 1) + Chal_Size (C, J - 1))
   with Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= C.Last_Layer + 1,
        Post => Chal_Off'Result <= J * Max_Chal_Size
                and then Chal_Off'Result >= 2 * J,
        Subprogram_Variant => (Decreases => J);

   function Proof_Off (C : Circuit; J : Natural) return Natural is
     (if J = 0 then 0 else Proof_Off (C, J - 1) + Proof_Size (C, J - 1))
   with Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= C.Last_Layer + 1,
        Post => Proof_Off'Result <= J * Max_Proof_Size
                and then Proof_Off'Result >= 2 * J,
        Subprogram_Variant => (Decreases => J);

   --  Pad variables are numbered from Base (ninput - npublic).
   function Pad_Off (C : Circuit; J : Natural; Base : Natural)
                     return Natural is
     (if J = 0 then Base
      else Pad_Off (C, J - 1, Base) + Pad_Size (C, J - 1))
   with Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= C.Last_Layer + 1 and then Base <= Max_Wires,
        Post => Pad_Off'Result <= Base + J * Max_Pad_Size
                and then Pad_Off'Result >= Base + 3 * J,
        Subprogram_Variant => (Decreases => J);

   --  One step and monotonicity of Pad_Off, from the hidden recursion.
   procedure Lemma_Pad_Step (C : Circuit; J : Natural; Base : Natural) with
     Ghost, Global => null,
     Pre  => J <= C.Last_Layer and then Base <= Max_Wires,
     Post => Pad_Off (C, J + 1, Base) = Pad_Off (C, J, Base) + Pad_Size (C, J);

   procedure Lemma_Pad_Mono (C : Circuit; I, J : Natural; Base : Natural) with
     Ghost, Global => null,
     Pre  => I <= J and then J <= C.Last_Layer + 1 and then Base <= Max_Wires,
     Post => Pad_Off (C, I, Base) <= Pad_Off (C, J, Base),
     Subprogram_Variant => (Decreases => J);

   function Chal_Total (C : Circuit) return Natural is
     (Chal_Off (C, C.Last_Layer + 1))
   with Global => null;

   function Proof_Total (C : Circuit) return Natural is
     (Proof_Off (C, C.Last_Layer + 1))
   with Global => null;

   --  The number of witnesses the commitment holds (nw of zk/verifier.rs
   --  and of Section 7.4: the private inputs then the pads of every
   --  layer, 4 logw + 3 each), the bound on every witness index the
   --  core emits.
   function Witness_Count (C : Circuit) return Natural is
     (Pad_Off (C, C.Last_Layer + 1, C.Ninput - C.Npublic))
   with Global => null,
        Post   => Witness_Count'Result >= C.Ninput - C.Npublic + 3
                  and then Witness_Count'Result
                           <= C.Ninput + (C.Last_Layer + 1) * Max_Pad_Size;

   --  Every quadratic triple of the core lies below Witness_Count: the
   --  pads of layer J end at Pad_Off (C, J + 1, Base).
   procedure Lemma_Pads_Below (C : Circuit) with
     Ghost, Global => null,
     Post =>
       (for all J in 0 .. C.Last_Layer =>
          Pad_Off (C, J, C.Ninput - C.Npublic) + 4 * C.Layers (J).Logw + 3
          <= Witness_Count (C));

   -------------------------------------------------------------------
   --  Inputs.
   -------------------------------------------------------------------

   --  Largest pad variable index a run can name.
   Max_Pad_Index : constant := Max_Wires + Max_Layers * Max_Pad_Size;

   --  All the verifier challenges of one proof (ADR 0022, D1).
   type Challenges (Last : Index) is record
      G           : Element_Array (0 .. Max_Logw - 1);
      Layer       : Element_Array (0 .. Last);
      Alpha_Input : Element;
   end record;

   --  The padded sumcheck proof, flat (Section 6.6, SumcheckLayerProof).
   type Sumcheck_Proof (Last : Index) is record
      Evals : Element_Array (0 .. Last);
   end record;

   --  A binding challenge vector; the first Logv entries are meaningful.
   subtype Challenge_Vector is Element_Array (0 .. Max_Logw - 1);

   -------------------------------------------------------------------
   --  Outputs (Section 6.7, LigeroTerm and the quadratic triples).
   -------------------------------------------------------------------

   --  The sparse matrix A in coordinate form: entry K is the triple
   --  (Coeff (K), Constraint (K), Witness (K)), K in 0 .. Count - 1.
   --  Three parallel arrays rather than an array of records, so that
   --  the provers see plain array updates on each component.
   type Index_Array is array (Index range <>) of Natural;

   type Ligero_Terms (Max : Index) is record
      Count      : Natural := 0;
      Coeff      : Element_Array (0 .. Max);
      Constraint : Index_Array (0 .. Max);
      Witness    : Index_Array (0 .. Max);
   end record
   with Dynamic_Predicate => Ligero_Terms.Count <= Ligero_Terms.Max + 1;

   type Lqc_Triple is record
      X, Y, Z : Natural;
   end record;

   type Lqc_Array is array (Natural range <>) of Lqc_Triple;

   --  Capacity of the claim expressions of a layer (ADR 0026): two
   --  claim pads, four round pads per round, three claim pads.
   Layer_Capacity : constant Capacity_Type := 4 * Max_Logw + 5;

   --  An upper bound on the Ligero terms emitted: 4 logw + 5 per layer
   --  and ninput - npublic + 2 for the input constraint.
   function A_Bound (C : Circuit) return Natural is
     ((C.Last_Layer + 1) * (4 * Max_Logw + 5) + C.Ninput + 2)
   with Global => null;

   --  Appends the linear constraint "E = 0" as constraint number
   --  B_Count: one entry of A per stored pair (zero coefficients
   --  included, ADR 0026) and Known into B.
   procedure Constrain_To_Be_Zero
     (E       : Expression;
      A       : in out Ligero_Terms;
      B       : in out Element_Array;
      B_Count : in out Natural)
   with
     Global => null,
     Pre  => E.Length <= A.Max + 1 - A.Count
       and then B'First = 0 and then B_Count < B'Length,
     Post => A.Count = A.Count'Old + E.Length
       and then B_Count = B_Count'Old + 1
       and then Same (B (B_Count'Old), E.Known)
       and then (for all K in 0 .. B_Count'Old - 1 =>
                   Same (B (K), B'Old (K)))
       and then (for all I in 1 .. E.Length =>
                   A.Witness (A.Count'Old + I - 1) = E.Terms (I).V)
       and then (for all I in 1 .. E.Length =>
                   A.Constraint (A.Count'Old + I - 1) = B_Count'Old)
       and then (for all I in 1 .. E.Length =>
                   Same (A.Coeff (A.Count'Old + I - 1), E.Terms (I).C))
       and then (for all K in 0 .. A.Count'Old - 1 =>
                   A.Witness (K) = A.Witness'Old (K))
       and then (for all K in 0 .. A.Count'Old - 1 =>
                   A.Constraint (K) = A.Constraint'Old (K))
       and then (for all K in 0 .. A.Count'Old - 1 =>
                   Same (A.Coeff (K), A.Coeff'Old (K)));

   -------------------------------------------------------------------
   --  The symbolic round (Section 6.7, symbolic_sumcheck_round): the
   --  prover's polynomial at the challenge, with p (0) and p (P2) read
   --  from the padded proof plus their pad variables and p (1) deduced
   --  from the claim. Gold by definition (ADR 0023).
   -------------------------------------------------------------------

   function Symbolic_Round
     (Claim      : Expression;
      Pad0, Pad1 : Natural;
      HP0, HP2   : Element;
      Chal       : Element) return Expression
   is
     (Add (Add (Scale (Add_Constant (Var (Pad0, Claim.Capacity), HP0),
                       Lagrange_Basis (Chal) (0)),
                Scale (Sub (Claim,
                            Add_Constant (Var (Pad0, Claim.Capacity), HP0)),
                       Lagrange_Basis (Chal) (1))),
           Scale (Add_Constant (Var (Pad1, Claim.Capacity), HP2),
                  Lagrange_Basis (Chal) (2))))
   with Global => null,
        Pre => Claim.Capacity >= Claim.Length + 3;

   --  The exact shape of a round when the two pad variables are fresh.
   procedure Lemma_Round_Shape
     (Claim      : Expression;
      Pad0, Pad1 : Natural;
      HP0, HP2   : Element;
      Chal       : Element)
   with
     Ghost, Global => null,
     Pre  => Claim.Capacity >= Claim.Length + 3
       and then Pad0 <= Max_Pad_Index
       and then Pad1 = Pad0 + 1
       and then Below (Claim, Pad0),
     Post => Symbolic_Round (Claim, Pad0, Pad1, HP0, HP2, Chal).Length
             <= Claim.Length + 2
       and then Below (Symbolic_Round (Claim, Pad0, Pad1, HP0, HP2, Chal),
                       Pad1 + 1);

   -------------------------------------------------------------------
   --  The claims state between layers (Section 6.7, ClaimsState).
   -------------------------------------------------------------------

   type Claims_State is record
      Logv           : Logw_Type;
      Claim0, Claim1 : Expression (Layer_Capacity);
      HC0, HC1       : Challenge_Vector;
   end record;

   --  Smallest L with 2^L >= N (ceil_lg2 of the reference), for the
   --  number of output-binding challenges in use.
   function Ceil_Lg2 (N : Wire_Count) return Natural with
     Global => null,
     Post => Ceil_Lg2'Result <= 24;

   --  One layer (Section 6.7, verify_layer): combines the two claims
   --  with alpha, runs the 2 logw symbolic rounds, subtracts the product
   --  expression of the padded claims times the bound quad, emits the
   --  linear constraint and the quadratic triple, and hands the next
   --  layer its two claims and binding challenges.
   procedure Verify_Layer
     (C       : Circuit;
      J       : Natural;
      Proof   : Sumcheck_Proof;
      Ch      : Challenges;
      Base    : Natural;
      State   : in out Claims_State;
      A       : in out Ligero_Terms;
      B       : in out Element_Array;
      B_Count : in out Natural;
      Lqc     : out Lqc_Triple)
   with
     Global => null,
     Pre  => J <= C.Last_Layer
       and then Base <= Max_Wires
       and then Base = C.Ninput - C.Npublic
       and then Ch.Last + 1 = Chal_Total (C)
       and then Proof.Last + 1 = Proof_Total (C)
       and then State.Claim0.Length <= 1 and then State.Claim1.Length <= 1
       and then Below (State.Claim0, Pad_Off (C, J, Base))
       and then Below (State.Claim1, Pad_Off (C, J, Base))
       and then A.Max + 1 - A.Count >= 4 * Max_Logw + 5
       and then B'First = 0 and then B_Count < B'Length,
     Post => A.Count <= A.Count'Old + 4 * Max_Logw + 5
       and then B_Count = B_Count'Old + 1
       and then (for all K in 0 .. A.Count'Old - 1 =>
                   A.Witness (K) = A.Witness'Old (K)
                   and then A.Constraint (K) = A.Constraint'Old (K))
       and then (for all K in A.Count'Old .. A.Count - 1 =>
                   A.Witness (K) < Pad_Off (C, J + 1, Base)
                   and then A.Constraint (K) = B_Count'Old)
       and then State.Logv = C.Layers (J).Logw
       and then State.Claim0.Length = 1 and then State.Claim1.Length = 1
       and then Below (State.Claim0, Pad_Off (C, J + 1, Base))
       and then Below (State.Claim1, Pad_Off (C, J + 1, Base))
       and then Lqc = (X => Pad_Off (C, J, Base) + 4 * C.Layers (J).Logw,
                       Y => Pad_Off (C, J, Base) + 4 * C.Layers (J).Logw + 1,
                       Z => Pad_Off (C, J, Base) + 4 * C.Layers (J).Logw + 2);

   --  The coefficient of input I in the input constraint: eq2 at I of
   --  the final binding, read from the eq2 table of bindeq when it fits
   --  (Phase D, M1), computed bit by bit otherwise. That the two agree
   --  is the tested fact that bindeq agrees with eq.
   function In_Coef (I : Natural; State : Claims_State; Alpha : Element)
                     return Element
   is
     (if State.Logv <= Max_Bindeq_Log
      then Beq2 (I, State.Logv, State.HC0, State.HC1, Alpha)
      else Eq2 (I, State.Logv, State.HC0, State.HC1, Alpha))
   with Ghost => Proof_Only, Global => null;

   --  The public inputs folded into the constant of the input
   --  constraint: the sum over the first N public inputs I of
   --  In_Coef (I) * Pub (I), in input order.
   function Pub_Binding_Ref
     (Pub   : Element_Array;
      State : Claims_State;
      Alpha : Element;
      N     : Natural) return Element
   is
     (if N = 0 then Zero
      else SA."+" (Pub_Binding_Ref (Pub, State, Alpha, N - 1),
                   SA."*" (In_Coef (N - 1, State, Alpha), Pub (N - 1))))
   with Ghost => Proof_Only,
        Global => null,
        Pre => Pub'First = 0 and then N <= Pub'Length,
        Subprogram_Variant => (Decreases => N);

   --  The end of the input constraint: the public binding Binding minus
   --  the final claim, claim0 + alpha claim1 (Section 6.7). Its terms
   --  are the pads of the claims, all after the private inputs.
   function Input_Tail
     (Binding : Element;
      State   : Claims_State;
      Alpha   : Element) return Expression
   is
     (Sub (From_Constant (Binding, Layer_Capacity),
           Add (State.Claim0, Scale (State.Claim1, Alpha))))
   with Global => null,
        Pre => State.Claim0.Length <= 1 and then State.Claim1.Length <= 1;

   --  The input constraint (Section 6.7, input_constraint): the
   --  multilinear extension of the inputs at the final binding, public
   --  inputs folded into the constant, minus the final claim. Written
   --  term by term in input order, then the terms of Input_Tail; the
   --  same terms, in the same order and with the same values, as the
   --  sorted Expression of the reference.
   procedure Input_Constraint
     (C       : Circuit;
      Pub     : Element_Array;
      State   : Claims_State;
      Alpha   : Element;
      A       : in out Ligero_Terms;
      B       : in out Element_Array;
      B_Count : in out Natural)
   with
     Global => null,
     Pre  => Pub'First = 0 and then Pub'Length = C.Npublic
       and then State.Claim0.Length <= 1 and then State.Claim1.Length <= 1
       and then Below (State.Claim0, Witness_Count (C))
       and then Below (State.Claim1, Witness_Count (C))
       and then A.Max + 1 - A.Count >= C.Ninput + 2
       and then B'First = 0 and then B_Count < B'Length,
     Post =>
       (Runtime =>
          A.Count <= A.Count'Old + C.Ninput + 2
          and then B_Count = B_Count'Old + 1
          and then (for all K in 0 .. A.Count'Old - 1 =>
                      A.Witness (K) = A.Witness'Old (K)
                      and then A.Constraint (K) = A.Constraint'Old (K))
          and then (for all K in A.Count'Old .. A.Count - 1 =>
                      A.Witness (K) < Witness_Count (C)
                      and then A.Constraint (K) = B_Count'Old),
        Proof_Only =>
          (for all W in 0 .. C.Ninput - C.Npublic - 1 =>
             A.Witness (A.Count'Old + W) = W
             and then A.Constraint (A.Count'Old + W) = B_Count'Old
             and then Same (A.Coeff (A.Count'Old + W),
                            In_Coef (C.Npublic + W, State, Alpha)))
          and then
          (declare
             T : constant Expression :=
               Input_Tail (Pub_Binding_Ref (Pub, State, Alpha, C.Npublic),
                           State, Alpha);
             S : constant Natural := A.Count'Old + (C.Ninput - C.Npublic);
           begin
             A.Count = S + T.Length
             and then (for all I in 1 .. T.Length =>
                         A.Witness (S + I - 1) = T.Terms (I).V
                         and then A.Constraint (S + I - 1) = B_Count'Old
                         and then Same (A.Coeff (S + I - 1), T.Terms (I).C))
             and then Same (B (B_Count'Old), T.Known)));

   --  The whole core (Section 6.7, symbolic_sumcheck_verifier_core).
   procedure Verifier_Core
     (C       : Circuit;
      Pub     : Element_Array;
      Proof   : Sumcheck_Proof;
      Ch      : Challenges;
      A       : out Ligero_Terms;
      B       : out Element_Array;
      Lqc     : out Lqc_Array)
   with
     Global => null,
     Pre  => Pub'First = 0 and then Pub'Length = C.Npublic
       and then Ch.Last + 1 = Chal_Total (C)
       and then Proof.Last + 1 = Proof_Total (C)
       and then A.Max + 1 >= A_Bound (C)
       and then B'First = 0 and then B'Length = C.Last_Layer + 2
       and then Lqc'First = 0 and then Lqc'Last = C.Last_Layer,
     Post => A.Count <= A_Bound (C)
       and then (for all K in 0 .. A.Count - 1 =>
                   A.Witness (K) < Witness_Count (C)
                   and then A.Constraint (K) <= C.Last_Layer + 1)
       and then (for all J in 0 .. C.Last_Layer =>
                   Lqc (J) = (X => Pad_Off (C, J, C.Ninput - C.Npublic)
                                     + 4 * C.Layers (J).Logw,
                              Y => Pad_Off (C, J, C.Ninput - C.Npublic)
                                     + 4 * C.Layers (J).Logw + 1,
                              Z => Pad_Off (C, J, C.Ninput - C.Npublic)
                                     + 4 * C.Layers (J).Logw + 2));

end Sumcheck_Verifier;
