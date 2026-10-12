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
--  Proof status (per instance). Symbolic_Round is Gold by definition:
--  an expression function that is the formula next = p0 l0 + p1 l1 +
--  p2 l2, p1 = claim - p0, written with the Gold operations of
--  Sumcheck_Expression. Verify_Layer, Input_Constraint and
--  Verifier_Core are Silver with postconditions on the sizes emitted
--  and on the pad indices of the quadratic triples (Gold trivially);
--  every claim expression keeps its variables below the current pad
--  pointer, which is what bounds the expression lengths by 4 logw + 5
--  (ADR 0026). Agreement with the upstream verifier on the emitted
--  constraints is tested on recorded runs (ADR 0027).
--
--  Errors as status (ADR 0022): sizes are checked by preconditions on
--  the records; nothing is raised. Public data only; no constant-time
--  requirement.

pragma SPARK_Mode (On);

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
        Post => Chal_Off'Result <= J * Max_Chal_Size,
        Subprogram_Variant => (Decreases => J);

   function Proof_Off (C : Circuit; J : Natural) return Natural is
     (if J = 0 then 0 else Proof_Off (C, J - 1) + Proof_Size (C, J - 1))
   with Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= C.Last_Layer + 1,
        Post => Proof_Off'Result <= J * Max_Proof_Size,
        Subprogram_Variant => (Decreases => J);

   --  Pad variables are numbered from Base (ninput - npublic).
   function Pad_Off (C : Circuit; J : Natural; Base : Natural)
                     return Natural is
     (if J = 0 then Base
      else Pad_Off (C, J - 1, Base) + Pad_Size (C, J - 1))
   with Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= C.Last_Layer + 1 and then Base <= Max_Wires,
        Post => Pad_Off'Result <= Base + J * Max_Pad_Size,
        Subprogram_Variant => (Decreases => J);

   function Chal_Total (C : Circuit) return Natural is
     (Chal_Off (C, C.Last_Layer + 1))
   with Global => null;

   function Proof_Total (C : Circuit) return Natural is
     (Proof_Off (C, C.Last_Layer + 1))
   with Global => null;

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

   --  Capacity of every expression of a run (ADR 0026).
   function Capacity_Of (C : Circuit) return Capacity_Type is
     (Natural'Max (C.Ninput - C.Npublic + 2, 4 * Max_Logw + 5))
   with Global => null;

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

   --  Every variable of E is below Bound: the claim expressions only
   --  ever name pad variables already assigned.
   function Below (E : Expression; Bound : Natural) return Boolean is
     (for all W in Natural => (if Has (E, W) then W < Bound))
   with Ghost, Global => null;

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

   type Claims_State (Capacity : Capacity_Type) is record
      Logv           : Logw_Type;
      Claim0, Claim1 : Expression (Capacity);
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
       and then State.Capacity = Capacity_Of (C)
       and then State.Claim0.Length <= 1 and then State.Claim1.Length <= 1
       and then Below (State.Claim0, Pad_Off (C, J, Base))
       and then Below (State.Claim1, Pad_Off (C, J, Base))
       and then A.Max + 1 - A.Count >= 4 * Max_Logw + 5
       and then B'First = 0 and then B_Count < B'Length,
     Post => A.Count <= A.Count'Old + 4 * Max_Logw + 5
       and then B_Count = B_Count'Old + 1
       and then State.Capacity = Capacity_Of (C)
       and then State.Logv = C.Layers (J).Logw
       and then State.Claim0.Length = 1 and then State.Claim1.Length = 1
       and then Below (State.Claim0, Pad_Off (C, J + 1, Base))
       and then Below (State.Claim1, Pad_Off (C, J + 1, Base))
       and then Lqc = (X => Pad_Off (C, J, Base) + 4 * C.Layers (J).Logw,
                       Y => Pad_Off (C, J, Base) + 4 * C.Layers (J).Logw + 1,
                       Z => Pad_Off (C, J, Base) + 4 * C.Layers (J).Logw + 2);

   --  The input constraint (Section 6.7, input_constraint): the
   --  multilinear extension of the inputs at the final binding, public
   --  inputs folded into the constant, minus the final claim.
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
       and then State.Capacity = Capacity_Of (C)
       and then State.Claim0.Length <= 1 and then State.Claim1.Length <= 1
       and then A.Max + 1 - A.Count >= C.Ninput + 2
       and then B'First = 0 and then B_Count < B'Length,
     Post => A.Count <= A.Count'Old + C.Ninput + 2
       and then B_Count = B_Count'Old + 1;

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
       and then (for all J in 0 .. C.Last_Layer =>
                   Lqc (J) = (X => Pad_Off (C, J, C.Ninput - C.Npublic)
                                     + 4 * C.Layers (J).Logw,
                              Y => Pad_Off (C, J, C.Ninput - C.Npublic)
                                     + 4 * C.Layers (J).Logw + 1,
                              Z => Pad_Off (C, J, C.Ninput - C.Npublic)
                                     + 4 * C.Layers (J).Logw + 2));

end Sumcheck_Verifier;
