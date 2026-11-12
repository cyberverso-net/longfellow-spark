--  Local_Check: the local identity of one wire of a circuit over
--  GF(2^128), the feasibility study of a proved checker for the
--  registered circuits (#88, F2).
--
--  A wire's terms are K * V (H0) * V (H1), as a layer of the circuit
--  states them. A certificate gives the wire's meaning as the product of
--  two forms A and B, each a sum of coefficients times declared wires
--  (wire 0 carries the constant one), and maps every pair (I, J) of the
--  expansion A * B to the term of the wire it falls into. The check is
--  executable; its lemma says that, for every assignment of the wires,
--  the value of the terms is the product of the values of the forms.
--
--  The forms' length is bounded (Max_Form, 3 declared wires and the
--  constant on the hash circuit, the bound F2 measured), and so is the
--  number of terms (Max_Terms). Normalising a product of two forms of
--  length k costs k * k pairs, each matched to one term.
--
--  The lemmas state equality with Same, the logical equality of
--  Field_GF2_128 (ADR 0066), which the provers rewrite with; they do not
--  rewrite with the predefined "=" of the record. The field operations
--  are reached through wrappers without a postcondition, "+" for Add and
--  "*" for Mul, as Sumcheck_Algebra does (ADR 0070): the provers see them
--  as opaque, and only the ring laws in the body look inside them. The
--  model of GF2_128 (Mul_Ref) never enters the proof of the lemma.
--
--  Proof status: Check_Product Silver; Lemma_Product Gold, by the ring
--  laws of Field_GF2_128 (Lemma_Mul_Assoc, Lemma_Mul_Comm,
--  Lemma_Mul_Distrib, Lemma_Add_Assoc, Lemma_Add_Comm, Lemma_Add_Zero,
--  Lemma_Add_Neg). On the task branch only, as the feasibility task
--  asks.

pragma SPARK_Mode (On);

with Proof_Levels;
with GF2_128; use GF2_128;
with Field_GF2_128;

package Local_Check is

   Max_Wire  : constant := 2 ** 24;
   Max_Terms : constant := 16;
   Max_Form  : constant := 4;

   --  A + B is Add (A, B), A * B is Mul (A, B); the bodies are hidden.
   function "+" (A, B : Element) return Element with
     Global => null, Inline,
     Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");
   function "*" (A, B : Element) return Element with
     Global => null, Inline,
     Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   --  The logical equality of the lemmas (ADR 0066): equality of terms
   --  for the provers, the predefined "=" at run time.
   function Same (A, B : Element) return Boolean
     renames Field_GF2_128.Same;

   subtype Wire is Natural range 0 .. Max_Wire;
   type Values is array (Wire range <>) of Element;

   type Term is record
      H0, H1 : Wire;
      K      : Element;
   end record;
   subtype Term_Count is Natural range 0 .. Max_Terms;
   subtype Term_Index is Positive range 1 .. Max_Terms;
   type Term_Array is array (Term_Index) of Term;

   type Form_Entry is record
      W : Wire;
      C : Element;
   end record;
   subtype Form_Count is Natural range 0 .. Max_Form;
   subtype Form_Index is Positive range 1 .. Max_Form;
   type Form_Array is array (Form_Index) of Form_Entry;

   --  The certificate's map: the term each pair (I, J) falls into.
   type Pair_Map is array (Form_Index, Form_Index) of Term_Index;

   function Term_Value (T : Term; V : Values) return Element is
     ((T.K * V (T.H0)) * V (T.H1))
   with Ghost => Proof_Only, Global => null,
        Pre => T.H0 in V'Range and then T.H1 in V'Range;

   function Wires_In (T : Term_Array; N : Term_Count; V : Values)
     return Boolean
   is (for all I in 1 .. N =>
         T (I).H0 in V'Range and then T (I).H1 in V'Range)
   with Ghost => Proof_Only, Global => null;

   function Form_In (F : Form_Array; N : Form_Count; V : Values)
     return Boolean
   is (for all I in 1 .. N => F (I).W in V'Range)
   with Ghost => Proof_Only, Global => null;

   --  The value of the first N terms, and of the first N entries of a form.
   function Sum_Terms (T : Term_Array; N : Term_Count; V : Values)
     return Element
   is (if N = 0 then Zero
       else Sum_Terms (T, N - 1, V) + Term_Value (T (N), V))
   with Ghost => Proof_Only, Global => null,
        Pre => Wires_In (T, N, V),
        Subprogram_Variant => (Decreases => N);

   function Sum_Form (F : Form_Array; N : Form_Count; V : Values)
     return Element
   is (if N = 0 then Zero
       else Sum_Form (F, N - 1, V) + F (N).C * V (F (N).W))
   with Ghost => Proof_Only, Global => null,
        Pre => Form_In (F, N, V),
        Subprogram_Variant => (Decreases => N);

   --  The pair (I, J) falls into term T when its two wires are T's.
   function Same_Monomial (A, B : Wire; T : Term) return Boolean is
     ((A = T.H0 and then B = T.H1) or else (A = T.H1 and then B = T.H0));

   --  The coefficient the expansion gives to term K: the sum of the
   --  products of coefficients of the pairs the map sends there, the
   --  pairs taken row by row (I, then J).
   function Collected
     (A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      M : Pair_Map; K : Term_Index;
      I : Form_Count; J : Form_Count) return Element
   is (if I = 0 then Zero
       elsif J = 0 then Collected (A, NA, B, NB, M, K, I - 1, NB)
       else Collected (A, NA, B, NB, M, K, I, J - 1)
            + (if M (I, J) = K then A (I).C * B (J).C else Zero))
   with Global => null,
        Pre => NA <= Max_Form and then NB <= Max_Form and then J <= NB,
        Subprogram_Variant => (Decreases => I, Decreases => J);

   --  The check: every pair is mapped to a term of the same monomial,
   --  and every term's coefficient is what the expansion collects there.
   function Check_Product
     (T : Term_Array; NT : Term_Count;
      A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      M : Pair_Map) return Boolean
   is ((for all I in 1 .. NA =>
          (for all J in 1 .. NB =>
             M (I, J) <= NT
             and then Same_Monomial (A (I).W, B (J).W, T (M (I, J)))))
       and then
       (for all K in 1 .. NT =>
          T (K).K = Collected (A, NA, B, NB, M, K, NA, NB)))
   with Global => null;

   --  The lemma: for every assignment V, the value of the wire's terms is
   --  the product of the values of the two forms.
   procedure Lemma_Product
     (T : Term_Array; NT : Term_Count;
      A : Form_Array; NA : Form_Count;
      B : Form_Array; NB : Form_Count;
      M : Pair_Map; V : Values)
   with Ghost => Proof_Only, Global => null,
        Pre  => Wires_In (T, NT, V)
                and then Form_In (A, NA, V) and then Form_In (B, NB, V)
                and then Check_Product (T, NT, A, NA, B, NB, M),
        Post => Same (Sum_Terms (T, NT, V),
                      Sum_Form (A, NA, V) * Sum_Form (B, NB, V));

end Local_Check;
