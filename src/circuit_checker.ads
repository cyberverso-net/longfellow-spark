--  Circuit_Checker: the walk of the circuit checker and its model
--  (ADR 0093), generic over the field (ADR 0024).
--
--  The walk goes over the layers of a packed circuit from the last one,
--  which reads the inputs, to layer 0. Every wire of a layer gets a
--  meaning over declared variables, from the meanings of the wires its
--  terms read: input wire i is variable i (variable 0 the constant one);
--  each term k * w(h1) * w(h0) with k /= 0 adds the pairs of the
--  expansion of meaning (h1) times meaning (h0) into the slots of its
--  wire, one slot per monomial. The certificate (Circuit_Certificates)
--  says which slot each pair falls into, and the walk checks it:
--
--  - a pair goes to a used slot of its own monomial, or to the next
--    unused slot when its monomial is new to the wire, and then that
--    monomial is none of the wire's used slots';
--  - at the end of the layer every slot the certificate counts is used.
--
--  So a wire's slots are the distinct monomials of its expansion in the
--  order they first appear: one normal form, whatever the certificate.
--  The kind of a wire is the checker's rule: linear when every slot has
--  degree at most 1 and they name at most Max_Form variables besides the
--  constant (its meaning is its slots), declared otherwise (it becomes
--  the next variable, which the checker numbers in the order of the
--  walk). The certificate names no variable, no coefficient, no kind.
--
--  What is proved, in two parts:
--
--  - Walk computes Accepts exactly: (St = Accepted) = Accepts (P, K).
--    Accepts is a function of the circuit and the certificate, defined
--    by a model of the walk over the shapes of the meanings (their
--    variables), which is all that acceptance depends on. Coverage is
--    by construction: the model ranges over the circuit's terms and
--    wires, not over the certificate's entries.
--  - Lemma_Accepts (block 3, in the body's second part): when Accepts
--    holds and the packed evaluation of the verifier returned OK, with
--    input wire 0 equal to one, there are values of the declared
--    variables, each the value of its home wire, at which every fact of
--    the model holds.
--
--  The model is written as recursive expression functions over the
--  position of the walk in a layer: the terms before N, and the first Q
--  pairs of term N. Each is hidden, as Packed_Circuits.Cursor_At is, and
--  a lemma gives one step of its body.
--
--  Documentation: docs/guide/10-certified-circuits.md, Section 3.
--  Decisions: ADR 0091, ADR 0093 (the model, the limits).
--
--  Proof status (per instance): Walk Gold against Accepts, Silver on its
--  statuses.
--
--  Trusted: Same as the equality of the field (register row T6); the
--  contracts at Proof_Only, the model among them, never compiled (T8);
--  the reader of the circuit file and Expand as for the verifier (R4,
--  T8).
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, circuits and
--  their certificates are public data (ADR 0037; register row S4).

pragma SPARK_Mode (On);

with Proof_Levels;
with Sumcheck_Algebra;
with Packed_Circuits;
with Circuit_Certificates;

generic
   with package SA is new Sumcheck_Algebra (<>);
   with package PC is new Packed_Circuits (SA);
   Max_Form           : Circuit_Certificates.Form_Bound;
   Max_Terms_Per_Wire : Positive;
   Max_Slots          : Circuit_Certificates.Slot_Count;
   Max_Layer_Slots    : Positive;
   Max_Vars           : Positive;
package Circuit_Checker is

   package CC renames Circuit_Certificates;

   subtype Element is SA.Element;
   Zero : Element renames SA.Zero;
   use type SA.F.Element;

   type Status is
     (Accepted,
      Cert_Mismatch,   --  layers or wires that are not the circuit's
      Too_Many_Terms,  --  a wire with more than Max_Terms_Per_Wire terms
      Too_Many_Slots,  --  a wire with more than Max_Slots slots
      Pool_Full,       --  a layer with more than Max_Layer_Slots slots
      Too_Many_Vars,   --  more than Max_Vars declared variables
      Bad_Hint,        --  a slot beyond the count, or not the next unused one
      Wrong_Monomial,  --  a pair sent to a slot of another monomial
      Duplicate_Slot,  --  a new slot whose monomial the wire already has
      Empty_Slot,      --  a counted slot no pair reaches
      Hints_Left);     --  a layer's hints not all used, or too few

   -------------------------------------------------------------------
   --  Shapes and monomials
   -------------------------------------------------------------------

   Max_Entries : constant := 4;
   subtype Entry_Count is Natural range 0 .. Max_Entries;
   subtype Entry_Index is Positive range 1 .. Max_Entries;
   type Var_List is array (Entry_Index) of Natural;

   --  The shape of a meaning: how many entries, and their variables.
   type Form_Shape is record
      N : Entry_Count;
      V : Var_List;
   end record;
   No_Shape : constant Form_Shape := (N => 0, V => [others => 0]);
   type Shape_Array is array (Natural range <>) of Form_Shape;

   --  Total in the index, as SA.W_At is.
   function Shape_At (M : Shape_Array; H : Natural) return Form_Shape is
     (if H in M'Range then M (H) else No_Shape)
   with Global => null;

   --  A monomial v_A * v_B with A <= B; variable 0 stands for one, so
   --  (0, B) is of degree 1 and (0, 0) the constant.
   type Monomial is record
      A, B : Natural;
   end record;
   function Mono (X, Y : Natural) return Monomial is
     (if X <= Y then (A => X, B => Y) else (A => Y, B => X))
   with Global => null;

   -------------------------------------------------------------------
   --  The layers and the certificate's part for each
   -------------------------------------------------------------------

   --  The place of circuit layer J in the walk, and in the certificate.
   function Walk_Index (P : PC.Packed_Circuit; J : Natural) return Natural
   is (P.Last_Layer + 1 - J)
   with Global => null, Pre => J <= P.Last_Layer;

   function Len (P : PC.Packed_Circuit; J : Natural) return Natural is
     (if P.Layers (J).Last + 1 >= P.Layers (J).First
      then P.Layers (J).Last + 1 - P.Layers (J).First else 0)
   with Global => null, Pre => J <= P.Last_Layer;

   function Out_Count (P : PC.Packed_Circuit; J : Natural) return Natural
   is (if J = 0 then P.Noutput else P.Layers (J - 1).NW_In)
   with Global => null, Pre => J <= P.Last_Layer;

   --  Term N (from 1) of layer J.
   function TT (P : PC.Packed_Circuit; J, N : Natural) return SA.Term is
     (PC.Term_At (P, J, N))
   with Ghost => Proof_Only, Global => null, Pre => J <= P.Last_Layer;

   function Span (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural)
     return CC.Layer_Span
   is (if Walk_Index (P, J) in 1 .. K.NL then K.Layers (Walk_Index (P, J))
       else (others => 0))
   with Global => null, Pre => J <= P.Last_Layer;

   --  The slot count the certificate gives wire G of layer J.
   function Count_Of
     (P : PC.Packed_Circuit; K : CC.Certificate; J, G : Natural)
      return Natural
   is (if CC.Spans_Ok (K) and then G < Span (P, K, J).Wires
       then K.Counts (Span (P, K, J).First_Wire + G + 1) else 0)
   with Global => null, Pre => J <= P.Last_Layer;

   --  The hint at position X (from 0) of layer J; beyond the span, one
   --  no slot has.
   function Hint_At
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      X : Long_Long_Integer) return Natural
   is (if CC.Spans_Ok (K)
          and then X in 0 .. Long_Long_Integer (Span (P, K, J).Hints) - 1
       then K.Hints (Span (P, K, J).First_Hint + Natural (X) + 1)
       else CC.Max_Count + 1)
   with Global => null, Pre => J <= P.Last_Layer;

   -------------------------------------------------------------------
   --  The model of one layer, over the shapes M of the wires it reads
   -------------------------------------------------------------------

   --  The pairs of a term's expansion: none for an assertion (k = 0).
   function Term_Pairs (M : Shape_Array; Tm : SA.Term) return Natural is
     (if Tm.K = Zero then 0
      else Shape_At (M, Tm.H1).N * Shape_At (M, Tm.H0).N)
   with Global => null;

   --  Pair Q (from 1) of a term's expansion: entry (Q - 1) / N0 + 1 of
   --  meaning (h1) times entry (Q - 1) mod N0 + 1 of meaning (h0), N0 the
   --  length of meaning (h0). Its monomial.
   function Pair_Mono (M : Shape_Array; Tm : SA.Term; Q : Positive)
     return Monomial
   is (if Shape_At (M, Tm.H0).N = 0 then (A => 0, B => 0)
       else Mono
         (Shape_At (M, Tm.H1).V
            (Integer'Min (Max_Entries, (Q - 1) / Shape_At (M, Tm.H0).N + 1)),
          Shape_At (M, Tm.H0).V ((Q - 1) mod Shape_At (M, Tm.H0).N + 1)))
   with Global => null;

   function Pairs
     (P : PC.Packed_Circuit; J : Natural; M : Shape_Array; N : Natural)
      return Natural
   is (Term_Pairs (M, TT (P, J, N)))
   with Ghost => Proof_Only, Global => null, Pre => J <= P.Last_Layer;

   --  The hints the terms before N + 1 use.
   function Hint_Pos
     (P : PC.Packed_Circuit; J : Natural; M : Shape_Array; N : Natural)
      return Long_Long_Integer
   is (if N = 0 then 0
       else Hint_Pos (P, J, M, N - 1) + Long_Long_Integer (Pairs (P, J, M, N)))
   with Ghost => Proof_Only, Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms,
        Post => Hint_Pos'Result in
                  0 .. Long_Long_Integer (N) * Max_Entries * Max_Entries,
        Subprogram_Variant => (Decreases => N);

   --  The hint of pair Q of term N.
   function H
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; N : Positive; Q : Positive) return Natural
   is (Hint_At (P, K, J,
                Hint_Pos (P, J, M, N - 1) + Long_Long_Integer (Q - 1)))
   with Ghost => Proof_Only, Global => null,
        Pre => J <= P.Last_Layer and then N <= SA.Max_Terms;

   --  The used slots of wire G after the terms before N and Q pairs of
   --  term N (Q = 0: after the terms before N).
   function Used
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; N : Positive; Q : Natural; G : Natural)
      return Natural
   is (if Q = 0 then
         (if N = 1 then 0
          else Used (P, K, J, M, N - 1, Pairs (P, J, M, N - 1), G))
       else Used (P, K, J, M, N, Q - 1, G)
            + (if G = TT (P, J, N).G
                  and then H (P, K, J, M, N, Q)
                           = Used (P, K, J, M, N, Q - 1, G)
               then 1 else 0))
   with Ghost => Proof_Only, Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms,
        Subprogram_Variant => (Decreases => N, Decreases => Q);

   --  The monomial of slot S (from 0) of wire G at the same point.
   function Slot_Mono
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; N : Positive; Q : Natural; G, S : Natural)
      return Monomial
   is (if Q = 0 then
         (if N = 1 then (A => 0, B => 0)
          else Slot_Mono (P, K, J, M, N - 1, Pairs (P, J, M, N - 1), G, S))
       elsif G = TT (P, J, N).G
         and then H (P, K, J, M, N, Q) = Used (P, K, J, M, N, Q - 1, G)
         and then S = H (P, K, J, M, N, Q)
       then Pair_Mono (M, TT (P, J, N), Q)
       else Slot_Mono (P, K, J, M, N, Q - 1, G, S))
   with Ghost => Proof_Only, Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms,
        Subprogram_Variant => (Decreases => N, Decreases => Q);

   --  Pair Q of term N passes the checks on its hint.
   function Pair_Ok
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; N : Positive; Q : Positive) return Boolean
   is (H (P, K, J, M, N, Q) < Count_Of (P, K, J, TT (P, J, N).G)
       and then H (P, K, J, M, N, Q)
                <= Used (P, K, J, M, N, Q - 1, TT (P, J, N).G)
       and then
       (if H (P, K, J, M, N, Q)
           < Used (P, K, J, M, N, Q - 1, TT (P, J, N).G)
        then Slot_Mono (P, K, J, M, N, Q - 1, TT (P, J, N).G,
                        H (P, K, J, M, N, Q))
             = Pair_Mono (M, TT (P, J, N), Q)
        else (for all S in 0 .. Used (P, K, J, M, N, Q - 1, TT (P, J, N).G) - 1
                => Slot_Mono (P, K, J, M, N, Q - 1, TT (P, J, N).G, S)
                   /= Pair_Mono (M, TT (P, J, N), Q))))
   with Ghost => Proof_Only, Global => null,
        Pre => J <= P.Last_Layer and then N <= SA.Max_Terms;

   --  Every pair up to pair Q of term N passes.
   function Pairs_Ok
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; N : Positive; Q : Natural) return Boolean
   is (if Q = 0 then
         (N = 1 or else Pairs_Ok (P, K, J, M, N - 1, Pairs (P, J, M, N - 1)))
       else Pairs_Ok (P, K, J, M, N, Q - 1)
            and then Pair_Ok (P, K, J, M, N, Q))
   with Ghost => Proof_Only, Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms,
        Subprogram_Variant => (Decreases => N, Decreases => Q);

   --  The terms (k /= 0) of wire G among the first N.
   function Wire_Terms
     (P : PC.Packed_Circuit; J : Natural; N : Natural; G : Natural)
      return Natural
   is (if N = 0 then 0
       else Wire_Terms (P, J, N - 1, G)
            + (if TT (P, J, N).G = G and then TT (P, J, N).K /= Zero
               then 1 else 0))
   with Ghost => Proof_Only, Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms,
        Post => Wire_Terms'Result <= N,
        Subprogram_Variant => (Decreases => N);

   --  The end of the layer: the state after its last term (N = Len + 1,
   --  Q = 0), as Used and Slot_Mono give it.
   function Used_End
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; G : Natural) return Natural
   is (if Len (P, J) = 0 then 0
       else Used (P, K, J, M, Len (P, J), Pairs (P, J, M, Len (P, J)), G))
   with Ghost => Proof_Only, Global => null,
        Pre => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms;

   function Mono_End
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; G, S : Natural) return Monomial
   is (if Len (P, J) = 0 then (A => 0, B => 0)
       else Slot_Mono (P, K, J, M, Len (P, J),
                       Pairs (P, J, M, Len (P, J)), G, S))
   with Ghost => Proof_Only, Global => null,
        Pre => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms;

   --  The slots of the wires before G.
   function Slot_Base
     (P : PC.Packed_Circuit; K : CC.Certificate; J, G : Natural)
      return Long_Long_Integer
   is (if G = 0 then 0
       else Slot_Base (P, K, J, G - 1)
            + Long_Long_Integer (Count_Of (P, K, J, G - 1)))
   with Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= P.Last_Layer and then G <= SA.Max_Wires,
        Post => Slot_Base'Result in 0 .. Long_Long_Integer (G) * 2**16,
        Subprogram_Variant => (Decreases => G);

   --  Layer J passes, with the shapes M of the wires it reads.
   function Layer_Ok
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array) return Boolean
   is (Span (P, K, J).Wires = Out_Count (P, J)
       and then Hint_Pos (P, J, M, Len (P, J))
                = Long_Long_Integer (Span (P, K, J).Hints)
       and then Slot_Base (P, K, J, Out_Count (P, J))
                <= Long_Long_Integer (Max_Layer_Slots)
       and then (Len (P, J) = 0
                 or else Pairs_Ok (P, K, J, M, Len (P, J),
                                   Pairs (P, J, M, Len (P, J))))
       and then (for all G in 0 .. Out_Count (P, J) - 1 =>
                   Count_Of (P, K, J, G) <= Max_Slots
                   and then Wire_Terms (P, J, Len (P, J), G)
                            <= Max_Terms_Per_Wire
                   and then Used_End (P, K, J, M, G) = Count_Of (P, K, J, G)))
   with Ghost => Proof_Only, Global => null,
        Pre => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms
               and then Out_Count (P, J) <= SA.Max_Wires;

   --  The kind rule: wire G is linear when every slot has degree at most
   --  1 and at most Max_Form of them are not the constant.
   function Linear
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; G : Natural) return Boolean
   is ((for all S in 0 .. Count_Of (P, K, J, G) - 1 =>
          Mono_End (P, K, J, M, G, S).A = 0)
       and then Count_Of (P, K, J, G)
                <= Max_Form
                   + (if (for some S in 0 .. Count_Of (P, K, J, G) - 1 =>
                            Mono_End (P, K, J, M, G, S).B = 0)
                      then 1 else 0))
   with Ghost => Proof_Only, Global => null,
        Pre => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms;

   --  The declared wires before G.
   function Declared_Before
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; G : Natural) return Natural
   is (if G = 0 then 0
       else Declared_Before (P, K, J, M, G - 1)
            + (if Linear (P, K, J, M, G - 1) then 0 else 1))
   with Ghost => Proof_Only, Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms,
        Post => Declared_Before'Result <= G,
        Subprogram_Variant => (Decreases => G);

   --  The shape of wire G's meaning, the next variable numbered from Vb.
   function Out_Shape
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; Vb : Natural; G : Natural) return Form_Shape
   is (if Linear (P, K, J, M, G) and then Count_Of (P, K, J, G) <= Max_Entries
       then (N => Count_Of (P, K, J, G),
             V => [for E in Entry_Index =>
                     (if E <= Count_Of (P, K, J, G)
                      then Mono_End (P, K, J, M, G, E - 1).B else 0)])
       else (N => 1,
             V => [1 => Vb + Declared_Before (P, K, J, M, G), others => 0]))
   with Ghost => Proof_Only, Global => null,
        Pre => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms
               and then Vb <= Max_Vars and then G <= SA.Max_Wires;

   function Out_Shapes
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; Vb : Natural) return Shape_Array
   is ([for G in 0 .. Out_Count (P, J) - 1 => Out_Shape (P, K, J, M, Vb, G)])
   with Ghost => Proof_Only, Global => null,
        Pre => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms
               and then Vb <= Max_Vars
               and then Out_Count (P, J) <= SA.Max_Wires;

   -------------------------------------------------------------------
   --  The model of the walk, and what it accepts
   -------------------------------------------------------------------

   --  The shapes of the input wires: input wire I is variable I.
   function Input_Shapes (P : PC.Packed_Circuit) return Shape_Array is
     ([for I in 0 .. P.Ninput - 1 => (N => 1, V => [1 => I, others => 0])])
   with Ghost => Proof_Only, Global => null;

   --  The walk from layer J down to layer 0, the wires of layer J reading
   --  shapes M, the variables numbered from Vb.
   function Walk_From
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; Vb : Natural) return Boolean
   is (Layer_Ok (P, K, J, M)
       and then Vb + Declared_Before (P, K, J, M, Out_Count (P, J))
                <= Max_Vars
       and then
       (J = 0
        or else Walk_From
                  (P, K, J - 1, Out_Shapes (P, K, J, M, Vb),
                   Vb + Declared_Before (P, K, J, M, Out_Count (P, J)))))
   with Ghost => Proof_Only, Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= P.Last_Layer and then Vb <= Max_Vars,
        Subprogram_Variant => (Decreases => J);

   function Accepts (P : PC.Packed_Circuit; K : CC.Certificate)
     return Boolean
   is (K.NL = P.Last_Layer + 1
       and then CC.Spans_Ok (K)
       and then P.Ninput <= Max_Vars
       and then Walk_From (P, K, P.Last_Layer, Input_Shapes (P), P.Ninput))
   with Ghost => Proof_Only, Global => null;

   -------------------------------------------------------------------
   --  The walk
   -------------------------------------------------------------------

   procedure Walk
     (P  : PC.Packed_Circuit;
      K  : CC.Certificate;
      St : out Status)
   with
     Global => null,
     Pre    =>
       (Runtime    => PC.Indices_Ok (P) and then PC.Layers_Ok (P),
        Proof_Only => PC.Valid (P) and then SA.Well_Formed (PC.Expand (P))),
     Post   =>
       (Proof_Only =>
          (St = Accepted) = Accepts (P, K));

end Circuit_Checker;
