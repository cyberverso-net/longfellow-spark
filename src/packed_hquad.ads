--  Packed_HQuad: the first step of the bound quad of a layer, read from
--  the packed circuit (the memory milestone, ADR 0080, block 2). As
--  upstream's bind_g (rust/runtime/sumcheck/src/hquad.rs at d5e6be7),
--  the terms of the layer are rebuilt one at a time from the deltas
--  (Packed_Circuits, the walk), bound with g, and merged as they come:
--  the working array has one entry per run of equal hands, never one per
--  term. On the mDoc hash circuit the largest layer, 3,578,789 terms,
--  has 439,013 runs; the largest working array, 1,153,333 entries, is
--  the one of a layer of 1,429,054 terms.
--
--  Layer_Runs counts the runs, so that the working array is allocated
--  once at its size. Bind_Merge is the shared kernel: the verifier's
--  Bind_Quad_Packed uses it here, the prover in a later block. The
--  rounds then run Bind_H of Sumcheck_HQuad, unchanged, on the merged
--  entries. Eval_Bound_Quad_Packed is the verifier's form when the eq
--  tables do not fit (Logv or Logw above Max_Bindeq_Log): a sum over
--  the walk, with no array at all.
--
--  The model is the layer of the ghost expansion, Layer_Of (P, J), the
--  layer of PC.Expand (P). Every result is stated on it exactly as the
--  kernels of Sumcheck_HQuad state theirs on the layer of an expanded
--  circuit: Bind_Merge gives what Merge_Terms gives (the invariant of
--  the rounds at round 0), Bind_Quad_Packed what Bind_Quad gives
--  (EBQT_Ref), Eval_Bound_Quad_Packed what Eval_Bound_Quad gives
--  (EBQ_Ref). The coefficient of a term travels from the walk to the
--  model by Same, the logical equality (Lemma_Walked_Step of
--  Packed_Circuits), since the equality of the field may not be the
--  logical one.
--
--  Bind_Step_Packed is a copy of Bind_Step (the body of Sumcheck_HQuad)
--  with Layer_Of (P, J) where Bind_Step names the layer T0: on the
--  packed path the layer is a value of level Proof_Only, which SPARK does
--  not accept as the actual of a parameter that is not ghost. The copy is
--  temporary: it is removed when the expanded path leaves the executable
--  code (issue #59).
--
--  Proof status: Gold for every subprogram against the references
--  above, except that Bind_Merge without the eq2 table (Logv above
--  Max_Bindeq_Log) states the run count only, as Merge_Terms does: its
--  coefficients are tested, not proved. No caller of this unit takes
--  that branch.
--  The kernels of Sumcheck_HQuad and their contracts are unchanged.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, circuits and
--  challenges are public data (ADR 0037).

pragma SPARK_Mode (On);

with Proof_Levels;
with Sumcheck_Algebra;
with Packed_Circuits;
with Sumcheck_HQuad;

generic
   with package SA is new Sumcheck_Algebra (<>);
   with package PC is new Packed_Circuits (SA);
   with package HQ is new Sumcheck_HQuad (SA);
package Packed_HQuad is

   subtype Element is SA.Element;
   subtype Element_Array is SA.Element_Array;
   subtype Term is SA.Term;
   subtype Term_Array is SA.Term_Array;

   use SA.F;
   use type SA.Term;

   Zero : Element renames SA.Zero;

   --  The layer J of the expansion of P: the terms Layer_Terms gives on
   --  Expand (P), taken as a slice, since Layer_Terms asks of its
   --  circuit the predicate of Circuit, which Valid does not state.
   function Layer_Of (P : PC.Packed_Circuit; J : Natural) return Term_Array
   is
     (PC.Expand (P).Terms (P.Layers (J).First .. P.Layers (J).Last))
   with Ghost => Proof_Only,
        Global => null,
        Pre    => PC.Valid (P) and then PC.Layers_Ok (P)
                  and then J <= P.Last_Layer;

   --  The number of runs of equal hands in a layer of Len terms.
   function Runs (T : Term_Array) return Natural is
     (if T'Length = 0 then 0 else HQ.Run_Id (T, T'Length - 1) + 1)
   with Ghost => Proof_Only, Global => null;

   --  The layer bound with g, as the invariant of the rounds reads it.
   function Bound_Layer
     (P      : PC.Packed_Circuit;
      J      : Natural;
      Logv   : Natural;
      G0, G1 : Element_Array;
      Alpha  : Element;
      Beta   : Element) return Term_Array
   is
     (HQ.BQ.Bound_Array (Layer_Of (P, J), Logv, G0, G1, Alpha, Beta))
   with Ghost => Proof_Only,
        Global => null,
        Pre    => PC.Valid (P) and then PC.Layers_Ok (P)
                  and then J <= P.Last_Layer
                  and then G0'First = 0 and then G1'First = 0
                  and then Logv <= G0'Length and then Logv <= G1'Length
                  and then Logv <= SA.Max_Bindeq_Log;

   --  The number of runs of layer J: one walk, a new run at each change
   --  of hands.
   procedure Layer_Runs (P : PC.Packed_Circuit; J : Natural; N : out Natural)
   with
     Global => null,
     Pre    =>
       (Runtime    =>
          J <= P.Last_Layer
          and then P.Layers (J).Last + 1 >= P.Layers (J).First,
        Proof_Only => PC.Valid (P) and then PC.Layers_Ok (P)),
     Post   =>
       (Runtime    => N <= PC.Layer_Len (P, J),
        Proof_Only => N = Runs (Layer_Of (P, J)));

   --  bind_g and the merge of the runs, from the walk: the first NT
   --  entries of W are the runs of the layer bound with g, as
   --  Merge_Terms leaves them. E is the eq2 table when Logv fits it;
   --  above, each coefficient is Bound_K and only the size is stated, as
   --  Merge_Terms states it without the tables.
   procedure Bind_Merge
     (P      : PC.Packed_Circuit;
      J      : Natural;
      E      : Element_Array;
      Logv   : Natural;
      G0, G1 : Element_Array;
      Alpha  : Element;
      Beta   : Element;
      C0, C1 : Element_Array;
      W      : in out Term_Array;
      NT     : out Natural)
   with
     Global => null,
     Pre    =>
       (Runtime    =>
          J <= P.Last_Layer
          and then P.Layers (J).Last + 1 >= P.Layers (J).First
          and then W'First = P.Layers (J).First
          and then G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= SA.Max_Logw
          and then C0'First = 0 and then C1'First = 0
          and then E'First = 0
          and then
          (if Logv <= SA.Max_Bindeq_Log
           then E'Last = SA.Table_Len (Logv) - 1),
        Proof_Only =>
          PC.Valid (P) and then PC.Layers_Ok (P)
          and then W'Length >= Runs (Layer_Of (P, J))
          and then
          (if Logv <= SA.Max_Bindeq_Log then
             (for all X in E'Range =>
                Same (E (X), SA.Beq2 (X, Logv, G0, G1, Alpha))))),
     Post   =>
       (Runtime    => NT <= W'Length,
        Proof_Only =>
          NT = Runs (Layer_Of (P, J))
          and then
          (if Logv <= SA.Max_Bindeq_Log then
             HQ.BQ.Inv (W, NT,
                        Bound_Layer (P, J, Logv, G0, G1, Alpha, Beta),
                        C0, 0, C1, 0)));

   --  One round of one hand on the merged entries: Bind_Step of
   --  Sumcheck_HQuad with Layer_Of (P, J) in place of T0 (see the
   --  header). Removed with the expanded path (issue #59).
   procedure Bind_Step_Packed
     (T        : in out Term_Array;
      NT       : in out Natural;
      H        : HQ.Hand;
      R        : Natural;
      HC0, HC1 : Element_Array;
      P        : PC.Packed_Circuit;
      J        : Natural;
      Logv     : Natural;
      G0, G1   : Element_Array;
      Alpha    : Element;
      Beta     : Element)
   with
     Global => null,
     Pre    =>
       (Runtime    =>
          NT <= T'Length
          and then HC0'First = 0 and then HC1'First = 0
          and then R < HC0'Length and then R < HC1'Length,
        Proof_Only =>
          PC.Valid (P) and then PC.Layers_Ok (P) and then J <= P.Last_Layer
          and then G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= SA.Max_Bindeq_Log
          and then
          HQ.BQ.Inv (T, NT, Bound_Layer (P, J, Logv, G0, G1, Alpha, Beta),
                     HC0, (if H = 0 then R else R + 1), HC1, R)),
     Post   =>
       (Runtime    => NT <= T'Length,
        Proof_Only =>
          HQ.BQ.Inv (T, NT, Bound_Layer (P, J, Logv, G0, G1, Alpha, Beta),
                     HC0, R + 1, HC1, (if H = 0 then R else R + 1)));

   --  bind_quad of the verifier (ADR 0073) on layer J of P: as
   --  Bind_Quad of Sumcheck_HQuad on the layer of the expansion, with
   --  the working array at the number of runs.
   procedure Bind_Quad_Packed
     (P           : PC.Packed_Circuit;
      J           : Natural;
      Logv        : Natural;
      G0, G1      : Element_Array;
      HC0, HC1    : Element_Array;
      Logw        : Natural;
      Alpha, Beta : Element;
      V           : out Element)
   with
     Global => null,
     Pre    =>
       (Runtime    =>
          J <= P.Last_Layer
          and then P.Layers (J).Last + 1 >= P.Layers (J).First
          and then G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= SA.Max_Bindeq_Log
          and then HC0'First = 0 and then HC1'First = 0
          and then Logw <= HC0'Length and then Logw <= HC1'Length
          and then Logw <= SA.Max_Bindeq_Log,
        Proof_Only => PC.Valid (P) and then PC.Layers_Ok (P)),
     Post   =>
       (Proof_Only =>
          Same (V,
                SA.EBQT_Ref (Layer_Of (P, J), PC.Layer_Len (P, J), Logv,
                             G0, G1, HC0, HC1, Logw, Alpha, Beta)));

   --  Eval_Bound_Quad of Sumcheck_Algebra on layer J of P, summed over
   --  the walk: the verifier's form when the eq tables do not fit.
   procedure Eval_Bound_Quad_Packed
     (P           : PC.Packed_Circuit;
      J           : Natural;
      Logv        : Natural;
      G0, G1      : Element_Array;
      HC0, HC1    : Element_Array;
      Logw        : Natural;
      Alpha, Beta : Element;
      V           : out Element)
   with
     Global => null,
     Pre    =>
       (Runtime    =>
          J <= P.Last_Layer
          and then P.Layers (J).Last + 1 >= P.Layers (J).First
          and then G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= SA.Max_Logw
          and then HC0'First = 0 and then HC1'First = 0
          and then Logw <= HC0'Length and then Logw <= HC1'Length
          and then Logw <= SA.Max_Logw,
        Proof_Only => PC.Valid (P) and then PC.Layers_Ok (P)),
     Post   =>
       (Proof_Only =>
          Same (V,
                SA.EBQ_Ref (Layer_Of (P, J), PC.Layer_Len (P, J), Logv,
                            G0, G1, HC0, HC1, Logw, Alpha, Beta)));

end Packed_HQuad;
