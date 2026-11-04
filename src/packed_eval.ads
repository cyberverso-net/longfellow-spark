--  Packed_Eval: the forward evaluation of a circuit from its packed form
--  (the memory milestone, ADR 0080, block 3). The prover computes the
--  wires of every layer here, as upstream's eval_circuit does with
--  for_each_term (rust/runtime/sumcheck/src/eval.rs at d5e6be7): the
--  terms of a layer are rebuilt one at a time from the deltas
--  (Packed_Circuits, the walk) and accumulated as they come. Eval_Layer
--  is Eval_Quad of Sumcheck_Algebra over the walk; Eval_Circuit drives
--  the layers as the expanded Eval_Circuit does, each layer's wires in
--  a heap segment of its own (block 4), so that the prover frees them
--  once the layer is proved.
--
--  The model is the ghost expansion Expand (P). Every result is stated
--  on it, at level Proof_Only, exactly as Eval_Quad and Eval_Circuit
--  state theirs on an expanded circuit (Acc_Ref, Z_Ref, Layer_Holds,
--  Layer_Z); the coefficient of a term travels from the walk to the
--  model by Same, the logical equality (Lemma_Walked_Step). The sizes
--  come from the shape of the packed circuit, Shape_Of (P); where the
--  references name the shape of the expansion, Lemma_Off_Eq joins the
--  two, since Off hides its recursion.
--
--  Proof status: Gold against the references of Sumcheck_Algebra on the
--  expansion. The expanded Eval_Circuit stays proved as the oracle that
--  prover_kat compares this unit with on the small circuits; it is not
--  on the path of the programs.
--
--  Constant-time discipline (ADR 0051): as Eval_Quad, which Eval_Layer
--  follows statement by statement. The branch on k = Zero reads a
--  circuit constant, public; the Z test of a term sets OK from a product
--  of wires, the satisfiability check of the prover (header of
--  zk_prover.ads). The guarantee is scoped to builds with assertions
--  disabled (ADR 0006).

pragma SPARK_Mode (On);

with Proof_Levels;
with Sumcheck_Algebra;
with Packed_Circuits;

generic
   with package SA is new Sumcheck_Algebra (<>);
   with package PC is new Packed_Circuits (SA);
package Packed_Eval is

   subtype Element is SA.Element;
   subtype Element_Array is SA.Element_Array;
   subtype Term_Array is SA.Term_Array;
   subtype Packed_Circuit is PC.Packed_Circuit;
   subtype Shape is SA.Shape;

   use type SA.Raw_Shape;

   Zero : Element renames SA.Zero;

   --  The layer J of the expansion of P: the terms Layer_Terms gives on
   --  Expand (P), taken as a slice (as Packed_HQuad.Layer_Of).
   function Layer_Of (P : Packed_Circuit; J : Natural) return Term_Array
   is
     (PC.Expand (P).Terms (P.Layers (J).First .. P.Layers (J).Last))
   with Ghost => Proof_Only,
        Global => null,
        Pre    => PC.Valid (P) and then PC.Layers_Ok (P)
                  and then J <= P.Last_Layer;

   --  The number of output wires of layer J (NW_Out of the expansion).
   function Out_Count (P : Packed_Circuit; J : Natural) return SA.Wire_Count
   is
     (if J = 0 then P.Noutput else P.Layers (J - 1).NW_In)
   with Global => null, Pre => J <= P.Last_Layer;

   --  The shape of the packed circuit, a Shape. Its precondition is the
   --  executable part of what the loader proves of the circuit: the
   --  indices of the form, its layers and Shape_Ok of its shape, which
   --  the command line checks once where the circuit enters the program
   --  (ADR 0072) and the proof carries from the loader's postcondition.
   --  An expression function, visible to the callers: a caller that
   --  sizes its buffers with the shape of P must see the same shape
   --  here, since Total_Wires below reads it through a hidden recursion
   --  that an equality of records does not cross.
   function Shape_Of (P : Packed_Circuit) return Shape is
     (PC.Shape_Of (P))
   with Global => null,
        Pre  => PC.Indices_Ok (P) and then PC.Layers_Ok (P)
                and then SA.Shape_Ok (PC.Shape_Of (P));

   --  Eval_Quad of layer J from the walk: V (G) accumulates
   --  k * w (h1) * w (h0) over the terms with g = G and k /= Zero, in
   --  that association, and OK says whether every Z assertion of the
   --  layer (k = Zero) holds on the input wires W (Base + h). W is the
   --  buffer of Eval_Circuit, Base the offset of the layer's input
   --  segment in it.
   procedure Eval_Layer
     (P    : Packed_Circuit;
      J    : Natural;
      W    : Element_Array;
      Base : Natural;
      V    : out Element_Array;
      OK   : out Boolean)
   with
     Global => null,
     Pre    =>
       (Runtime    =>
          J <= P.Last_Layer
          and then P.Layers (J).Last + 1 >= P.Layers (J).First
          and then W'First = 0 and then V'First = 0
          and then W'Length <= Natural'Last - SA.Max_Wires
          and then Base <= W'Length
          and then P.Layers (J).NW_In <= W'Length - Base
          and then V'Length = Out_Count (P, J),
        Proof_Only =>
          PC.Valid (P) and then PC.Layers_Ok (P)
          and then SA.Well_Formed (PC.Expand (P))),
     Post   =>
       (Proof_Only =>
          OK = SA.Z_Ref (W, Base, Layer_Of (P, J), PC.Layer_Len (P, J))
          and then
          (for all G in V'Range =>
             SA.F.Same (V (G),
                   SA.Acc_Ref (W, Base, Layer_Of (P, J),
                               PC.Layer_Len (P, J), G))));

   --  Eval_Circuit of Sumcheck_Algebra from the packed form, the wires
   --  one segment per layer (ADR 0080, block 4): Wr comes with every
   --  segment null (Allocate_Segs) and leaves with segment J the wires
   --  computed by layer J and the last segment the inputs W, each in
   --  its own heap array of Seg_Size (S, J) elements; OK says whether
   --  every Z assertion holds and every output of layer 0 is zero. The
   --  postcondition is the one of the expanded Eval_Circuit on the
   --  expansion of P, stated layer by layer on the segments
   --  (Layer_Holds_Seg, Layer_Z_Seg), so that the prover can free the
   --  segment of a layer once the layer is proved.
   procedure Eval_Circuit
     (P  : Packed_Circuit;
      W  : Element_Array;
      Wr : in out SA.Seg_Array;
      OK : out Boolean)
   with
     Global => null,
     Pre    =>
       (Runtime    =>
          PC.Indices_Ok (P) and then PC.Layers_Ok (P)
          and then SA.Shape_Ok (PC.Shape_Of (P))
          and then W'First = 0 and then W'Length = P.Ninput
          and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
          and then SA.Segs_Null (Wr),
        Proof_Only =>
          PC.Valid (P) and then SA.Well_Formed (PC.Expand (P))),
     Post   =>
       (Runtime    => SA.Segs_Shape (Wr, Shape_Of (P)),
        Proof_Only =>
          (for all I in 0 .. P.Ninput - 1 =>
             SA.F.Same (Wr (P.Last_Layer + 1) (I), W (I)))
          and then
          (for all J in 0 .. P.Last_Layer =>
             SA.Layer_Holds_Seg (PC.Expand (P), Wr (J).all, Wr (J + 1).all,
                                 J))
          and then
          OK = ((for all J in 0 .. P.Last_Layer =>
                   SA.Layer_Z_Seg (PC.Expand (P), Wr (J + 1).all, J))
                and then
                (for all G in 0 .. P.Noutput - 1 =>
                   SA.F."=" (Wr (0) (G), Zero))));

end Packed_Eval;
