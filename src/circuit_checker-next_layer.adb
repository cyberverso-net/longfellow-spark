--  Next_Layer: the meanings of one layer's wires from its slots (ADR
--  0093). A wire is linear when every slot has degree at most 1 and they
--  name at most Max_Form variables besides the constant: its meaning is
--  its slots, each slot's B with its coefficient. Otherwise it is
--  declared: its meaning is its variable, Vb plus the declared wires
--  before it, with the coefficient one. The kind is decided from the
--  monomials alone, as in Check_Layer.Wire_Shape.

separate (Circuit_Checker)
procedure Next_Layer
  (P    : PC.Packed_Circuit;
   K    : CC.Certificate;
   J    : Natural;
   Vb   : Natural;
   Mono : Mono_Array;
   C    : Coef_Pool;
   NM   : in out Shape_Array;
   NC   : in out Coef_Array;
   Lin  : in out Flag_Array)
is
   S  : constant CC.Layer_Span := K.Layers (Walk_Index (P, J));
   NO : constant Natural := Out_Count (P, J);

   function RJ return Shape_Array is (Reads (P, K, J))
   with Ghost => Proof_Only, Pre => (Proof_Only => J <= P.Last_Layer);
   function CJ return Coef_Array is (Read_Coefs (P, K, J))
   with Ghost => Proof_Only, Pre => (Proof_Only => J <= P.Last_Layer);

   --  What the nested subprogram knows of the layer.
   function Ctx return Boolean is
     (J <= P.Last_Layer and then K.NL = P.Last_Layer + 1
      and then CC.Spans_Ok (K) and then S = Span (P, K, J)
      and then NO = Out_Count (P, J) and then S.Wires = NO
      and then Len (P, J) <= SA.Max_Terms
      and then NO <= SA.Max_Wires and then Vb <= Max_Vars
      and then Mono'First = 1 and then Mono'Last = Max_Layer_Slots
      and then C'First = 1 and then C'Last = Max_Layer_Slots)
   with Ghost => Proof_Only;

   --  The meaning of wire G, whose slots start after Bg.
   procedure One_Wire
     (G    : Natural;
      Bg   : Natural;
      Decl : Natural;
      Sh   : out Form_Shape;
      Cf   : out Coef_List;
      Lg   : out Boolean)
   with
     Pre  => (Proof_Only =>
             Ctx and then G < NO
             and then Decl = Declared_Before (P, K, J, RJ, G)
             and then Decl <= G
             and then Bg <= Max_Layer_Slots
             and then Count_Of (P, K, J, G) <= Max_Layer_Slots - Bg
             and then (for all S2 in 0 .. Count_Of (P, K, J, G) - 1 =>
                         Mono (Bg + S2 + 1) = Mono_End (P, K, J, RJ, G, S2)
                         and then SA.Same (C (Bg + S2 + 1),
                                           Coef_End (P, K, J, RJ, CJ, G, S2)))),
     Post => (Proof_Only =>
             Lg = Linear (P, K, J, RJ, G)
             and then Sh.N = Out_Shape (P, K, J, RJ, Vb, G).N
             and then (for all E in Entry_Index =>
                         Sh.V (E) = Out_Shape (P, K, J, RJ, Vb, G).V (E))
             and then
             (for all E in Entry_Index =>
                SA.Same (Cf (E),
                         (if Lg and then Count_Of (P, K, J, G) <= Max_Entries
                          then (if E <= Count_Of (P, K, J, G)
                                then Coef_End (P, K, J, RJ, CJ, G, E - 1)
                                else Zero)
                          else (if E = 1 then SA.One else Zero)))))
   is
      Cn    : Natural;
      All_A : Boolean := True;    --  every slot of degree at most 1
      Const : Boolean := False;   --  a slot is the constant
   begin
      Lemma_Count_Of (P, K, J, G);
      Cn := K.Counts (S.First_Wire + G + 1);
      pragma Assert (Proof_Only => Cn = Count_Of (P, K, J, G));
      for S2 in 0 .. Cn - 1 loop
         All_A := All_A and then Mono (Bg + S2 + 1).A = 0;
         Const := Const or else Mono (Bg + S2 + 1).B = 0;
         pragma Loop_Invariant
           (Proof_Only =>
              (All_A = (for all S3 in 0 .. S2 =>
                         Mono_End (P, K, J, RJ, G, S3).A = 0)));
         pragma Loop_Invariant
           (Proof_Only =>
              (Const = (for some S3 in 0 .. S2 =>
                         Mono_End (P, K, J, RJ, G, S3).B = 0)));
      end loop;
      Lg := All_A and then Cn <= Max_Form + (if Const then 1 else 0);
      pragma Assert (Proof_Only => Lg = Linear (P, K, J, RJ, G));
      if Lg then
         pragma Assert (Proof_Only => Cn <= Max_Entries);
         Sh := (N => Cn, V => [others => 0]);
         Cf := [others => Zero];
         for E2 in 1 .. Cn loop
            Sh.V (E2) := Mono (Bg + E2).B;
            Cf (E2) := C (Bg + E2);
            pragma Loop_Invariant (Proof_Only => Sh.N = Cn);
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all E3 in 1 .. E2 =>
                   Sh.V (E3) = Mono_End (P, K, J, RJ, G, E3 - 1).B
                   and then SA.Same (Cf (E3),
                                     Coef_End (P, K, J, RJ, CJ, G, E3 - 1))));
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all E3 in E2 + 1 .. Max_Entries =>
                   Sh.V (E3) = 0 and then SA.Same (Cf (E3), Zero)));
         end loop;
      else
         Sh := (N => 1, V => [1 => Vb + Decl, others => 0]);
         Cf := [1 => SA.One, others => Zero];
      end if;
   end One_Wire;

   Bg   : Natural := 0;
   Decl : Natural := 0;
   Sh   : Form_Shape;
   Cf   : Coef_List;
   Lg   : Boolean;
begin
   pragma Assert (Proof_Only => S = Span (P, K, J));
   PC.Lemma_Valid (P);
   pragma Assert (Proof_Only => Len (P, J) <= SA.Max_Terms);
   pragma Assert (Proof_Only => Ctx);
   Lemma_Slot_Base_Def (P, K, J, 0);
   Lemma_Declared_Def (P, K, J, RJ, 0);
   for G in 0 .. NO - 1 loop
      pragma Loop_Invariant
        (Proof_Only =>
           (NM'First = 0 and then NM'Last = NO - 1
           and then NC'First = 0 and then NC'Last = NO - 1
           and then Lin'First = 0 and then Lin'Last = NO - 1));
      pragma Loop_Invariant (Proof_Only =>
                               (Long_Long_Integer (Bg) = Slot_Base (P, K, J, G)));
      pragma Loop_Invariant
        (Proof_Only =>
           (Decl = Declared_Before (P, K, J, RJ, G) and then Decl <= G));
      pragma Loop_Invariant
        (Proof_Only =>
           (for all G2 in 0 .. G - 1 =>
             Lin (G2) = Linear (P, K, J, RJ, G2)
             and then NM (G2).N = Out_Shapes (P, K, J, RJ, Vb) (G2).N
             and then (for all E in Entry_Index =>
                         NM (G2).V (E) = Out_Shapes (P, K, J, RJ, Vb) (G2).V (E)
                         and then
                         SA.Same (NC (G2) (E),
                                  Out_Coefs (P, K, J, RJ, CJ) (G2) (E)))));
      One_Wire (G, Bg, Decl, Sh, Cf, Lg);
      NM (G) := Sh;
      NC (G) := Cf;
      Lin (G) := Lg;
      pragma Assert
        (Proof_Only =>
           (for all E in Entry_Index =>
             SA.Same (NC (G) (E), Out_Coefs (P, K, J, RJ, CJ) (G) (E))));
      Lemma_Declared_Def (P, K, J, RJ, G + 1);
      if not Lg then
         Decl := Decl + 1;
      end if;
      Lemma_Count_Of (P, K, J, G);
      Lemma_Slot_Base_Def (P, K, J, G + 1);
      Bg := Bg + K.Counts (S.First_Wire + G + 1);
   end loop;
end Next_Layer;
