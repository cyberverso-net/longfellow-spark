--  Layer_Coefficients: the slots of one layer, their monomials and their
--  coefficients, from the certificate's counts and hints (ADR 0093). The
--  layer is walked as Check_Layer walks it, with no check: each pair adds
--  its coefficient to the slot its hint names, and a new slot takes its
--  monomial when the hint is the wire's next unused slot. A hint beyond
--  the wire's count names no slot of the pool and is skipped; the model
--  changes no slot below the count there either.
--
--  Each step is a subprogram of its own with its contract, as in
--  Check_Layer: the slot bases, one pair.

separate (Circuit_Checker)
procedure Layer_Coefficients
  (P    : PC.Packed_Circuit;
   K    : CC.Certificate;
   J    : Natural;
   M    : Shape_Array;
   CM   : Coef_Array;
   Mono : in out Mono_Array;
   C    : in out Coef_Pool;
   Fits : out Boolean)
is
   use type SA.Element;
   function "+" (A, B : Element) return Element renames SA."+";
   function "*" (A, B : Element) return Element renames SA."*";

   S  : constant CC.Layer_Span := K.Layers (Walk_Index (P, J));
   NO : constant Natural := Out_Count (P, J);
   L  : constant Natural := Len (P, J);
   NW : constant Natural := P.Layers (J).NW_In;

   --  The shapes and the coefficients the model reads.
   function RJ return Shape_Array is (Reads (P, K, J))
   with Ghost => Proof_Only, Pre => (Proof_Only => J <= P.Last_Layer);
   function CJ return Coef_Array is (Read_Coefs (P, K, J))
   with Ghost => Proof_Only, Pre => (Proof_Only => J <= P.Last_Layer);

   --  What the nested subprograms know of the layer.
   function Ctx return Boolean is
     (J <= P.Last_Layer and then K.NL = P.Last_Layer + 1
      and then CC.Spans_Ok (K) and then S = Span (P, K, J)
      and then NO = Out_Count (P, J) and then S.Wires = NO
      and then L = Len (P, J)
      and then L <= SA.Max_Terms
      and then NW = P.Layers (J).NW_In
      and then NO <= SA.Max_Wires and then NW <= SA.Max_Wires
      and then M'First = 0 and then M'Last = NW - 1
      and then CM'First = 0 and then CM'Last = NW - 1
      and then Same_Shapes (M, RJ) and then Same_Coefs (CM, CJ))
   with Ghost => Proof_Only;

   -------------------------------------------------------------------
   --  The slot bases
   -------------------------------------------------------------------

   function Bases_Ok (Base : Base_Array) return Boolean is
     (Ctx and then Base'First = 0 and then Base'Last = NO
      and then Base (NO) <= Max_Layer_Slots
      and then (for all G in 0 .. NO =>
                  Long_Long_Integer (Base (G)) = Slot_Base (P, K, J, G))
      and then (for all G in 0 .. NO - 1 =>
                  Base (G + 1) = Base (G) + Count_Of (P, K, J, G))
      and then (for all G in 0 .. NO => Base (G) <= Base (NO)))
   with Ghost => Proof_Only;

   procedure Compute_Bases (Base : in out Base_Array; Ok : out Boolean)
   with
     Pre  => (Proof_Only =>
             Ctx and then Base'First = 0 and then Base'Last = NO),
     Post => (Proof_Only =>
             Base'First = 0 and then Base'Last = NO
             and then Ok = (Slot_Base (P, K, J, NO)
                            <= Long_Long_Integer (Max_Layer_Slots))
             and then (if Ok then Bases_Ok (Base)))
   is
      Total : Long_Long_Integer := 0;
      Cnt   : Natural;
   begin
      Base (0) := 0;
      Lemma_Slot_Base_Def (P, K, J, 0);
      for G in 0 .. NO - 1 loop
         Lemma_Count_Of (P, K, J, G);
         Cnt := K.Counts (S.First_Wire + G + 1);
         pragma Assert (Proof_Only => Cnt = Count_Of (P, K, J, G));
         Lemma_Slot_Base_Def (P, K, J, G + 1);
         Total := Total + Long_Long_Integer (Cnt);
         Base (G + 1) :=
           (if Total <= Long_Long_Integer (Max_Layer_Slots)
            then Natural (Total) else Max_Layer_Slots);
         pragma Loop_Invariant (Proof_Only =>
                                  (Total = Slot_Base (P, K, J, G + 1)));
         pragma Loop_Invariant (Proof_Only => Base (0) = 0);
         pragma Loop_Invariant
           (Proof_Only =>
              (if Total <= Long_Long_Integer (Max_Layer_Slots) then
                Long_Long_Integer (Base (G + 1)) = Total
                and then (for all G2 in 0 .. G + 1 =>
                            Long_Long_Integer (Base (G2))
                            = Slot_Base (P, K, J, G2))
                and then (for all G2 in 0 .. G =>
                            Base (G2 + 1)
                            = Base (G2) + Count_Of (P, K, J, G2))
                and then (for all G2 in 0 .. G + 1 =>
                            Base (G2) <= Base (G + 1))));
      end loop;
      Ok := Total <= Long_Long_Integer (Max_Layer_Slots);
   end Compute_Bases;

   --  A wire's region ends before every later wire's base.
   procedure Lemma_Disjoint (Base : Base_Array; G1 : Natural)
   with
     Ghost => Proof_Only,
     Pre   => (Proof_Only => Bases_Ok (Base) and then G1 < NO),
     Post  => (Proof_Only =>
              Base (G1) + Count_Of (P, K, J, G1) <= Base (NO)
              and then (for all G2 in G1 + 1 .. NO =>
                          Base (G1) + Count_Of (P, K, J, G1) <= Base (G2)))
   is
   begin
      for G2 in G1 + 1 .. NO loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all G3 in G1 + 1 .. G2 =>
                Base (G1) + Count_Of (P, K, J, G1) <= Base (G3)));
      end loop;
   end Lemma_Disjoint;

   --  Every earlier wire's region ends before G's base.
   procedure Lemma_Before (Base : Base_Array; G : Natural)
   with
     Ghost => Proof_Only,
     Pre   => (Proof_Only => Bases_Ok (Base) and then G < NO),
     Post  => (Proof_Only =>
              (for all G1 in 0 .. G - 1 =>
                 Base (G1) + Count_Of (P, K, J, G1) <= Base (G)))
   is
   begin
      for G1 in 0 .. G - 1 loop
         Lemma_Disjoint (Base, G1);
         pragma Loop_Invariant
           (Proof_Only =>
              (for all G3 in 0 .. G1 =>
                Base (G3) + Count_Of (P, K, J, G3) <= Base (G)));
      end loop;
   end Lemma_Before;

   -------------------------------------------------------------------
   --  One pair
   -------------------------------------------------------------------

   --  The used counts and the monomials of the slots below each wire's
   --  count are the model's at (N, Q).
   function Monos_Ok
     (Base : Base_Array; Used_A : Nat_Array; Mo : Mono_Array;
      N : Positive; Q : Natural) return Boolean
   is (for all G in 0 .. NO - 1 =>
         Used_A (G) = Used (P, K, J, RJ, N, Q, G)
         and then (for all S2 in 0 .. Count_Of (P, K, J, G) - 1 =>
                     Mo (Base (G) + S2 + 1)
                     = Slot_Mono (P, K, J, RJ, N, Q, G, S2)))
   with Ghost => Proof_Only,
        Pre => (Proof_Only =>
               Ctx and then Bases_Ok (Base)
               and then Used_A'First = 0 and then Used_A'Last = NO
               and then Mo'First = 1 and then Mo'Last = Max_Layer_Slots
               and then N <= SA.Max_Terms + 1);

   --  The coefficients of the slots below each wire's count are the
   --  model's at (N, Q).
   function Coefs_Ok
     (Base : Base_Array; Co : Coef_Pool; N : Positive; Q : Natural)
      return Boolean
   is (for all G in 0 .. NO - 1 =>
         (for all S2 in 0 .. Count_Of (P, K, J, G) - 1 =>
            SA.Same (Co (Base (G) + S2 + 1),
                     Slot_Coef (P, K, J, RJ, CJ, N, Q, G, S2))))
   with Ghost => Proof_Only,
        Pre => (Proof_Only =>
               Ctx and then Bases_Ok (Base)
               and then Co'First = 1 and then Co'Last = Max_Layer_Slots
               and then N <= SA.Max_Terms + 1);

   function State_Ok
     (Base : Base_Array; Used_A : Nat_Array; Mo : Mono_Array;
      Co : Coef_Pool; N : Positive; Q : Natural) return Boolean
   is (Monos_Ok (Base, Used_A, Mo, N, Q) and then Coefs_Ok (Base, Co, N, Q))
   with Ghost => Proof_Only,
        Pre => (Proof_Only =>
               Ctx and then Bases_Ok (Base)
               and then Used_A'First = 0 and then Used_A'Last = NO
               and then Mo'First = 1 and then Mo'Last = Max_Layer_Slots
               and then Co'First = 1 and then Co'Last = Max_Layer_Slots
               and then N <= SA.Max_Terms + 1);

   --  The pair's coefficient Pc added to the slot its hint Hi names,
   --  when that slot is below the wire's count.
   procedure Add_Coef
     (Base : Base_Array;
      Co   : in out Coef_Pool;
      Tm   : SA.Term;
      N    : Positive;
      Q    : Positive;
      Hi   : Natural;
      Pc   : Element)
   with
     Pre  => (Proof_Only =>
             Ctx and then Bases_Ok (Base)
             and then Co'First = 1 and then Co'Last = Max_Layer_Slots
             and then N <= L
             and then Tm = TT (P, J, N) and then Tm.G < NO
             and then Hi = H (P, K, J, RJ, N, Q)
             and then SA.Same (Pc, Pair_Coef (RJ, CJ, TT (P, J, N), Q))
             and then Coefs_Ok (Base, Co, N, Q - 1)),
     Post => (Proof_Only => Coefs_Ok (Base, Co, N, Q))
   is
      G   : constant Natural := Tm.G;
      Co0 : constant Coef_Pool := Co with Ghost => Proof_Only;
   begin
      Lemma_Disjoint (Base, G);
      Lemma_Before (Base, G);
      Lemma_Slot_Coef_Step (P, K, J, RJ, CJ, N, Q, NO);
      Lemma_Count_Of (P, K, J, G);
      if Hi < K.Counts (S.First_Wire + G + 1) then
         pragma Assert
           (Proof_Only =>
              (SA.Same (Co (Base (G) + Hi + 1),
                        Slot_Coef (P, K, J, RJ, CJ, N, Q - 1, G, Hi))));
         pragma Assert
           (Proof_Only =>
              (SA.Same (Slot_Coef (P, K, J, RJ, CJ, N, Q, G, Hi),
                        Slot_Coef (P, K, J, RJ, CJ, N, Q - 1, G, Hi)
                        + Pair_Coef (RJ, CJ, TT (P, J, N), Q))));
         Co (Base (G) + Hi + 1) := Co (Base (G) + Hi + 1) + Pc;
         pragma Assert
           (Proof_Only =>
              (SA.Same (Co (Base (G) + Hi + 1),
                        Slot_Coef (P, K, J, RJ, CJ, N, Q, G, Hi))));
      end if;
      --  Every other slot is unchanged, in the pool and in the model.
      pragma Assert
        (Proof_Only =>
           (for all G2 in 0 .. NO - 1 =>
              (for all S2 in 0 .. Count_Of (P, K, J, G2) - 1 =>
                 (if G2 /= G or else S2 /= Hi then
                    SA.Same (Co (Base (G2) + S2 + 1),
                             Co0 (Base (G2) + S2 + 1))
                    and then
                    SA.Same (Slot_Coef (P, K, J, RJ, CJ, N, Q, G2, S2),
                             Slot_Coef (P, K, J, RJ, CJ, N, Q - 1, G2,
                                        S2))))));
   end Add_Coef;

   procedure Add_Pair
     (Base   : Base_Array;
      Used_A : in out Nat_Array;
      Mo     : in out Mono_Array;
      Co     : in out Coef_Pool;
      Tm     : SA.Term;
      N      : Positive;
      Q      : Positive;
      HP     : Long_Long_Integer)
   with
     Pre  => (Proof_Only =>
             Ctx and then Bases_Ok (Base)
             and then Used_A'First = 0 and then Used_A'Last = NO
             and then Mo'First = 1 and then Mo'Last = Max_Layer_Slots
             and then Co'First = 1 and then Co'Last = Max_Layer_Slots
             and then N <= L
             and then Tm = TT (P, J, N) and then Tm.G < NO
             and then Tm.H0 < NW and then Tm.H1 < NW
             and then Tm.K /= Zero
             and then SA.Same (Tm.K, TT (P, J, N).K)
             and then Q <= Pairs (P, J, RJ, N)
             and then HP = Hint_Pos (P, J, RJ, N - 1)
                           + Long_Long_Integer (Q - 1)
             and then State_Ok (Base, Used_A, Mo, Co, N, Q - 1)),
     Post => (Proof_Only =>
             Used_A'First = 0 and then Used_A'Last = NO
             and then State_Ok (Base, Used_A, Mo, Co, N, Q))
   is
      G   : constant Natural := Tm.G;
      N0  : constant Natural := M (Tm.H0).N;
      Row : Entry_Index;
      Col : Entry_Index;
      Hi  : Natural;
      Cn  : Natural;
      Pm  : Monomial;
      Pc  : Element;
      U   : Natural;
   begin
      Lemma_Disjoint (Base, G);
      Lemma_Before (Base, G);
      Lemma_Used_All (P, K, J, RJ, N, Q, NO);
      Lemma_Slot_Mono_All (P, K, J, RJ, N, Q, NO);
      Lemma_Slot_Coef_Step (P, K, J, RJ, CJ, N, Q, NO);
      Lemma_Hint_At (P, K, J, HP);
      Lemma_Count_Of (P, K, J, G);
      pragma Assert (Proof_Only =>
                       (Shape_At (M, Tm.H0).N = Shape_At (RJ, Tm.H0).N));
      pragma Assert (Proof_Only =>
                       (Shape_At (M, Tm.H1).N = Shape_At (RJ, Tm.H1).N));
      pragma Assert (Proof_Only => N0 >= 1);
      Row := Integer'Min (Max_Entries, (Q - 1) / N0 + 1);
      Col := (Q - 1) mod N0 + 1;
      Hi := (if HP < Long_Long_Integer (S.Hints)
             then K.Hints (S.First_Hint + Natural (HP) + 1)
             else CC.Max_Count + 1);
      pragma Assert (Proof_Only => Hi = H (P, K, J, RJ, N, Q));
      Cn := K.Counts (S.First_Wire + G + 1);
      pragma Assert (Proof_Only => Cn = Count_Of (P, K, J, G));
      --  The pair's monomial and coefficient, from the executable shapes
      --  and coefficients, which are the model's entry by entry.
      Pm := Circuit_Checker.Mono (M (Tm.H1).V (Row), M (Tm.H0).V (Col));
      pragma Assert (Proof_Only =>
                       (M (Tm.H1).V (Row) = Shape_At (RJ, Tm.H1).V (Row)));
      pragma Assert (Proof_Only =>
                       (M (Tm.H0).V (Col) = Shape_At (RJ, Tm.H0).V (Col)));
      pragma Assert (Proof_Only => Pm = Pair_Mono (RJ, Tm, Q));
      Pc := (Tm.K * CM (Tm.H1) (Row)) * CM (Tm.H0) (Col);
      pragma Assert (Proof_Only =>
                       (SA.Same (CM (Tm.H1) (Row), Coefs_At (CJ, Tm.H1) (Row))));
      pragma Assert (Proof_Only =>
                       (SA.Same (CM (Tm.H0) (Col), Coefs_At (CJ, Tm.H0) (Col))));
      pragma Assert (Proof_Only => SA.Same (Pc, Pair_Coef (RJ, CJ, Tm, Q)));
      pragma Assert
        (Proof_Only => SA.Same (Pc, Pair_Coef (RJ, CJ, TT (P, J, N), Q)));
      U := Used_A (G);
      pragma Assert (Proof_Only => U = Used (P, K, J, RJ, N, Q - 1, G));
      Add_Coef (Base, Co, Tm, N, Q, Hi, Pc);
      if Hi < Cn and then Hi = U then
         Mo (Base (G) + Hi + 1) := Pm;
      end if;
      if Hi = U then
         Used_A (G) := U + 1;
      end if;
      pragma Assert
        (Proof_Only => Monos_Ok (Base, Used_A, Mo, N, Q));
   end Add_Pair;

   --  The state after term N is the model's at (N + 1, 0).
   procedure Lemma_Next_Term
     (Base : Base_Array; Used_A : Nat_Array; Mo : Mono_Array;
      Co : Coef_Pool; N : Positive)
   with
     Ghost => Proof_Only,
     Pre   => Ctx and then Bases_Ok (Base)
              and then Used_A'First = 0 and then Used_A'Last = NO
              and then Mo'First = 1 and then Mo'Last = Max_Layer_Slots
              and then Co'First = 1 and then Co'Last = Max_Layer_Slots
              and then N <= L
              and then State_Ok (Base, Used_A, Mo, Co, N, Pairs (P, J, RJ, N)),
     Post  => State_Ok (Base, Used_A, Mo, Co, N + 1, 0)
   is
   begin
      Lemma_Used_All (P, K, J, RJ, N + 1, 0, NO);
      Lemma_Slot_Mono_All (P, K, J, RJ, N + 1, 0, NO);
      Lemma_Slot_Coef_Step (P, K, J, RJ, CJ, N + 1, 0, NO);
      pragma Assert (Monos_Ok (Base, Used_A, Mo, N + 1, 0));
      pragma Assert (Coefs_Ok (Base, Co, N + 1, 0));
   end Lemma_Next_Term;

   Base   : Base_Access;
   Used_A : Nat_Access;
   HP     : Long_Long_Integer := 0;
   Cur    : PC.Cursor := PC.Start (P, J);
   Tm     : SA.Term;
   Ok     : Boolean;
begin
   Mono := [others => (A => 0, B => 0)];
   C := [others => Zero];
   pragma Assert (Proof_Only => S = Span (P, K, J));
   pragma Assert (Proof_Only =>
                    (NO <= SA.Max_Wires and then NW <= SA.Max_Wires));
   pragma Assert (Proof_Only => Ctx);

   Base := new Base_Array'(0 .. NO => 0);
   Compute_Bases (Base.all, Ok);
   Fits := Ok;
   if not Ok then
      Free_Bases (Base);
      return;
   end if;

   Used_A := new Nat_Array'(0 .. NO => 0);
   PC.Lemma_Valid (P);
   pragma Assert (Proof_Only => PC.Expand (P).Layers (J) = P.Layers (J));
   pragma Assert
     (Proof_Only =>
        (SA.Fits (PC.Expand (P).Terms (P.Layers (J).First .. P.Layers (J).Last),
                 NO, NW)));
   PC.Lemma_Walked_Start (P, J);
   Lemma_Hint_Pos_Zero (P, J, RJ);
   Lemma_Used_All (P, K, J, RJ, 1, 0, NO);
   Lemma_Slot_Mono_All (P, K, J, RJ, 1, 0, NO);
   Lemma_Slot_Coef_Step (P, K, J, RJ, CJ, 1, 0, NO);
   pragma Assert (Proof_Only =>
                    (State_Ok (Base.all, Used_A.all, Mono, C, 1, 0)));
   for N in 1 .. L loop
      pragma Loop_Invariant (Proof_Only => PC.Walked (P, J, N - 1, Cur));
      pragma Loop_Invariant
        (Proof_Only =>
           (Base /= null and then Used_A /= null
           and then Base'First = 0 and then Base'Last = NO
           and then Used_A'First = 0 and then Used_A'Last = NO));
      pragma Loop_Invariant (Proof_Only => Bases_Ok (Base.all));
      pragma Loop_Invariant (Proof_Only => HP = Hint_Pos (P, J, RJ, N - 1));
      pragma Loop_Invariant (Proof_Only =>
                               (State_Ok (Base.all, Used_A.all, Mono, C, N, 0)));
      PC.Lemma_Walked_Step (P, J, N, Cur);
      Tm := PC.Term_Of (P, Cur);
      Cur := PC.Step (P, Cur);
      pragma Assert (Proof_Only =>
                       (Tm = PC.Expand (P).Terms (P.Layers (J).First + N - 1)));
      pragma Assert (Proof_Only => Tm = TT (P, J, N));
      pragma Assert (Proof_Only => SA.Same (Tm.K, TT (P, J, N).K));
      pragma Assert (Proof_Only =>
                       (Tm.G < NO and then Tm.H0 < NW and then Tm.H1 < NW));
      Lemma_Hint_Pos_Step (P, J, RJ, N);
      if Tm.K /= Zero then
         pragma Assert
           (Proof_Only => M (Tm.H1).N * M (Tm.H0).N = Pairs (P, J, RJ, N));
         for Q in 1 .. M (Tm.H1).N * M (Tm.H0).N loop
            pragma Loop_Invariant
              (Proof_Only =>
                 (HP = Hint_Pos (P, J, RJ, N - 1) + Long_Long_Integer (Q - 1)));
            pragma Loop_Invariant
              (Proof_Only =>
                 (State_Ok (Base.all, Used_A.all, Mono, C, N, Q - 1)));
            pragma Loop_Invariant
              (Proof_Only =>
                 (Bases_Ok (Base.all)
                 and then Used_A'First = 0 and then Used_A'Last = NO));
            Add_Pair (Base.all, Used_A.all, Mono, C, Tm, N, Q, HP);
            HP := HP + 1;
         end loop;
      end if;
      --  The state after term N is the model's at (N, Pairs (N)), which
      --  is its state at (N + 1, 0).
      pragma Assert (Proof_Only => HP = Hint_Pos (P, J, RJ, N));
      pragma Assert
        (Proof_Only =>
           (State_Ok (Base.all, Used_A.all, Mono, C, N, Pairs (P, J, RJ, N))));
      Lemma_Next_Term (Base.all, Used_A.all, Mono, C, N);
   end loop;

   --  The end of the layer, in the model's terms.
   pragma Assert
     (Proof_Only =>
        (for all G in 0 .. NO - 1 =>
          Long_Long_Integer (Base (G)) = Slot_Base (P, K, J, G)
          and then Base (G) + Count_Of (P, K, J, G) <= Max_Layer_Slots
          and then
          (for all S2 in 0 .. Count_Of (P, K, J, G) - 1 =>
             Mono (Base (G) + S2 + 1) = Mono_End (P, K, J, RJ, G, S2)
             and then SA.Same (C (Base (G) + S2 + 1),
                               Coef_End (P, K, J, RJ, CJ, G, S2)))));
   Free_Bases (Base);
   Free_Nats (Used_A);
end Layer_Coefficients;
