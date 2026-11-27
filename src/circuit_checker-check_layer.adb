--  Check_Layer: one layer of the walk (ADR 0093). Every check sets a
--  flag rather than leaving: the layer is walked to its end, and once a
--  check has failed the slots are no longer updated. So each flag is,
--  at every step, the conjunction the model states, and the state of
--  the slots is the model's as long as every check before has passed.
--
--  Each step is a subprogram of its own with its contract, so that each
--  proof sees only the facts it needs (docs/guide/verification-
--  approach.md, "Lessons of the proofs"): the slot bases, the regions of
--  the wires in the pool, one pair, the shape of one wire.

separate (Circuit_Checker)
procedure Check_Layer
  (P       : PC.Packed_Circuit;
   K       : CC.Certificate;
   J       : Natural;
   M       : Shape_Array;
   Vb      : Natural;
   Pool    : in out Mono_Array;
   Next    : out Shape_Access;
   Vb_Next : out Natural;
   St      : out Status)
is
   S   : constant CC.Layer_Span := K.Layers (Walk_Index (P, J));
   NO  : constant Natural := Out_Count (P, J);
   L   : constant Natural := Len (P, J);
   NW  : constant Natural := P.Layers (J).NW_In;

   --  The shapes the model reads: the walk's M, field by field.
   function RJ return Shape_Array is (Reads (P, K, J))
   with Ghost => Proof_Only, Pre => J <= P.Last_Layer;

   --  What the nested subprograms know of the layer: the precondition of
   --  Check_Layer and the values of the constants above, which they do
   --  not see otherwise.
   function Ctx return Boolean is
     (J <= P.Last_Layer and then K.NL = P.Last_Layer + 1
      and then CC.Spans_Ok (K) and then S = Span (P, K, J)
      and then NO = Out_Count (P, J) and then S.Wires = NO
      and then L = Len (P, J) and then L <= SA.Max_Terms
      and then NW = P.Layers (J).NW_In
      and then NO <= SA.Max_Wires and then NW <= SA.Max_Wires
      and then M'First = 0 and then M'Last = NW - 1
      and then Same_Shapes (M, RJ)
      and then Vb <= Max_Vars)
   with Ghost => Proof_Only;

   -------------------------------------------------------------------
   --  The slot bases
   -------------------------------------------------------------------

   --  The bases of the wires' regions in the pool, when they fit.
   function Bases_Ok (Base : Base_Array) return Boolean is
     (Ctx and then Base'First = 0 and then Base'Last = NO
      and then Base (0) = 0
      and then Base (NO) <= Max_Layer_Slots
      and then (for all G in 0 .. NO - 1 =>
                  Base (G + 1) = Base (G) + Count_Of (P, K, J, G))
      and then (for all G in 0 .. NO => Base (G) <= Base (NO)))
   with Ghost => Proof_Only;

   procedure Compute_Bases
     (Base      : in out Base_Array;
      Counts_Ok : out Boolean;
      Fits      : out Boolean)
   with
     Pre  => Ctx and then Base'First = 0 and then Base'Last = NO,
     Post => Base'First = 0 and then Base'Last = NO
             and then Counts_Ok
                      = (for all G in 0 .. NO - 1 =>
                           Count_Of (P, K, J, G) <= Max_Slots)
             and then Fits
                      = (Slot_Base (P, K, J, NO)
                         <= Long_Long_Integer (Max_Layer_Slots))
             and then (if Fits then Bases_Ok (Base))
   is
      Total : Long_Long_Integer := 0;
      Cnt   : Natural;
   begin
      Counts_Ok := True;
      Base (0) := 0;
      Lemma_Slot_Base_Def (P, K, J, 0);
      for G in 0 .. NO - 1 loop
         Lemma_Count_Of (P, K, J, G);
         Cnt := K.Counts (S.First_Wire + G + 1);
         pragma Assert (Cnt = Count_Of (P, K, J, G));
         Counts_Ok := Counts_Ok and then Cnt <= Max_Slots;
         Lemma_Slot_Base_Def (P, K, J, G + 1);
         Total := Total + Long_Long_Integer (Cnt);
         Base (G + 1) :=
           (if Total <= Long_Long_Integer (Max_Layer_Slots)
            then Natural (Total) else Max_Layer_Slots);
         pragma Loop_Invariant (Total = Slot_Base (P, K, J, G + 1));
         pragma Loop_Invariant (Base (0) = 0);
         pragma Loop_Invariant
           (Counts_Ok = (for all G2 in 0 .. G =>
                           Count_Of (P, K, J, G2) <= Max_Slots));
         pragma Loop_Invariant
           (if Total <= Long_Long_Integer (Max_Layer_Slots) then
              Long_Long_Integer (Base (G + 1)) = Total
              and then (for all G2 in 0 .. G =>
                          Base (G2 + 1)
                          = Base (G2) + Count_Of (P, K, J, G2))
              and then (for all G2 in 0 .. G + 1 =>
                          Base (G2) <= Base (G + 1)));
      end loop;
      Fits := Total <= Long_Long_Integer (Max_Layer_Slots);
   end Compute_Bases;

   --  The bases never decrease: a wire's region ends where the next
   --  begins, so it ends before every later wire's base.
   procedure Lemma_Disjoint (Base : Base_Array; G1 : Natural)
   with
     Ghost => Proof_Only,
     Pre   => Bases_Ok (Base) and then G1 < NO,
     Post  => Base (G1) + Count_Of (P, K, J, G1) <= Base (NO)
              and then (for all G2 in G1 + 1 .. NO =>
                          Base (G1) + Count_Of (P, K, J, G1) <= Base (G2))
   is
   begin
      for G2 in G1 + 1 .. NO loop
         pragma Loop_Invariant
           (for all G3 in G1 + 1 .. G2 =>
              Base (G1) + Count_Of (P, K, J, G1) <= Base (G3));
      end loop;
   end Lemma_Disjoint;

   --  Every earlier wire's region ends before G's base.
   procedure Lemma_Before (Base : Base_Array; G : Natural)
   with
     Ghost => Proof_Only,
     Pre   => Bases_Ok (Base) and then G < NO,
     Post  => (for all G1 in 0 .. G - 1 =>
                 Base (G1) + Count_Of (P, K, J, G1) <= Base (G))
   is
   begin
      for G1 in 0 .. G - 1 loop
         Lemma_Disjoint (Base, G1);
         pragma Loop_Invariant
           (for all G3 in 0 .. G1 =>
              Base (G3) + Count_Of (P, K, J, G3) <= Base (G));
      end loop;
   end Lemma_Before;

   -------------------------------------------------------------------
   --  One pair
   -------------------------------------------------------------------

   --  The state of the slots is the model's at (N, Q).
   function State_Ok
     (Base : Base_Array; Used_A : Nat_Array; Pool : Mono_Array;
      N : Positive; Q : Natural) return Boolean
   is (for all G in 0 .. NO - 1 =>
         Used_A (G) = Used (P, K, J, RJ, N, Q, G)
         and then Used_A (G) <= Count_Of (P, K, J, G)
         and then (for all S2 in 0 .. Used_A (G) - 1 =>
                     Pool (Base (G) + S2 + 1)
                     = Slot_Mono (P, K, J, RJ, N, Q, G, S2)))
   with Ghost => Proof_Only,
        Pre => Ctx and then Bases_Ok (Base)
               and then Used_A'First = 0 and then Used_A'Last = NO
               and then Pool'First = 1 and then Pool'Last = Max_Layer_Slots
               and then N <= SA.Max_Terms + 1;

   procedure Check_Pair
     (Base   : Base_Array;
      Used_A : in out Nat_Array;
      Pool   : in out Mono_Array;
      Tm     : SA.Term;
      N      : Positive;
      Q      : Positive;
      HP     : Long_Long_Integer;
      Ok     : in out Boolean)
   with
     Pre  => Ctx and then Bases_Ok (Base)
             and then Used_A'First = 0 and then Used_A'Last = NO
             and then Pool'First = 1 and then Pool'Last = Max_Layer_Slots
             and then N <= L
             and then Tm = TT (P, J, N) and then Tm.G < NO
             and then Tm.K /= Zero
             and then Q <= Pairs (P, J, RJ, N)
             and then HP = Hint_Pos (P, J, RJ, N - 1)
                           + Long_Long_Integer (Q - 1)
             and then Ok = Pairs_Ok (P, K, J, RJ, N, Q - 1)
             and then (if Ok then State_Ok (Base, Used_A, Pool, N, Q - 1)),
     Post => Used_A'First = 0 and then Used_A'Last = NO
             and then Ok = Pairs_Ok (P, K, J, RJ, N, Q)
             and then (if Ok then State_Ok (Base, Used_A, Pool, N, Q))
   is
      G  : constant Natural := Tm.G;
      Hi : Natural;
      Pm : Monomial;
      U  : Natural;
   begin
      Lemma_Disjoint (Base, Tm.G);
      Lemma_Before (Base, Tm.G);
      Lemma_Used_All (P, K, J, RJ, N, Q, NO);
      Lemma_Slot_Mono_All (P, K, J, RJ, N, Q, NO);
      Lemma_Pairs_Ok_Def (P, K, J, RJ, N, Q);
      if not Ok then
         return;
      end if;
      Lemma_Hint_At (P, K, J, HP);
      Hi := (if HP < Long_Long_Integer (S.Hints)
             then K.Hints (S.First_Hint + Natural (HP) + 1)
             else CC.Max_Count + 1);
      pragma Assert (Hi = H (P, K, J, RJ, N, Q));
      Pm := Pair_Mono (M, Tm, Q);
      --  M and RJ agree field by field on the two wires the term reads.
      pragma Assert
        (Shape_At (M, Tm.H1).N = Shape_At (RJ, Tm.H1).N
         and then Shape_At (M, Tm.H0).N = Shape_At (RJ, Tm.H0).N
         and then (for all E in Entry_Index =>
                     Shape_At (M, Tm.H1).V (E) = Shape_At (RJ, Tm.H1).V (E)
                     and then Shape_At (M, Tm.H0).V (E)
                              = Shape_At (RJ, Tm.H0).V (E)));
      pragma Assert (Pm = Pair_Mono (RJ, Tm, Q));
      U := Used_A (G);
      pragma Assert (U = Used (P, K, J, RJ, N, Q - 1, G));
      if Hi < Count_Of (P, K, J, G) and then Hi <= U then
         if Hi < U then
            pragma Assert
              (Pool (Base (G) + Hi + 1)
               = Slot_Mono (P, K, J, RJ, N, Q - 1, G, Hi));
            Ok := Pool (Base (G) + Hi + 1) = Pm;
            pragma Assert (Ok = Pair_Ok (P, K, J, RJ, N, Q));
         else
            pragma Assert
              (for all S2 in 0 .. U - 1 =>
                 Pool (Base (G) + S2 + 1)
                 = Slot_Mono (P, K, J, RJ, N, Q - 1, G, S2));
            Ok := (for all S2 in 0 .. U - 1 =>
                     Pool (Base (G) + S2 + 1) /= Pm);
            pragma Assert
              (Ok = (for all S2 in 0 .. U - 1 =>
                       Slot_Mono (P, K, J, RJ, N, Q - 1, G, S2) /= Pm));
            pragma Assert (Ok = Pair_Ok (P, K, J, RJ, N, Q));
            if Ok then
               Pool (Base (G) + U + 1) := Pm;
               Used_A (G) := U + 1;
            end if;
         end if;
      else
         Ok := False;
         pragma Assert (not Pair_Ok (P, K, J, RJ, N, Q));
      end if;
   end Check_Pair;

   -------------------------------------------------------------------
   --  The shape of one wire, at the end of the layer
   -------------------------------------------------------------------

   procedure Wire_Shape
     (Base     : Base_Array;
      Pool     : Mono_Array;
      G        : Natural;
      Decl     : Natural;
      Sh       : out Form_Shape;
      Declared : out Boolean)
   with
     Pre  => Ctx and then Bases_Ok (Base) and then G < NO
             and then Pool'First = 1 and then Pool'Last = Max_Layer_Slots
             and then Decl = Declared_Before (P, K, J, RJ, G)
             and then Vb <= Max_Vars and then Decl <= G
             and then (for all S2 in 0 .. Count_Of (P, K, J, G) - 1 =>
                         Pool (Base (G) + S2 + 1)
                         = Mono_End (P, K, J, RJ, G, S2)),
     Post => Sh = Out_Shape (P, K, J, RJ, Vb, G)
             and then Declared = not Linear (P, K, J, RJ, G)
   is
      Cn    : constant Natural := Count_Of (P, K, J, G);
      Lin   : Boolean;
      All_A : Boolean := True;    --  every slot of degree at most 1
      Const : Boolean := False;   --  a slot is the constant
   begin
      Lemma_Disjoint (Base, G);
      for S2 in 0 .. Cn - 1 loop
         All_A := All_A and then Pool (Base (G) + S2 + 1).A = 0;
         Const := Const or else Pool (Base (G) + S2 + 1).B = 0;
         pragma Loop_Invariant
           (All_A = (for all S3 in 0 .. S2 =>
                       Mono_End (P, K, J, RJ, G, S3).A = 0));
         pragma Loop_Invariant
           (Const = (for some S3 in 0 .. S2 =>
                       Mono_End (P, K, J, RJ, G, S3).B = 0));
      end loop;
      Lin := All_A and then Cn <= Max_Form + (if Const then 1 else 0);
      pragma Assert (Lin = Linear (P, K, J, RJ, G));
      Declared := not Lin;
      if Lin then
         pragma Assert (Cn <= Max_Entries);
         Sh := (N => Cn, V => [others => 0]);
         for E2 in 1 .. Cn loop
            Sh.V (E2) := Pool (Base (G) + E2).B;
            pragma Loop_Invariant (Sh.N = Cn);
            pragma Loop_Invariant
              (for all E3 in 1 .. E2 =>
                 Sh.V (E3) = Mono_End (P, K, J, RJ, G, E3 - 1).B);
            pragma Loop_Invariant
              (for all E3 in E2 + 1 .. Max_Entries => Sh.V (E3) = 0);
         end loop;
      else
         Sh := (N => 1, V => [1 => Vb + Decl, others => 0]);
      end if;
   end Wire_Shape;

   --  The shapes of the layer's wires, and its declared wires.
   procedure Build_Next
     (Base : Base_Array;
      Pool : Mono_Array;
      Next : out Shape_Access;
      Decl : out Natural)
   with
     Pre  => Ctx and then Bases_Ok (Base)
             and then Pool'First = 1 and then Pool'Last = Max_Layer_Slots
             and then (for all G in 0 .. NO - 1 =>
                         (for all S2 in 0 .. Count_Of (P, K, J, G) - 1 =>
                            Pool (Base (G) + S2 + 1)
                            = Mono_End (P, K, J, RJ, G, S2))),
     Post => Next /= null and then Next'First = 0
             and then Next'Last = NO - 1
             and then Same_Shapes (Next.all, Out_Shapes (P, K, J, RJ, Vb))
             and then Decl = Declared_Before (P, K, J, RJ, NO)
             and then Decl <= NO
   is
      Sh       : Form_Shape;
      Declared : Boolean;
   begin
      Decl := 0;
      Next := new Shape_Array'(0 .. NO - 1 => No_Shape);
      Lemma_Declared_Def (P, K, J, RJ, 0);
      for G in 0 .. NO - 1 loop
         Wire_Shape (Base, Pool, G, Decl, Sh, Declared);
         Next (G) := Sh;
         Lemma_Declared_Def (P, K, J, RJ, G + 1);
         if Declared then
            Decl := Decl + 1;
         end if;
         pragma Loop_Invariant
           (Next /= null and then Next'First = 0
            and then Next'Last = NO - 1);
         pragma Loop_Invariant
           (Decl = Declared_Before (P, K, J, RJ, G + 1)
            and then Decl <= G + 1);
         pragma Loop_Invariant
           (for all G2 in 0 .. G =>
              Next (G2) = Out_Shape (P, K, J, RJ, Vb, G2));
      end loop;
      pragma Assert (Same_Shapes (Next.all, Out_Shapes (P, K, J, RJ, Vb)));
   end Build_Next;

   Base   : Base_Access;
   Used_A : Nat_Access;
   Terms  : Nat_Access;

   Counts_Ok  : Boolean;
   Fits       : Boolean;
   Pairs_Ok_F : Boolean := True;
   HP     : Long_Long_Integer := 0;
   C      : PC.Cursor := PC.Start (P, J);
   Tm     : SA.Term;
begin
   Next := null;
   Vb_Next := Vb;
   pragma Assert (S = Span (P, K, J));
   if S.Wires /= NO then
      Lemma_Layer_Ok_Def (P, K, J, RJ);
      pragma Assert (not Layer_Ok (P, K, J, RJ));
      St := Cert_Mismatch;
      return;
   end if;
   pragma Assert (NO <= SA.Max_Wires and then NW <= SA.Max_Wires);
   pragma Assert (Ctx);

   Base := new Base_Array'(0 .. NO => 0);
   Compute_Bases (Base.all, Counts_Ok, Fits);
   if not Fits then
      Lemma_Layer_Ok_Def (P, K, J, RJ);
      pragma Assert (not Layer_Ok (P, K, J, RJ));
      Free_Bases (Base);
      St := Pool_Full;
      return;
   end if;

   Used_A := new Nat_Array'(0 .. NO => 0);
   Terms := new Nat_Array'(0 .. NO => 0);
   PC.Lemma_Valid (P);
   --  The terms of the layer name wires in range: the conjunct of
   --  Well_Formed on layer J of the expansion, whose layer table is P's.
   pragma Assert (PC.Expand (P).Layers (J) = P.Layers (J));
   pragma Assert
     (SA.Fits (PC.Expand (P).Terms (P.Layers (J).First .. P.Layers (J).Last),
               NO, NW));
   PC.Lemma_Walked_Start (P, J);
   Lemma_Hint_Pos_Zero (P, J, RJ);
   Lemma_Used_All (P, K, J, RJ, 1, 0, NO);
   Lemma_Slot_Mono_All (P, K, J, RJ, 1, 0, NO);
   pragma Assert (State_Ok (Base.all, Used_A.all, Pool, 1, 0));
   for N in 1 .. L loop
      pragma Loop_Invariant (Proof_Only => PC.Walked (P, J, N - 1, C));
      pragma Loop_Invariant
        (Base /= null and then Used_A /= null and then Terms /= null
         and then Base'First = 0 and then Base'Last = NO
         and then Used_A'First = 0 and then Used_A'Last = NO
         and then Terms'First = 0 and then Terms'Last = NO);
      pragma Loop_Invariant (Bases_Ok (Base.all));
      pragma Loop_Invariant (HP = Hint_Pos (P, J, RJ, N - 1));
      pragma Loop_Invariant
        (for all G in 0 .. NO - 1 =>
           Terms (G) = Wire_Terms (P, J, N - 1, G)
           and then Terms (G) <= N - 1);
      pragma Loop_Invariant
        (Pairs_Ok_F = (N = 1
                       or else Pairs_Ok (P, K, J, RJ, N - 1,
                                         Pairs (P, J, RJ, N - 1))));
      pragma Loop_Invariant
        (if Pairs_Ok_F then State_Ok (Base.all, Used_A.all, Pool, N, 0));
      PC.Lemma_Walked_Step (P, J, N, C);
      Tm := PC.Term_Of (P, C);
      C := PC.Step (P, C);
      pragma Assert (Tm = PC.Expand (P).Terms (P.Layers (J).First + N - 1));
      pragma Assert (Tm = TT (P, J, N));
      pragma Assert
        (Tm.G < NO and then Tm.H0 < NW and then Tm.H1 < NW);
      Lemma_Wire_Terms_All (P, J, N, NO);
      Lemma_Hint_Pos_Step (P, J, RJ, N);
      Lemma_Pairs_Ok_Def (P, K, J, RJ, N, 0);
      if Tm.K /= Zero then
         Terms (Tm.G) := Terms (Tm.G) + 1;
         pragma Assert
           (Shape_At (M, Tm.H1).N * Shape_At (M, Tm.H0).N
            = Pairs (P, J, RJ, N));
         for Q in 1 .. Shape_At (M, Tm.H1).N * Shape_At (M, Tm.H0).N loop
            pragma Loop_Invariant
              (HP = Hint_Pos (P, J, RJ, N - 1) + Long_Long_Integer (Q - 1));
            pragma Loop_Invariant
              (Pairs_Ok_F = Pairs_Ok (P, K, J, RJ, N, Q - 1));
            pragma Loop_Invariant
              (if Pairs_Ok_F then
                 State_Ok (Base.all, Used_A.all, Pool, N, Q - 1));
            pragma Loop_Invariant
              (Bases_Ok (Base.all)
               and then Used_A'First = 0 and then Used_A'Last = NO);
            Check_Pair (Base.all, Used_A.all, Pool, Tm, N, Q, HP,
                        Pairs_Ok_F);
            HP := HP + 1;
         end loop;
      end if;
      --  The state after term N is the model's at (N, Pairs (N)), which
      --  is its state at (N + 1, 0).
      pragma Assert (HP = Hint_Pos (P, J, RJ, N));
      pragma Assert
        (Pairs_Ok_F = Pairs_Ok (P, K, J, RJ, N, Pairs (P, J, RJ, N)));
      pragma Assert
        (if Pairs_Ok_F then
           State_Ok (Base.all, Used_A.all, Pool, N, Pairs (P, J, RJ, N)));
      Lemma_Used_All (P, K, J, RJ, N + 1, 0, NO);
      Lemma_Slot_Mono_All (P, K, J, RJ, N + 1, 0, NO);
      Lemma_Pairs_Ok_Def (P, K, J, RJ, N + 1, 0);
   end loop;

   --  The end of the walk of the layer, in the model's terms.
   pragma Assert (HP = Hint_Pos (P, J, RJ, L));
   pragma Assert
     (for all G in 0 .. NO - 1 => Terms (G) = Wire_Terms (P, J, L, G));
   pragma Assert
     (Pairs_Ok_F
      = (L = 0 or else Pairs_Ok (P, K, J, RJ, L, Pairs (P, J, RJ, L))));
   pragma Assert
     (if Pairs_Ok_F then
        (for all G in 0 .. NO - 1 =>
           Used_A (G) = Used_End (P, K, J, RJ, G)
           and then (for all S2 in 0 .. Used_A (G) - 1 =>
                       Pool (Base (G) + S2 + 1)
                       = Mono_End (P, K, J, RJ, G, S2))));

   declare
      Ok : constant Boolean :=
        Counts_Ok and then Pairs_Ok_F
        and then HP = Long_Long_Integer (S.Hints)
        and then (for all G in 0 .. NO - 1 =>
                    Used_A (G) = Count_Of (P, K, J, G)
                    and then Terms (G) <= Max_Terms_Per_Wire);
      Decl     : Natural := 0;
   begin
      Lemma_Layer_Ok_Def (P, K, J, RJ);
      pragma Assert (Ok = Layer_Ok (P, K, J, RJ));
      if not Ok then
         St := (if not Counts_Ok then Too_Many_Slots
                elsif not Pairs_Ok_F then Bad_Hint
                elsif HP /= Long_Long_Integer (S.Hints) then Hints_Left
                elsif (for some G in 0 .. NO - 1 =>
                         Used_A (G) /= Count_Of (P, K, J, G))
                then Empty_Slot
                else Too_Many_Terms);
      else
         Build_Next (Base.all, Pool, Next, Decl);
         if Vb + Decl > Max_Vars then
            Free_Shapes (Next);
            St := Too_Many_Vars;
         else
            Vb_Next := Vb + Decl;
            St := Accepted;
         end if;
         pragma Assert
           ((St = Accepted)
            = (Layer_Ok (P, K, J, RJ)
               and then Vb + Declared_Before (P, K, J, RJ, NO) <= Max_Vars));
      end if;
   end;
   Free_Bases (Base);
   Free_Nats (Used_A);
   Free_Nats (Terms);
end Check_Layer;
