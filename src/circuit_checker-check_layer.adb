--  Check_Layer: one layer of the walk (ADR 0093). Every check sets a
--  flag rather than leaving: the layer is walked to its end, and once a
--  check has failed the slots are no longer updated. So each flag is,
--  at every step, the conjunction the model states, and the state of
--  the slots is the model's as long as every check before has passed.

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
   E   : constant SA.Circuit := PC.Expand (P) with Ghost => Proof_Only;

   Base   : Nat_Access;       --  0 .. NO: the slots of the wires before
   Used_A : Nat_Access;       --  0 .. NO - 1: each wire's used slots
   Terms  : Nat_Access;       --  0 .. NO - 1: each wire's terms
   Total  : Long_Long_Integer := 0;

   Counts_Ok : Boolean := True;   --  every count at most Max_Slots
   Pairs_Ok_F : Boolean := True;  --  every pair so far passes
   HP     : Long_Long_Integer := 0;   --  the hints used so far
   C      : PC.Cursor := PC.Start (P, J);
   Tm     : SA.Term;
   Cnt    : Natural;
begin
   Next := null;
   Vb_Next := Vb;
   if S.Wires /= NO then
      St := Cert_Mismatch;
      return;
   end if;

   --  The counts and the slot bases.
   Base := new Nat_Array'(0 .. NO => 0);
   for G in 0 .. NO - 1 loop
      Cnt := K.Counts (S.First_Wire + G + 1);
      pragma Assert (Cnt = Count_Of (P, K, J, G));
      Counts_Ok := Counts_Ok and then Cnt <= Max_Slots;
      Lemma_Slot_Base_Def (P, K, J, G + 1);
      Total := Total + Long_Long_Integer (Cnt);
      if Total <= Long_Long_Integer (Max_Layer_Slots) then
         Base (G + 1) := Natural (Total);
      else
         Base (G + 1) := Max_Layer_Slots;
      end if;
      pragma Loop_Invariant (Base /= null and then Base'First = 0
                             and then Base'Last = NO);
      pragma Loop_Invariant (Total = Slot_Base (P, K, J, G + 1));
      pragma Loop_Invariant
        (Counts_Ok = (for all G2 in 0 .. G => Count_Of (P, K, J, G2)
                                              <= Max_Slots));
      pragma Loop_Invariant
        (for all G2 in 0 .. G + 1 => Base (G2) <= Max_Layer_Slots);
      pragma Loop_Invariant
        (if Total <= Long_Long_Integer (Max_Layer_Slots) then
           (for all G2 in 0 .. G + 1 =>
              Long_Long_Integer (Base (G2)) = Slot_Base (P, K, J, G2)));
      pragma Loop_Invariant
        (for all G2 in 0 .. G => Base (G2) <= Base (G2 + 1));
   end loop;
   if Total > Long_Long_Integer (Max_Layer_Slots) then
      Free_Nats (Base);
      St := Pool_Full;
      return;
   end if;
   pragma Assert (Total = Slot_Base (P, K, J, NO));

   Used_A := new Nat_Array'(0 .. NO => 0);
   Terms := new Nat_Array'(0 .. NO => 0);
   PC.Lemma_Valid (P);
   PC.Lemma_Walked_Start (P, J);
   for N in 1 .. L loop
      pragma Loop_Invariant (Proof_Only => PC.Walked (P, J, N - 1, C));
      pragma Loop_Invariant
        (Base /= null and then Used_A /= null and then Terms /= null
         and then Base'First = 0 and then Base'Last = NO
         and then Used_A'First = 0 and then Used_A'Last = NO
         and then Terms'First = 0 and then Terms'Last = NO);
      pragma Loop_Invariant (HP = Hint_Pos (P, J, M, N - 1));
      pragma Loop_Invariant
        (for all G in 0 .. NO - 1 =>
           Terms (G) = Wire_Terms (P, J, N - 1, G));
      pragma Loop_Invariant
        (Pairs_Ok_F = (N = 1
                       or else Pairs_Ok (P, K, J, M, N - 1,
                                         Pairs (P, J, M, N - 1))));
      pragma Loop_Invariant
        (if Pairs_Ok_F then
           (for all G in 0 .. NO - 1 =>
              Used_A (G) = Used (P, K, J, M, N, 0, G)
              and then Used_A (G) <= Count_Of (P, K, J, G)
              and then (for all S2 in 0 .. Used_A (G) - 1 =>
                          Pool (Base (G) + S2 + 1)
                          = Slot_Mono (P, K, J, M, N, 0, G, S2))));
      PC.Lemma_Walked_Step (P, J, N, C);
      Tm := PC.Term_Of (P, C);
      C := PC.Step (P, C);
      Lemma_Wire_Terms_Def (P, J, N, 0);
      if Tm.K /= Zero then
         Terms (Tm.G) := Terms (Tm.G) + 1;
         declare
            A1 : constant Form_Shape := Shape_At (M, Tm.H1);
            A0 : constant Form_Shape := Shape_At (M, Tm.H0);
            NP : constant Natural := A1.N * A0.N;
            G  : constant Natural := Tm.G;
            Hi : Natural;
            Pm : Monomial;
            U  : Natural;
         begin
            for Q in 1 .. NP loop
               if Pairs_Ok_F then
                  Hi := (if HP < Long_Long_Integer (S.Hints)
                         then K.Hints (S.First_Hint + Natural (HP) + 1)
                         else CC.Max_Count + 1);
                  Pm := Pair_Mono (M, Tm, Q);
                  U := Used_A (G);
                  if Hi < Count_Of (P, K, J, G) and then Hi <= U then
                     if Hi < U then
                        Pairs_Ok_F := Pool (Base (G) + Hi + 1) = Pm;
                     else
                        Pairs_Ok_F :=
                          (for all S2 in 0 .. U - 1 =>
                             Pool (Base (G) + S2 + 1) /= Pm);
                        if Pairs_Ok_F then
                           Pool (Base (G) + U + 1) := Pm;
                           Used_A (G) := U + 1;
                        end if;
                     end if;
                  else
                     Pairs_Ok_F := False;
                  end if;
               end if;
               HP := HP + 1;
            end loop;
         end;
      end if;
   end loop;

   --  The end of the layer: the hints all used, every slot reached,
   --  every wire within its terms.
   declare
      Ok : constant Boolean :=
        Counts_Ok and then Pairs_Ok_F
        and then HP = Long_Long_Integer (S.Hints)
        and then (for all G in 0 .. NO - 1 =>
                    Used_A (G) = Count_Of (P, K, J, G)
                    and then Terms (G) <= Max_Terms_Per_Wire);
      Decl : Natural := 0;
      Lin  : Boolean;
      Cn   : Natural;
      Sh   : Form_Shape;
   begin
      if not Ok then
         St := (if not Counts_Ok then Too_Many_Slots
                elsif not Pairs_Ok_F then Bad_Hint
                elsif HP /= Long_Long_Integer (S.Hints) then Hints_Left
                elsif (for some G in 0 .. NO - 1 =>
                         Used_A (G) /= Count_Of (P, K, J, G))
                then Empty_Slot
                else Too_Many_Terms);
      else
         Next := new Shape_Array'(0 .. NO - 1 => No_Shape);
         for G in 0 .. NO - 1 loop
            Cn := Count_Of (P, K, J, G);
            Lin := (for all S2 in 0 .. Cn - 1 => Pool (Base (G) + S2 + 1).A = 0)
              and then Cn <= Max_Form
                  + (if (for some S2 in 0 .. Cn - 1 =>
                           Pool (Base (G) + S2 + 1).B = 0)
                     then 1 else 0);
            if Lin and then Cn <= Max_Entries then
               Sh := (N => Cn, V => [others => 0]);
               for E2 in 1 .. Cn loop
                  Sh.V (E2) := Pool (Base (G) + E2).B;
               end loop;
            else
               Sh := (N => 1, V => [1 => Vb + Decl, others => 0]);
               Decl := Decl + 1;
            end if;
            Next (G) := Sh;
         end loop;
         if Vb + Decl > Max_Vars then
            Free_Shapes (Next);
            St := Too_Many_Vars;
         else
            Vb_Next := Vb + Decl;
            St := Accepted;
         end if;
      end if;
   end;
   Free_Nats (Base);
   Free_Nats (Used_A);
   Free_Nats (Terms);
end Check_Layer;
