--  Lemma_Accepts: the theorem of the walk (ADR 0093). When the walk
--  accepts and the wires satisfy the circuit (the segments of a packed
--  evaluation that returned OK), with input wire 0 equal to one, the
--  values of the home wires satisfy every fact of the model.
--
--  The proof, layer by layer from the inputs (each step a lemma of its
--  own, so that each proof sees only the facts it needs):
--
--  1. One term: the pairs of its expansion, valued at V and summed in
--     the order of the walk, are k * meaning (h1) * meaning (h0)
--     (Lemma_Term).
--  2. One pair: adding it to its slot raises the value of the wire's
--     slots by the pair's value (Lemma_Pair).
--  3. One layer: the evaluation's sum of a wire, Acc_Ref, is the value
--     of its slots at the end of the layer (Lemma_Layer_Sum).
--  4. The meanings of the layer's wires are their values; the facts of
--     the layer hold (Lemma_Layer).
--  5. V is built from the home wires, layer by layer from the inputs,
--     and the layers are taken in turn from the last to layer 0.

separate (Circuit_Checker)
procedure Lemma_Accepts
  (P  : PC.Packed_Circuit;
   K  : CC.Certificate;
   W  : SA.Element_Array;
   Wr : SA.Seg_Array;
   V  : out SA.Element_Array)
is
   use type SA.Element;
   function "+" (A, B : Element) return Element renames SA."+";
   function "*" (A, B : Element) return Element renames SA."*";
   function Same (A, B : Element) return Boolean renames SA.Same;

   -------------------------------------------------------------------
   --  Values
   -------------------------------------------------------------------

   --  The value of a monomial at X.
   function MV (X : SA.Element_Array; Mn : Monomial) return Element is
     (V_At (X, Mn.A) * V_At (X, Mn.B))
   with Ghost => Proof_Only;

   --  The value of a meaning: the shape and coefficients of wire H.
   function Mean
     (R : Shape_Array; CR : Coef_Array; X : SA.Element_Array; H : Natural)
      return Element
   is (Eval_Meaning (Shape_At (R, H), Coefs_At (CR, H), X,
                     Shape_At (R, H).N))
   with Ghost => Proof_Only;

   --  The first Q pairs of a term, valued and summed in the walk's order.
   function Pairs_Sum
     (R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      Tm : SA.Term; Q : Natural) return Element
   is (if Q = 0 then Zero
       else Pairs_Sum (R, CR, X, Tm, Q - 1)
            + Pair_Coef (R, CR, Tm, Q) * MV (X, Pair_Mono (R, Tm, Q)))
   with Ghost => Proof_Only,
        Pre  => Q <= Max_Entries * Max_Entries,
        Subprogram_Variant => (Decreases => Q);

   -------------------------------------------------------------------
   --  1. One term
   -------------------------------------------------------------------

   --  The value of a pair: its coefficient times its monomial is
   --  (k c1 v1) (c0 v0), whatever the order of the monomial.
   procedure Lemma_Pair_Value
     (K1, C1, C0, V1, V0 : Element; Mn : Monomial; X : SA.Element_Array;
      X1, X0 : Natural)
   with Ghost => Proof_Only,
        Pre  => Mn = Mono (X1, X0)
                and then Same (V1, V_At (X, X1))
                and then Same (V0, V_At (X, X0)),
        Post => Same (((K1 * C1) * C0) * MV (X, Mn),
                      (K1 * (C1 * V1)) * (C0 * V0))
   is
   begin
      --  MV is v1 v0 in either order.
      SA.Lemma_Mul_Comm (V_At (X, X1), V_At (X, X0));
      pragma Assert (Same (MV (X, Mn), V1 * V0));
      --  ((k c1) c0) (v1 v0) = (k (c1 v1)) (c0 v0), by the ring laws.
      SA.Lemma_Mul_Assoc (K1 * C1, C0, V1 * V0);
      SA.Lemma_Mul_Assoc (C0, V1, V0);
      SA.Lemma_Mul_Comm (C0, V1);
      SA.Lemma_Mul_Assoc (V1, C0, V0);
      SA.Lemma_Mul_Assoc (K1 * C1, V1, C0 * V0);
      SA.Lemma_Mul_Assoc (K1, C1, V1);
   end Lemma_Pair_Value;

   --  The division that numbers the pairs, by cases on the divisor so
   --  that each case is linear.
   procedure Lemma_Div (I0, N0, C : Natural)
   with Ghost => Proof_Only,
        Pre  => N0 in 1 .. Max_Entries and then C < N0
                and then I0 < Max_Entries,
        Post => (I0 * N0 + C) / N0 = I0 and then (I0 * N0 + C) mod N0 = C
   is
   begin
      case N0 is
         when 1 => null;
         when 2 => null;
         when 3 => null;
         when others => null;
      end case;
   end Lemma_Div;

   --  The pairs of row I (entry I of meaning (h1)), up to column Q0 of
   --  meaning (h0), added to the rows before.
   procedure Lemma_Row
     (R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      Tm : SA.Term; I : Positive; Q0 : Natural)
   with Ghost => Proof_Only,
        Pre  => Tm.K /= Zero
                and then I <= Shape_At (R, Tm.H1).N
                and then Q0 <= Shape_At (R, Tm.H0).N
                and then Shape_At (R, Tm.H0).N >= 1,
        Post => Same
          (Pairs_Sum (R, CR, X, Tm, (I - 1) * Shape_At (R, Tm.H0).N + Q0),
           Pairs_Sum (R, CR, X, Tm, (I - 1) * Shape_At (R, Tm.H0).N)
           + (Tm.K * (Coefs_At (CR, Tm.H1) (I)
                      * V_At (X, Shape_At (R, Tm.H1).V (I))))
             * Eval_Meaning (Shape_At (R, Tm.H0), Coefs_At (CR, Tm.H0), X,
                             Q0)),
        Subprogram_Variant => (Decreases => Q0)
   is
      N0 : constant Positive := Shape_At (R, Tm.H0).N;
      A  : constant Element :=
        Tm.K * (Coefs_At (CR, Tm.H1) (I)
                * V_At (X, Shape_At (R, Tm.H1).V (I)));
      S0 : constant Element := Pairs_Sum (R, CR, X, Tm, (I - 1) * N0);
   begin
      if Q0 = 0 then
         SA.RL.Lemma_Mul_Zero (A);
         SA.Lemma_Add_Zero (S0);
      else
         Lemma_Row (R, CR, X, Tm, I, Q0 - 1);
         declare
            Q  : constant Positive := (I - 1) * N0 + Q0;
            C0 : constant Element := Coefs_At (CR, Tm.H0) (Q0);
            V0 : constant Element := V_At (X, Shape_At (R, Tm.H0).V (Q0));
            E  : constant Element :=
              Eval_Meaning (Shape_At (R, Tm.H0), Coefs_At (CR, Tm.H0), X,
                            Q0 - 1);
         begin
            --  Pair Q takes entry I of meaning (h1) and Q0 of meaning (h0).
            Lemma_Div (I - 1, N0, Q0 - 1);
            pragma Assert
              ((Q - 1) / N0 + 1 = I and then (Q - 1) mod N0 + 1 = Q0);
            pragma Assert
              (Same (Pairs_Sum (R, CR, X, Tm, Q),
                     Pairs_Sum (R, CR, X, Tm, Q - 1)
                     + Pair_Coef (R, CR, Tm, Q)
                       * MV (X, Pair_Mono (R, Tm, Q))));
            pragma Assert
              (Same (Pair_Coef (R, CR, Tm, Q),
                     (Tm.K * Coefs_At (CR, Tm.H1) (I)) * C0));
            pragma Assert
              (Pair_Mono (R, Tm, Q)
               = Mono (Shape_At (R, Tm.H1).V (I),
                       Shape_At (R, Tm.H0).V (Q0)));
            pragma Assert
              (Same (Eval_Meaning (Shape_At (R, Tm.H0), Coefs_At (CR, Tm.H0),
                                   X, Q0),
                     E + C0 * V0));
            Lemma_Pair_Value
              (Tm.K, Coefs_At (CR, Tm.H1) (I), C0,
               V_At (X, Shape_At (R, Tm.H1).V (I)), V0,
               Pair_Mono (R, Tm, Q), X,
               Shape_At (R, Tm.H1).V (I), Shape_At (R, Tm.H0).V (Q0));
            --  A (E + c0 v0) = A E + A (c0 v0).
            SA.Lemma_Mul_Distrib (A, E, C0 * V0);
            SA.Lemma_Add_Assoc (S0, A * E, A * (C0 * V0));
            SA.Lemma_Mul_Assoc (Tm.K, Coefs_At (CR, Tm.H1) (I)
                                      * V_At (X, Shape_At (R, Tm.H1).V (I)),
                                C0 * V0);
         end;
      end if;
   end Lemma_Row;

   --  The whole term: its pairs sum to k * meaning (h1) * meaning (h0).
   procedure Lemma_Term
     (R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      Tm : SA.Term; I : Natural)
   with Ghost => Proof_Only,
        Pre  => Tm.K /= Zero and then I <= Shape_At (R, Tm.H1).N,
        Post => Same
          (Pairs_Sum (R, CR, X, Tm, I * Shape_At (R, Tm.H0).N),
           (Tm.K * Eval_Meaning (Shape_At (R, Tm.H1), Coefs_At (CR, Tm.H1),
                                 X, I))
           * Mean (R, CR, X, Tm.H0)),
        Subprogram_Variant => (Decreases => I)
   is
      N0 : constant Natural := Shape_At (R, Tm.H0).N;
      E0 : constant Element := Mean (R, CR, X, Tm.H0);
   begin
      if I = 0 then
         --  No pair: (k * 0) * e0 = 0.
         SA.RL.Lemma_Mul_Zero (Tm.K);
         SA.Lemma_Mul_Comm (Zero, E0);
         SA.RL.Lemma_Mul_Zero (E0);
      elsif N0 = 0 then
         --  An empty meaning (h0): every row is empty, e0 = 0.
         SA.RL.Lemma_Mul_Zero
           (Tm.K * Eval_Meaning (Shape_At (R, Tm.H1), Coefs_At (CR, Tm.H1),
                                 X, I));
      else
         Lemma_Term (R, CR, X, Tm, I - 1);
         Lemma_Row (R, CR, X, Tm, I, N0);
         declare
            E1 : constant Element :=
              Eval_Meaning (Shape_At (R, Tm.H1), Coefs_At (CR, Tm.H1), X,
                            I - 1);
            T1 : constant Element :=
              Coefs_At (CR, Tm.H1) (I) * V_At (X, Shape_At (R, Tm.H1).V (I));
         begin
            --  (k (e1 + t1)) e0 = (k e1) e0 + (k t1) e0.
            SA.Lemma_Mul_Distrib (Tm.K, E1, T1);
            SA.RL.Lemma_Mul_Distrib_R (Tm.K * E1, Tm.K * T1, E0);
         end;
      end if;
   end Lemma_Term;

   -------------------------------------------------------------------
   --  2. One pair
   -------------------------------------------------------------------

   --  The first S slots of wire G at (N, Q), valued at X and summed.
   function Slots_Sum
     (J : Natural; R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      N : Positive; Q : Natural; G, S : Natural) return Element
   is (if S = 0 then Zero
       else Slots_Sum (J, R, CR, X, N, Q, G, S - 1)
            + Slot_Coef (P, K, J, R, CR, N, Q, G, S - 1)
              * MV (X, Slot_Mono (P, K, J, R, N, Q, G, S - 1)))
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms + 1
                and then S <= CC.Max_Count + 2,
        Subprogram_Variant => (Decreases => S);

   --  One step of Slot_Coef, for every wire and slot.
   procedure Lemma_Slot_Coef_All
     (J : Natural; R : Shape_Array; CR : Coef_Array;
      N : Positive; Q : Natural; NO : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms + 1,
        Post => (for all G in 0 .. NO - 1 =>
                   (for all S in 0 .. CC.Max_Count + 1 =>
                      Same
                        (Slot_Coef (P, K, J, R, CR, N, Q, G, S),
                         (if Q = 0 then
                           (if N = 1 then Zero
                            else Slot_Coef (P, K, J, R, CR, N - 1,
                                            Pairs (P, J, R, N - 1), G, S))
                         elsif G = TT (P, J, N).G
                           and then S = H (P, K, J, R, N, Q)
                         then Slot_Coef (P, K, J, R, CR, N, Q - 1, G, S)
                              + Pair_Coef (R, CR, TT (P, J, N), Q)
                         else Slot_Coef (P, K, J, R, CR, N, Q - 1, G, S)))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Coef);
   begin
      null;
   end Lemma_Slot_Coef_All;

   --  A slot not yet used has no contribution.
   function Fresh
     (J : Natural; R : Shape_Array; CR : Coef_Array;
      N : Positive; Q : Natural; G : Natural) return Boolean
   is (for all S in Used (P, K, J, R, N, Q, G) .. CC.Max_Count + 1 =>
         Same (Slot_Coef (P, K, J, R, CR, N, Q, G, S), Zero))
   with Ghost => Proof_Only,
        Pre => J <= P.Last_Layer and then N <= SA.Max_Terms + 1;

   --  The slots below S change only at the pair's slot H, by C times its
   --  monomial, when H is among them.
   procedure Lemma_Sum_Change
     (J : Natural; R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      N : Positive; Q : Positive; G, S : Natural; NO : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms
                and then G = TT (P, J, N).G and then G < NO
                and then S <= Used (P, K, J, R, N, Q - 1, G)
                and then Used (P, K, J, R, N, Q - 1, G) <= CC.Max_Count
                and then Pair_Ok (P, K, J, R, N, Q),
        Post => Same
          (Slots_Sum (J, R, CR, X, N, Q, G, S),
           Slots_Sum (J, R, CR, X, N, Q - 1, G, S)
           + (if H (P, K, J, R, N, Q) < S
              then Pair_Coef (R, CR, TT (P, J, N), Q)
                   * MV (X, Pair_Mono (R, TT (P, J, N), Q))
              else Zero)),
        Subprogram_Variant => (Decreases => S)
   is
      Hq : constant Natural := H (P, K, J, R, N, Q);
      C  : constant Element := Pair_Coef (R, CR, TT (P, J, N), Q);
      Pm : constant Monomial := Pair_Mono (R, TT (P, J, N), Q);
   begin
      Lemma_Slot_Coef_All (J, R, CR, N, Q, NO);
      Lemma_Slot_Mono_All (P, K, J, R, N, Q, NO);
      Lemma_Used_All (P, K, J, R, N, Q, NO);
      if S = 0 then
         SA.Lemma_Add_Zero (Zero);
      else
         Lemma_Sum_Change (J, R, CR, X, N, Q, G, S - 1, NO);
         declare
            S0 : constant Element :=
              Slots_Sum (J, R, CR, X, N, Q - 1, G, S - 1);
            D  : constant Element :=
              (if Hq < S - 1 then C * MV (X, Pm) else Zero);
            T0 : constant Element :=
              Slot_Coef (P, K, J, R, CR, N, Q - 1, G, S - 1)
              * MV (X, Slot_Mono (P, K, J, R, N, Q - 1, G, S - 1));
         begin
            --  Slot S - 1 keeps its monomial (it is used), and its
            --  coefficient grows by C when it is the pair's.
            pragma Assert
              (Slot_Mono (P, K, J, R, N, Q, G, S - 1)
               = Slot_Mono (P, K, J, R, N, Q - 1, G, S - 1));
            pragma Assert
              (Same (Slots_Sum (J, R, CR, X, N, Q - 1, G, S), S0 + T0));
            pragma Assert
              (Same (Slots_Sum (J, R, CR, X, N, Q, G, S - 1), S0 + D));
            if Hq = S - 1 then
               pragma Assert (Slot_Mono (P, K, J, R, N, Q - 1, G, S - 1) = Pm);
               pragma Assert (Same (D, Zero));
               pragma Assert
                 (Same (Slot_Coef (P, K, J, R, CR, N, Q, G, S - 1),
                        Slot_Coef (P, K, J, R, CR, N, Q - 1, G, S - 1) + C));
               SA.RL.Lemma_Mul_Distrib_R
                 (Slot_Coef (P, K, J, R, CR, N, Q - 1, G, S - 1), C,
                  MV (X, Pm));
               SA.Lemma_Add_Zero (S0);
               SA.Lemma_Add_Assoc (S0, T0, C * MV (X, Pm));
               pragma Assert
                 (Same (Slots_Sum (J, R, CR, X, N, Q, G, S),
                        S0 + (T0 + C * MV (X, Pm))));
            else
               pragma Assert
                 (Same (Slot_Coef (P, K, J, R, CR, N, Q, G, S - 1),
                        Slot_Coef (P, K, J, R, CR, N, Q - 1, G, S - 1)));
               pragma Assert
                 (Same (Slots_Sum (J, R, CR, X, N, Q, G, S), (S0 + D) + T0));
               --  (s0 + d) + t0 = (s0 + t0) + d.
               SA.Lemma_Add_Assoc (S0, D, T0);
               SA.Lemma_Add_Comm (D, T0);
               SA.Lemma_Add_Assoc (S0, T0, D);
            end if;
         end;
      end if;
   end Lemma_Sum_Change;

   --  A wire whose slots the pair does not touch keeps its sum.
   procedure Lemma_Sum_Same
     (J : Natural; R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      N : Positive; Q : Positive; G, S : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms
                and then S <= CC.Max_Count + 1
                and then G < SA.Max_Wires and then G /= TT (P, J, N).G,
        Post => Same (Slots_Sum (J, R, CR, X, N, Q, G, S),
                      Slots_Sum (J, R, CR, X, N, Q - 1, G, S)),
        Subprogram_Variant => (Decreases => S)
   is
   begin
      Lemma_Slot_Coef_All (J, R, CR, N, Q, G + 1);
      Lemma_Slot_Mono_All (P, K, J, R, N, Q, G + 1);
      if S > 0 then
         Lemma_Sum_Same (J, R, CR, X, N, Q, G, S - 1);
      end if;
   end Lemma_Sum_Same;

   --  One pair, accepted: the wire's slots gain its value, the other
   --  wires' are unchanged, the unused slots stay empty, and every count
   --  stays within the certificate's bound.
   procedure Lemma_Pair
     (J : Natural; R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      N : Positive; Q : Positive; NO : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms
                and then NO <= SA.Max_Wires and then TT (P, J, N).G < NO
                and then Pair_Ok (P, K, J, R, N, Q)
                and then (for all G in 0 .. NO - 1 =>
                            Used (P, K, J, R, N, Q - 1, G) <= CC.Max_Count
                            and then Fresh (J, R, CR, N, Q - 1, G)),
        Post => (for all G in 0 .. NO - 1 =>
                   Used (P, K, J, R, N, Q, G) <= CC.Max_Count
                   and then Fresh (J, R, CR, N, Q, G)
                   and then Same
                     (Slots_Sum (J, R, CR, X, N, Q, G,
                                 Used (P, K, J, R, N, Q, G)),
                      Slots_Sum (J, R, CR, X, N, Q - 1, G,
                                 Used (P, K, J, R, N, Q - 1, G))
                      + (if G = TT (P, J, N).G
                         then Pair_Coef (R, CR, TT (P, J, N), Q)
                              * MV (X, Pair_Mono (R, TT (P, J, N), Q))
                         else Zero)))
   is
      G0 : constant Natural := TT (P, J, N).G;
      U  : constant Natural := Used (P, K, J, R, N, Q - 1, G0);
      Hq : constant Natural := H (P, K, J, R, N, Q);
      C  : constant Element := Pair_Coef (R, CR, TT (P, J, N), Q);
   begin
      Lemma_Slot_Coef_All (J, R, CR, N, Q, NO);
      Lemma_Slot_Mono_All (P, K, J, R, N, Q, NO);
      Lemma_Used_All (P, K, J, R, N, Q, NO);
      --  The pair's hint is below the wire's count, at most Max_Count.
      pragma Assert (Hq < Count_Of (P, K, J, G0) and then Hq <= U);
      --  Every wire's unused slots stay empty: the pair writes slot Hq of
      --  G0 only, and Hq is below G0's count after the pair.
      for G in 0 .. NO - 1 loop
         pragma Assert
           (for all S in Used (P, K, J, R, N, Q, G) .. CC.Max_Count + 1 =>
              (G /= G0 or else S /= Hq)
              and then Same (Slot_Coef (P, K, J, R, CR, N, Q, G, S),
                             Slot_Coef (P, K, J, R, CR, N, Q - 1, G, S))
              and then S >= Used (P, K, J, R, N, Q - 1, G));
         pragma Assert (Fresh (J, R, CR, N, Q, G));
         pragma Assert (Used (P, K, J, R, N, Q, G) <= CC.Max_Count);
         if G /= G0 then
            Lemma_Sum_Same (J, R, CR, X, N, Q, G, Used (P, K, J, R, N, Q, G));
            SA.Lemma_Add_Zero
              (Slots_Sum (J, R, CR, X, N, Q - 1, G,
                          Used (P, K, J, R, N, Q - 1, G)));
         end if;
         pragma Loop_Invariant
           (for all G2 in 0 .. G =>
              Used (P, K, J, R, N, Q, G2) <= CC.Max_Count
              and then Fresh (J, R, CR, N, Q, G2)
              and then (G2 = G0
                        or else Same
                          (Slots_Sum (J, R, CR, X, N, Q, G2,
                                      Used (P, K, J, R, N, Q, G2)),
                           Slots_Sum (J, R, CR, X, N, Q - 1, G2,
                                      Used (P, K, J, R, N, Q - 1, G2))
                           + Zero)));
      end loop;
      --  The pair's wire.
      Lemma_Sum_Change (J, R, CR, X, N, Q, G0, U, NO);
      if Hq = U then
         --  A new slot U: it was empty, and now holds C at the pair's
         --  monomial.
         pragma Assert (Same (Slot_Coef (P, K, J, R, CR, N, Q - 1, G0, U),
                              Zero));
         SA.RL.Lemma_Zero_Add (C);
         pragma Assert
           (Same (Slot_Coef (P, K, J, R, CR, N, Q, G0, U), C));
         pragma Assert
           (Slot_Mono (P, K, J, R, N, Q, G0, U)
            = Pair_Mono (R, TT (P, J, N), Q));
         SA.Lemma_Add_Zero (Slots_Sum (J, R, CR, X, N, Q - 1, G0, U));
         pragma Assert
           (Same (Slots_Sum (J, R, CR, X, N, Q, G0, U),
                  Slots_Sum (J, R, CR, X, N, Q - 1, G0, U)));
         pragma Assert
           (Same (Slots_Sum (J, R, CR, X, N, Q, G0, U + 1),
                  Slots_Sum (J, R, CR, X, N, Q - 1, G0, U)
                  + C * MV (X, Pair_Mono (R, TT (P, J, N), Q))));
      else
         pragma Assert (Used (P, K, J, R, N, Q, G0) = U);
      end if;
   end Lemma_Pair;

   -------------------------------------------------------------------
   --  3. One layer
   -------------------------------------------------------------------

   --  The pairs of term N, one at a time: the wire's slots gain the
   --  first Q pairs' values.
   procedure Lemma_Term_Slots
     (J : Natural; R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      N : Positive; Q : Natural; NO : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms
                and then NO <= SA.Max_Wires and then TT (P, J, N).G < NO
                and then Q <= Pairs (P, J, R, N)
                and then Pairs_Ok (P, K, J, R, N, Q)
                and then (for all G in 0 .. NO - 1 =>
                            Used (P, K, J, R, N, 0, G) <= CC.Max_Count
                            and then Fresh (J, R, CR, N, 0, G)),
        Post => (for all G in 0 .. NO - 1 =>
                   Used (P, K, J, R, N, Q, G) <= CC.Max_Count
                   and then Fresh (J, R, CR, N, Q, G)
                   and then Same
                     (Slots_Sum (J, R, CR, X, N, Q, G,
                                 Used (P, K, J, R, N, Q, G)),
                      Slots_Sum (J, R, CR, X, N, 0, G,
                                 Used (P, K, J, R, N, 0, G))
                      + (if G = TT (P, J, N).G
                         then Pairs_Sum (R, CR, X, TT (P, J, N), Q)
                         else Zero))),
        Subprogram_Variant => (Decreases => Q)
   is
      --  The step for one wire, from the facts at Q - 1 and the pair's.
      procedure Step_G (G : Natural)
      with Ghost => Proof_Only,
           Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms
                   and then Q >= 1 and then Q <= Pairs (P, J, R, N)
                   and then G < NO
                   and then Same
                     (Slots_Sum (J, R, CR, X, N, Q - 1, G,
                                 Used (P, K, J, R, N, Q - 1, G)),
                      Slots_Sum (J, R, CR, X, N, 0, G,
                                 Used (P, K, J, R, N, 0, G))
                      + (if G = TT (P, J, N).G
                         then Pairs_Sum (R, CR, X, TT (P, J, N), Q - 1)
                         else Zero))
                   and then Same
                     (Slots_Sum (J, R, CR, X, N, Q, G,
                                 Used (P, K, J, R, N, Q, G)),
                      Slots_Sum (J, R, CR, X, N, Q - 1, G,
                                 Used (P, K, J, R, N, Q - 1, G))
                      + (if G = TT (P, J, N).G
                         then Pair_Coef (R, CR, TT (P, J, N), Q)
                              * MV (X, Pair_Mono (R, TT (P, J, N), Q))
                         else Zero)),
           Post => Same
                     (Slots_Sum (J, R, CR, X, N, Q, G,
                                 Used (P, K, J, R, N, Q, G)),
                      Slots_Sum (J, R, CR, X, N, 0, G,
                                 Used (P, K, J, R, N, 0, G))
                      + (if G = TT (P, J, N).G
                         then Pairs_Sum (R, CR, X, TT (P, J, N), Q)
                         else Zero))
      is
         A0 : constant Element :=
           Slots_Sum (J, R, CR, X, N, 0, G, Used (P, K, J, R, N, 0, G));
         B  : constant Element :=
           (if G = TT (P, J, N).G
            then Pairs_Sum (R, CR, X, TT (P, J, N), Q - 1) else Zero);
         C  : constant Element :=
           (if G = TT (P, J, N).G
            then Pair_Coef (R, CR, TT (P, J, N), Q)
                 * MV (X, Pair_Mono (R, TT (P, J, N), Q))
            else Zero);
      begin
         --  (a + b) + c = a + (b + c), and b + c is the first Q pairs
         --  (or 0 + 0 for another wire).
         SA.Lemma_Add_Assoc (A0, B, C);
         SA.Lemma_Add_Zero (Zero);
      end Step_G;
   begin
      if Q = 0 then
         for G in 0 .. NO - 1 loop
            SA.Lemma_Add_Zero
              (Slots_Sum (J, R, CR, X, N, 0, G, Used (P, K, J, R, N, 0, G)));
            pragma Loop_Invariant
              (for all G2 in 0 .. G =>
                 Same
                   (Slots_Sum (J, R, CR, X, N, 0, G2,
                               Used (P, K, J, R, N, 0, G2)),
                    Slots_Sum (J, R, CR, X, N, 0, G2,
                               Used (P, K, J, R, N, 0, G2))
                    + (if G2 = TT (P, J, N).G
                       then Pairs_Sum (R, CR, X, TT (P, J, N), 0)
                       else Zero)));
         end loop;
      else
         Lemma_Pairs_Ok_Def (P, K, J, R, N, Q);
         Lemma_Term_Slots (J, R, CR, X, N, Q - 1, NO);
         Lemma_Pair (J, R, CR, X, N, Q, NO);
         for G in 0 .. NO - 1 loop
            Step_G (G);
            pragma Loop_Invariant
              (for all G2 in 0 .. G =>
                 Same
                   (Slots_Sum (J, R, CR, X, N, Q, G2,
                               Used (P, K, J, R, N, Q, G2)),
                    Slots_Sum (J, R, CR, X, N, 0, G2,
                               Used (P, K, J, R, N, 0, G2))
                    + (if G2 = TT (P, J, N).G
                       then Pairs_Sum (R, CR, X, TT (P, J, N), Q)
                       else Zero)));
         end loop;
      end if;
   end Lemma_Term_Slots;

   --  The state at (N + 1, 0) is the state after term N: the same sums.
   procedure Lemma_Sum_Next
     (J : Natural; R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      N : Positive; G, S : Natural; NO : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms
                and then G < NO and then S <= CC.Max_Count + 1,
        Post => Same (Slots_Sum (J, R, CR, X, N + 1, 0, G, S),
                      Slots_Sum (J, R, CR, X, N, Pairs (P, J, R, N), G, S)),
        Subprogram_Variant => (Decreases => S)
   is
   begin
      Lemma_Slot_Coef_All (J, R, CR, N + 1, 0, NO);
      Lemma_Slot_Mono_All (P, K, J, R, N + 1, 0, NO);
      if S > 0 then
         Lemma_Sum_Next (J, R, CR, X, N, G, S - 1, NO);
      end if;
   end Lemma_Sum_Next;

   --  The end state's sum is Eval_Slots.
   procedure Lemma_Sum_End
     (J : Natural; R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      G, S : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then Len (P, J) >= 1
                and then Len (P, J) <= SA.Max_Terms
                and then S <= CC.Max_Count,
        Post => Same
          (Slots_Sum (J, R, CR, X, Len (P, J),
                      Pairs (P, J, R, Len (P, J)), G, S),
           Eval_Slots (P, K, J, R, CR, X, G, S)),
        Subprogram_Variant => (Decreases => S)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Eval_Slots);
   begin
      if S > 0 then
         Lemma_Sum_End (J, R, CR, X, G, S - 1);
      end if;
   end Lemma_Sum_End;

   --  A layer whose last pair passes passes at every earlier term.
   procedure Lemma_Prefix
     (J : Natural; R : Shape_Array; N : Positive)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms
                and then N <= Len (P, J)
                and then Pairs_Ok (P, K, J, R, Len (P, J),
                                   Pairs (P, J, R, Len (P, J))),
        Post => Pairs_Ok (P, K, J, R, N, Pairs (P, J, R, N))
   is
   begin
      for N2 in reverse N + 1 .. Len (P, J) loop
         pragma Loop_Invariant
           (Pairs_Ok (P, K, J, R, N2, Pairs (P, J, R, N2)));
         for Q in reverse 1 .. Pairs (P, J, R, N2) loop
            pragma Loop_Invariant (Pairs_Ok (P, K, J, R, N2, Q));
            Lemma_Pairs_Ok_Def (P, K, J, R, N2, Q);
         end loop;
         Lemma_Pairs_Ok_Def (P, K, J, R, N2, 0);
      end loop;
   end Lemma_Prefix;

   --  The unused slots after term N are those at (N + 1, 0).
   procedure Lemma_Fresh_Next
     (J : Natural; R : Shape_Array; CR : Coef_Array; N : Positive;
      G : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms
                and then G < SA.Max_Wires
                and then Fresh (J, R, CR, N, Pairs (P, J, R, N), G),
        Post => Fresh (J, R, CR, N + 1, 0, G)
                and then Used (P, K, J, R, N + 1, 0, G)
                         = Used (P, K, J, R, N, Pairs (P, J, R, N), G)
   is
   begin
      Lemma_Slot_Coef_All (J, R, CR, N + 1, 0, G + 1);
      Lemma_Used_All (P, K, J, R, N + 1, 0, G + 1);
   end Lemma_Fresh_Next;

   --  The inputs of layer J have their meanings at X.
   function In_Mean
     (R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      Win : SA.Element_Array; NW : Natural) return Boolean
   is (for all H in 0 .. NW - 1 =>
         Same (SA.W_At (Win, H), Mean (R, CR, X, H)))
   with Ghost => Proof_Only, Pre => Win'First = 0;

   --  One layer: the evaluation's sum of each wire, Acc_Ref, is the value
   --  of its slots at the end of the walk of the layer.
   procedure Lemma_Layer_Sum
     (J : Natural; R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      Win : SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer
                and then PC.Valid (P) and then SA.Well_Formed (PC.Expand (P))
                and then Len (P, J) <= SA.Max_Terms
                and then Win'First = 0
                and then Win'Length <= Natural'Last - SA.Max_Wires
                and then In_Mean (R, CR, X, Win, P.Layers (J).NW_In)
                and then Layer_Ok (P, K, J, R),
        Post => (for all G in 0 .. Out_Count (P, J) - 1 =>
                   Same (SA.Acc_Ref (Win, 0,
                                     SA.Layer_Terms (PC.Expand (P), J),
                                     Len (P, J), G),
                         Eval_Slots (P, K, J, R, CR, X, G,
                                     Count_Of (P, K, J, G))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", SA.Acc_Ref);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Eval_Slots);
      E  : constant SA.Circuit := PC.Expand (P);
      T  : constant SA.Term_Array := SA.Layer_Terms (E, J);
      NO : constant Natural := Out_Count (P, J);
      L  : constant Natural := Len (P, J);
      NW : constant Natural := P.Layers (J).NW_In;
   begin
      Lemma_Layer_Ok_Def (P, K, J, R);
      PC.Lemma_Valid (P);
      pragma Assert (E.Layers (J) = P.Layers (J));
      pragma Assert (T'First = P.Layers (J).First and then T'Length = L);
      pragma Assert (SA.Fits (T, NO, NW));
      Lemma_Used_All (P, K, J, R, 1, 0, NO);
      Lemma_Slot_Coef_All (J, R, CR, 1, 0, NO);
      for N in 1 .. L loop
         pragma Loop_Invariant
           (for all G in 0 .. NO - 1 =>
              Used (P, K, J, R, N, 0, G) <= CC.Max_Count
              and then Fresh (J, R, CR, N, 0, G)
              and then Same (SA.Acc_Ref (Win, 0, T, N - 1, G),
                             Slots_Sum (J, R, CR, X, N, 0, G,
                                        Used (P, K, J, R, N, 0, G))));
         declare
            Tm : constant SA.Term := TT (P, J, N);
         begin
            pragma Assert (T (T'First + N - 1) = Tm);
            pragma Assert (Same (T (T'First + N - 1).K, Tm.K));
            pragma Assert (Tm.G < NO and then Tm.H0 < NW and then Tm.H1 < NW);
            Lemma_Prefix (J, R, N);
            Lemma_Pairs_Ok_Def (P, K, J, R, N, 0);
            Lemma_Term_Slots (J, R, CR, X, N, Pairs (P, J, R, N), NO);
            if Tm.K /= Zero then
               Lemma_Term (R, CR, X, Tm, Shape_At (R, Tm.H1).N);
               pragma Assert
                 (Same (SA.W_At (Win, Tm.H1), Mean (R, CR, X, Tm.H1))
                  and then Same (SA.W_At (Win, Tm.H0),
                                 Mean (R, CR, X, Tm.H0)));
            end if;
            Lemma_Used_All (P, K, J, R, N + 1, 0, NO);
            Lemma_Slot_Coef_All (J, R, CR, N + 1, 0, NO);
            Lemma_Slot_Mono_All (P, K, J, R, N + 1, 0, NO);
            for G in 0 .. NO - 1 loop
               Lemma_Fresh_Next (J, R, CR, N, G);
               Lemma_Sum_Next
                 (J, R, CR, X, N, G, Used (P, K, J, R, N + 1, 0, G), NO);
               pragma Assert
                 (Same (Slots_Sum (J, R, CR, X, N + 1, 0, G,
                                   Used (P, K, J, R, N + 1, 0, G)),
                        Slots_Sum (J, R, CR, X, N, Pairs (P, J, R, N), G,
                                   Used (P, K, J, R, N, Pairs (P, J, R, N),
                                         G))));
               if Tm.K /= Zero and then G = Tm.G then
                  pragma Assert
                    (Same (SA.Acc_Ref (Win, 0, T, N, G),
                           SA.Acc_Ref (Win, 0, T, N - 1, G)
                           + (Tm.K * SA.W_At (Win, Tm.H1))
                             * SA.W_At (Win, Tm.H0)));
                  pragma Assert
                    (Same ((Tm.K * SA.W_At (Win, Tm.H1))
                           * SA.W_At (Win, Tm.H0),
                           Pairs_Sum (R, CR, X, Tm, Pairs (P, J, R, N))));
               else
                  pragma Assert
                    (Same (SA.Acc_Ref (Win, 0, T, N, G),
                           SA.Acc_Ref (Win, 0, T, N - 1, G)));
                  SA.Lemma_Add_Zero
                    (Slots_Sum (J, R, CR, X, N, 0, G,
                                Used (P, K, J, R, N, 0, G)));
               end if;
               pragma Loop_Invariant
                 (for all G2 in 0 .. G =>
                    Used (P, K, J, R, N + 1, 0, G2) <= CC.Max_Count
                    and then Fresh (J, R, CR, N + 1, 0, G2)
                    and then
                    Same (SA.Acc_Ref (Win, 0, T, N, G2),
                          Slots_Sum (J, R, CR, X, N + 1, 0, G2,
                                     Used (P, K, J, R, N + 1, 0, G2))));
            end loop;
         end;
      end loop;
      --  The end: the state after the last term, with every slot the
      --  certificate counts used.
      if L >= 1 then
         for G in 0 .. NO - 1 loop
            Lemma_Sum_Next
              (J, R, CR, X, L, G, Used (P, K, J, R, L + 1, 0, G), NO);
            Lemma_Sum_End (J, R, CR, X, G, Count_Of (P, K, J, G));
            pragma Loop_Invariant
              (for all G2 in 0 .. G =>
                 Same (SA.Acc_Ref (Win, 0, T, L, G2),
                       Eval_Slots (P, K, J, R, CR, X, G2,
                                   Count_Of (P, K, J, G2))));
         end loop;
      end if;
   end Lemma_Layer_Sum;

   -------------------------------------------------------------------
   --  4. The meanings and the facts of one layer
   -------------------------------------------------------------------

   --  A linear wire's meaning, entry by entry, is its slots' value when
   --  variable 0 is one.
   procedure Lemma_Linear_Eval
     (J : Natural; R : Shape_Array; CR : Coef_Array; X : SA.Element_Array;
      Vb : Natural; G : Natural; S : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms
                and then Vb <= Max_Vars and then G < Out_Count (P, J)
                and then Linear (P, K, J, R, G)
                and then Count_Of (P, K, J, G) <= Max_Entries
                and then S <= Count_Of (P, K, J, G)
                and then Same (V_At (X, 0), SA.One),
        Post => Same
          (Eval_Meaning (Out_Shape (P, K, J, R, Vb, G),
                         Coefs_At (Out_Coefs (P, K, J, R, CR), G), X, S),
           Eval_Slots (P, K, J, R, CR, X, G, S)),
        Subprogram_Variant => (Decreases => S)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Eval_Slots);
   begin
      if S > 0 then
         Lemma_Linear_Eval (J, R, CR, X, Vb, G, S - 1);
         declare
            Mn : constant Monomial := Mono_End (P, K, J, R, G, S - 1);
            Cf : constant Element := Coef_End (P, K, J, R, CR, G, S - 1);
         begin
            --  The slot is (0, B): v0 vB = 1 vB = vB.
            pragma Assert (Mn.A = 0);
            pragma Assert (Out_Shape (P, K, J, R, Vb, G).V (S) = Mn.B);
            pragma Assert
              (Same (Coefs_At (Out_Coefs (P, K, J, R, CR), G) (S), Cf));
            SA.RL.Lemma_One_Mul (V_At (X, Mn.B));
            pragma Assert (Same (MV (X, Mn), V_At (X, Mn.B)));
         end;
      end if;
   end Lemma_Linear_Eval;

   --  Every assertion of the layer, from Z_Ref: its two wires' product
   --  is zero.
   procedure Lemma_Z_All
     (Win : SA.Element_Array; T : SA.Term_Array; L : Natural)
   with Ghost => Proof_Only,
        Pre  => Win'First = 0 and then L <= T'Length
                and then SA.Z_Ref (Win, 0, T, L),
        Post => (for all N in 1 .. L =>
                   (if T (T'First + N - 1).K = Zero then
                      SA.W_At (Win, T (T'First + N - 1).H1)
                      * SA.W_At (Win, T (T'First + N - 1).H0) = Zero))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", SA.Z_Ref);
   begin
      for N in reverse 1 .. L loop
         pragma Loop_Invariant
           (SA.Z_Ref (Win, 0, T, N)
            and then (for all N2 in N + 1 .. L =>
                        (if T (T'First + N2 - 1).K = Zero then
                           SA.W_At (Win, T (T'First + N2 - 1).H1)
                           * SA.W_At (Win, T (T'First + N2 - 1).H0)
                           = Zero)));
      end loop;
   end Lemma_Z_All;

   --  The wires of layer J that are declared hold, in X, the values of
   --  their home wires.
   function Homes_Layer (J : Natural; X : SA.Element_Array) return Boolean
   is (for all G in 0 .. Out_Count (P, J) - 1 =>
         (if not Linear (P, K, J, Reads (P, K, J), G) then
            Same (V_At (X, First_Var (P, K, J)
                           + Declared_Before (P, K, J, Reads (P, K, J), G)),
                  SA.W_At (Wr (J).all, G))))
   with Ghost => Proof_Only,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => J <= P.Last_Layer and then Wr'First = 0
               and then Wr'Last = P.Last_Layer + 1
               and then Wr (J) /= null and then Wr (J)'First = 0;

   --  One wire: its value is its meaning. A linear wire's meaning is
   --  its slots; a declared wire's is its variable, which holds the
   --  wire's value. A declared wire's fact follows.
   procedure Lemma_Wire (J : Natural; X : SA.Element_Array; G : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms
                and then Out_Count (P, J) <= SA.Max_Wires
                and then G < Out_Count (P, J)
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then Wr (J) /= null and then Wr (J)'First = 0
                and then Same (V_At (X, 0), SA.One)
                and then Same (SA.W_At (Wr (J).all, G),
                               Eval_Slots (P, K, J, Reads (P, K, J),
                                           Read_Coefs (P, K, J), X, G,
                                           Count_Of (P, K, J, G)))
                and then (if not Linear (P, K, J, Reads (P, K, J), G) then
                            Same (V_At (X, First_Var (P, K, J)
                                           + Declared_Before
                                               (P, K, J, Reads (P, K, J), G)),
                                  SA.W_At (Wr (J).all, G))),
        Post => Same (SA.W_At (Wr (J).all, G),
                      Mean (Out_Shapes (P, K, J, Reads (P, K, J),
                                        First_Var (P, K, J)),
                            Out_Coefs (P, K, J, Reads (P, K, J),
                                       Read_Coefs (P, K, J)),
                            X, G))
                and then
                (if not Linear (P, K, J, Reads (P, K, J), G) then
                   Same (V_At (X, First_Var (P, K, J)
                                  + Declared_Before
                                      (P, K, J, Reads (P, K, J), G)),
                         Eval_Slots (P, K, J, Reads (P, K, J),
                                     Read_Coefs (P, K, J), X, G,
                                     Count_Of (P, K, J, G))))
   is
      R  : constant Shape_Array := Reads (P, K, J);
      CR : constant Coef_Array := Read_Coefs (P, K, J);
      FV : constant Natural := First_Var (P, K, J);
      C  : constant Natural := Count_Of (P, K, J, G);
   begin
      pragma Assert
        (Shape_At (Out_Shapes (P, K, J, R, FV), G).N
         = Out_Shape (P, K, J, R, FV, G).N);
      pragma Assert
        (for all E in Entry_Index =>
           Shape_At (Out_Shapes (P, K, J, R, FV), G).V (E)
           = Out_Shape (P, K, J, R, FV, G).V (E));
      if Linear (P, K, J, R, G) then
         pragma Assert (C <= Max_Entries);
         pragma Assert (Out_Shape (P, K, J, R, FV, G).N = C);
         Lemma_Linear_Eval (J, R, CR, X, FV, G, C);
      else
         pragma Assert (Out_Shape (P, K, J, R, FV, G).N = 1);
         pragma Assert
           (Out_Shape (P, K, J, R, FV, G).V (1)
            = FV + Declared_Before (P, K, J, R, G));
         pragma Assert
           (Same (Coefs_At (Out_Coefs (P, K, J, R, CR), G) (1), SA.One));
         SA.RL.Lemma_One_Mul (V_At (X, FV + Declared_Before (P, K, J, R, G)));
         SA.RL.Lemma_Zero_Add
           (SA.One * V_At (X, FV + Declared_Before (P, K, J, R, G)));
      end if;
   end Lemma_Wire;

   --  The assertions of layer J, from the values of the wires: when the
   --  product of an assertion's two wires is zero and the wires have
   --  their meanings, the product of the meanings is zero.
   procedure Lemma_Asserts_Of
     (J : Natural; X : SA.Element_Array; Win : SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer
                and then Win'First = 0
                and then (for all N in 1 .. Len (P, J) =>
                            TT (P, J, N).H0 < P.Layers (J).NW_In
                            and then TT (P, J, N).H1 < P.Layers (J).NW_In)
                and then In_Mean (Reads (P, K, J), Read_Coefs (P, K, J), X,
                                  Win, P.Layers (J).NW_In)
                and then (for all N in 1 .. Len (P, J) =>
                            (if TT (P, J, N).K = Zero then
                               SA.W_At (Win, TT (P, J, N).H1)
                               * SA.W_At (Win, TT (P, J, N).H0) = Zero)),
        Post => Asserts_Hold (P, K, J, X)
   is
   begin
      for N in 1 .. Len (P, J) loop
         pragma Loop_Invariant
           (for all N2 in 1 .. N =>
              (if TT (P, J, N2).K = Zero then
                 SA."*" (Eval_Meaning (Shape_At (Reads (P, K, J),
                                                 TT (P, J, N2).H1),
                                       Coefs_At (Read_Coefs (P, K, J),
                                                 TT (P, J, N2).H1),
                                       X,
                                       Shape_At (Reads (P, K, J),
                                                 TT (P, J, N2).H1).N),
                         Eval_Meaning (Shape_At (Reads (P, K, J),
                                                 TT (P, J, N2).H0),
                                       Coefs_At (Read_Coefs (P, K, J),
                                                 TT (P, J, N2).H0),
                                       X,
                                       Shape_At (Reads (P, K, J),
                                                 TT (P, J, N2).H0).N))
                 = Zero));
      end loop;
   end Lemma_Asserts_Of;

   --  The assertions of layer J: the product of each one's two wires is
   --  zero (Z_Ref), and the wires have their meanings.
   procedure Lemma_Asserts (J : Natural; X : SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer
                and then PC.Valid (P) and then SA.Well_Formed (PC.Expand (P))
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then Wr (J + 1) /= null and then Wr (J + 1)'First = 0
                and then Wr (J + 1)'Length = P.Layers (J).NW_In
                and then In_Mean (Reads (P, K, J), Read_Coefs (P, K, J), X,
                                  Wr (J + 1).all, P.Layers (J).NW_In)
                and then SA.Layer_Z_Seg (PC.Expand (P), Wr (J + 1).all, J),
        Post => Asserts_Hold (P, K, J, X)
   is
      --  The facts of Z_Ref and of the circuit's shape, with the terms
      --  named as the model names them.
      procedure Z_Facts
      with Ghost => Proof_Only,
           Pre  => J <= P.Last_Layer
                   and then PC.Valid (P)
                   and then SA.Well_Formed (PC.Expand (P))
                   and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                   and then Wr (J + 1) /= null and then Wr (J + 1)'First = 0
                   and then SA.Layer_Z_Seg (PC.Expand (P), Wr (J + 1).all, J),
           Post => (for all N in 1 .. Len (P, J) =>
                      TT (P, J, N).H0 < P.Layers (J).NW_In
                      and then TT (P, J, N).H1 < P.Layers (J).NW_In
                      and then
                      (if TT (P, J, N).K = Zero then
                         SA.W_At (Wr (J + 1).all, TT (P, J, N).H1)
                         * SA.W_At (Wr (J + 1).all, TT (P, J, N).H0) = Zero))
      is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", SA.Layer_Z_Seg);
         E  : constant SA.Circuit := PC.Expand (P);
         T  : constant SA.Term_Array := SA.Layer_Terms (E, J);
         L  : constant Natural := Len (P, J);
         NW : constant Natural := P.Layers (J).NW_In;
      begin
         PC.Lemma_Valid (P);
         pragma Assert (E.Layers (J) = P.Layers (J));
         pragma Assert (T'First = P.Layers (J).First and then T'Length = L);
         pragma Assert (SA.Fits (T, Out_Count (P, J), NW));
         Lemma_Z_All (Wr (J + 1).all, T, L);
         for N in 1 .. L loop
            pragma Assert (T (T'First + N - 1) = TT (P, J, N));
            pragma Assert (Same (T (T'First + N - 1).K, TT (P, J, N).K));
            pragma Loop_Invariant
              (for all N2 in 1 .. N =>
                 TT (P, J, N2).H0 < NW and then TT (P, J, N2).H1 < NW
                 and then
                 (if TT (P, J, N2).K = Zero then
                    SA.W_At (Wr (J + 1).all, TT (P, J, N2).H1)
                    * SA.W_At (Wr (J + 1).all, TT (P, J, N2).H0) = Zero));
         end loop;
      end Z_Facts;
   begin
      Z_Facts;
      Lemma_Asserts_Of (J, X, Wr (J + 1).all);
   end Lemma_Asserts;

   --  One output of layer 0: its value is zero and its meaning, so its
   --  meaning is zero.
   procedure Lemma_Output (X : SA.Element_Array; G : Natural)
   with Ghost => Proof_Only,
        Pre  => Len (P, 0) <= SA.Max_Terms
                and then Out_Count (P, 0) <= SA.Max_Wires
                and then G < Out_Count (P, 0)
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then Wr (0) /= null
                and then Wr (0)'First = 0
                and then SA.F."=" (SA.W_At (Wr (0).all, G), Zero)
                and then Same (SA.W_At (Wr (0).all, G),
                               Mean (Out_Shapes (P, K, 0, Reads (P, K, 0),
                                                 First_Var (P, K, 0)),
                                     Out_Coefs (P, K, 0, Reads (P, K, 0),
                                                Read_Coefs (P, K, 0)),
                                     X, G)),
        Post => Eval_Meaning
                  (Out_Shape (P, K, 0, Reads (P, K, 0), First_Var (P, K, 0), G),
                   Coefs_At (Out_Coefs (P, K, 0, Reads (P, K, 0),
                                        Read_Coefs (P, K, 0)), G),
                   X, Out_Shape (P, K, 0, Reads (P, K, 0),
                                 First_Var (P, K, 0), G).N)
                = Zero
   is
   begin
      null;
   end Lemma_Output;

   --  One layer: its wires' values are their meanings, and its facts
   --  hold.
   procedure Lemma_Layer (J : Natural; X : SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer
                and then PC.Valid (P) and then SA.Well_Formed (PC.Expand (P))
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then (for all L in Wr'Range =>
                            Wr (L) /= null and then Wr (L)'First = 0)
                and then Wr (J)'Length = Out_Count (P, J)
                and then Wr (J + 1)'Length = P.Layers (J).NW_In
                and then Wr (J + 1)'Length <= Natural'Last - SA.Max_Wires
                and then Layer_Accepted (P, K, J)
                and then Same (V_At (X, 0), SA.One)
                and then In_Mean (Reads (P, K, J), Read_Coefs (P, K, J), X,
                                  Wr (J + 1).all, P.Layers (J).NW_In)
                and then SA.Layer_Holds_Seg (PC.Expand (P), Wr (J).all,
                                             Wr (J + 1).all, J)
                and then SA.Layer_Z_Seg (PC.Expand (P), Wr (J + 1).all, J)
                and then Homes_Layer (J, X)
                and then (if J = 0 then
                            (for all G in 0 .. P.Noutput - 1 =>
                               SA.F."=" (Wr (0) (G), Zero))),
        Post => (for all G in 0 .. Out_Count (P, J) - 1 =>
                   Same (SA.W_At (Wr (J).all, G),
                         Mean (Out_Shapes (P, K, J, Reads (P, K, J),
                                           First_Var (P, K, J)),
                               Out_Coefs (P, K, J, Reads (P, K, J),
                                          Read_Coefs (P, K, J)),
                               X, G)))
                and then Layer_Facts (P, K, J, X)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         SA.Layer_Holds_Seg);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Homes_Layer);
      R   : constant Shape_Array := Reads (P, K, J);
      CR  : constant Coef_Array := Read_Coefs (P, K, J);
      FV  : constant Natural := First_Var (P, K, J);
      E   : constant SA.Circuit := PC.Expand (P);
      NO  : constant Natural := Out_Count (P, J);
   begin
      Lemma_Layer_Accepted_Def (P, K, J);
      Lemma_Layer_Ok_Def (P, K, J, R);
      PC.Lemma_Valid (P);
      pragma Assert (E.Layers (J) = P.Layers (J));
      Lemma_Layer_Sum (J, R, CR, X, Wr (J + 1).all);
      --  The wires.
      for G in 0 .. NO - 1 loop
         Lemma_Wire (J, X, G);
         pragma Loop_Invariant
           (for all G2 in 0 .. G =>
              Same (SA.W_At (Wr (J).all, G2),
                    Mean (Out_Shapes (P, K, J, R, FV),
                          Out_Coefs (P, K, J, R, CR), X, G2))
              and then
              (if not Linear (P, K, J, R, G2) then
                 Same (V_At (X, FV + Declared_Before (P, K, J, R, G2)),
                       Eval_Slots (P, K, J, R, CR, X, G2,
                                   Count_Of (P, K, J, G2)))));
      end loop;
      pragma Assert (Declared_Hold (P, K, J, X));
      --  The assertions.
      Lemma_Asserts (J, X);
      --  The outputs, on layer 0.
      if J = 0 then
         for G in 0 .. NO - 1 loop
            pragma Assert (SA.F."=" (SA.W_At (Wr (J).all, G), Zero));
            Lemma_Output (X, G);
            pragma Loop_Invariant
              (for all G2 in 0 .. G =>
                 Eval_Meaning
                   (Out_Shape (P, K, J, R, FV, G2),
                    Coefs_At (Out_Coefs (P, K, J, R, CR), G2),
                    X, Out_Shape (P, K, J, R, FV, G2).N)
                 = Zero);
         end loop;
      end if;
      pragma Assert (Outputs_Zero (P, K, J, X));
      Lemma_Layer_Facts_Def (P, K, J, X);
   end Lemma_Layer;

   -------------------------------------------------------------------
   --  5. The values of the variables, and the layers in turn
   -------------------------------------------------------------------

   --  Declared_Before grows: each wire before G that is declared counts
   --  one, so two declared wires of a layer have distinct variables, and
   --  all of them are below the layer's count.
   procedure Lemma_Decl_Mono (J : Natural; G : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms,
        Post => (for all G2 in 0 .. G - 1 =>
                   Declared_Before (P, K, J, Reads (P, K, J), G2)
                   + (if Linear (P, K, J, Reads (P, K, J), G2) then 0 else 1)
                   <= Declared_Before (P, K, J, Reads (P, K, J), G))
   is
   begin
      for G1 in 1 .. G loop
         Lemma_Declared_Def (P, K, J, Reads (P, K, J), G1);
         pragma Loop_Invariant
           (for all G2 in 0 .. G1 - 1 =>
              Declared_Before (P, K, J, Reads (P, K, J), G2)
              + (if Linear (P, K, J, Reads (P, K, J), G2) then 0 else 1)
              <= Declared_Before (P, K, J, Reads (P, K, J), G1));
      end loop;
   end Lemma_Decl_Mono;

   --  The variables of layer J's declared wires receive their home
   --  wires' values; the variables below the layer's first are kept.
   procedure Build_Layer (J : Natural; X : in out SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms
                and then X'First = 0 and then X'Length = Max_Vars
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then (for all L in Wr'Range =>
                            Wr (L) /= null and then Wr (L)'First = 0)
                and then First_Var (P, K, J)
                         + Declared_Before (P, K, J, Reads (P, K, J),
                                            Out_Count (P, J))
                         <= Max_Vars,
        Post => (for all I in 0 .. First_Var (P, K, J) - 1 =>
                   Same (X (I), X'Old (I)))
                and then Homes_Layer (J, X)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Homes_Layer);
      FV : constant Natural := First_Var (P, K, J);
      NO : constant Natural := Out_Count (P, J);
   begin
      Lemma_Decl_Mono (J, NO);
      for G in 0 .. NO - 1 loop
         Lemma_Decl_Mono (J, G);
         if not Linear (P, K, J, Reads (P, K, J), G) then
            X (FV + Declared_Before (P, K, J, Reads (P, K, J), G)) :=
              SA.W_At (Wr (J).all, G);
         end if;
         pragma Loop_Invariant
           (for all I in 0 .. FV - 1 => Same (X (I), X'Loop_Entry (I)));
         pragma Loop_Invariant
           (for all G2 in 0 .. G =>
              (if not Linear (P, K, J, Reads (P, K, J), G2) then
                 Same (V_At (X, FV + Declared_Before (P, K, J,
                                                      Reads (P, K, J), G2)),
                       SA.W_At (Wr (J).all, G2))));
      end loop;
   end Build_Layer;

   --  The base: the input wires have their meanings, variable I with
   --  the coefficient one.
   procedure Lemma_Inputs_Mean (X : SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  => P.Ninput <= Max_Vars
                and then X'First = 0 and then X'Length = Max_Vars
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then Wr (P.Last_Layer + 1) /= null
                and then Wr (P.Last_Layer + 1)'First = 0
                and then Wr (P.Last_Layer + 1)'Length = P.Ninput
                and then (for all I in 0 .. P.Ninput - 1 =>
                            Same (X (I), Wr (P.Last_Layer + 1) (I))),
        Post => In_Mean (Reads (P, K, P.Last_Layer),
                         Read_Coefs (P, K, P.Last_Layer), X,
                         Wr (P.Last_Layer + 1).all, P.Ninput)
   is
   begin
      Lemma_Reads_Def (P, K, P.Last_Layer);
      for I in 0 .. P.Ninput - 1 loop
         pragma Assert (Shape_At (Reads (P, K, P.Last_Layer), I).N = 1);
         pragma Assert (Shape_At (Reads (P, K, P.Last_Layer), I).V (1) = I);
         pragma Assert
           (Same (Coefs_At (Read_Coefs (P, K, P.Last_Layer), I) (1), SA.One));
         SA.RL.Lemma_One_Mul (V_At (X, I));
         SA.RL.Lemma_Zero_Add (SA.One * V_At (X, I));
         pragma Assert
           (Same (Mean (Reads (P, K, P.Last_Layer),
                        Read_Coefs (P, K, P.Last_Layer), X, I),
                  V_At (X, I)));
         pragma Loop_Invariant
           (for all I2 in 0 .. I =>
              Same (SA.W_At (Wr (P.Last_Layer + 1).all, I2),
                    Mean (Reads (P, K, P.Last_Layer),
                          Read_Coefs (P, K, P.Last_Layer), X, I2)));
      end loop;
   end Lemma_Inputs_Mean;

   --  The step: the wires layer J reads are layer J + 1's, whose values
   --  are their meanings.
   procedure Lemma_Next_Mean (J : Natural; X : SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  => J < P.Last_Layer
                and then PC.Valid (P) and then SA.Well_Formed (PC.Expand (P))
                and then Len (P, J + 1) <= SA.Max_Terms
                and then Out_Count (P, J + 1) <= SA.Max_Wires
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then Wr (J + 1) /= null and then Wr (J + 1)'First = 0
                and then
                (for all G in 0 .. Out_Count (P, J + 1) - 1 =>
                   Same (SA.W_At (Wr (J + 1).all, G),
                         Mean (Out_Shapes (P, K, J + 1, Reads (P, K, J + 1),
                                           First_Var (P, K, J + 1)),
                               Out_Coefs (P, K, J + 1, Reads (P, K, J + 1),
                                          Read_Coefs (P, K, J + 1)),
                               X, G))),
        Post => In_Mean (Reads (P, K, J), Read_Coefs (P, K, J), X,
                         Wr (J + 1).all, P.Layers (J).NW_In)
   is
   begin
      Lemma_Reads_Def (P, K, J + 1);
      pragma Assert (Out_Count (P, J + 1) = P.Layers (J).NW_In);
   end Lemma_Next_Mean;

   --  The first variable after layer J's: its first, plus its count of
   --  declared wires.
   function Top (J : Natural) return Natural is
     (First_Var (P, K, J)
      + Declared_Before (P, K, J, Reads (P, K, J), Out_Count (P, J)))
   with Ghost => Proof_Only,
        Pre => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms;

   --  Layer J's declared wires have variables below B, holding their
   --  home wires' values.
   function Homes_Below
     (J : Natural; X : SA.Element_Array; B : Natural) return Boolean
   is (for all G in 0 .. Out_Count (P, J) - 1 =>
         (if not Linear (P, K, J, Reads (P, K, J), G) then
            First_Var (P, K, J)
            + Declared_Before (P, K, J, Reads (P, K, J), G) < B
            and then
            Same (V_At (X, First_Var (P, K, J)
                           + Declared_Before (P, K, J, Reads (P, K, J), G)),
                  SA.W_At (Wr (J).all, G))))
   with Ghost => Proof_Only,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => J <= P.Last_Layer and then Wr'First = 0
               and then Wr'Last = P.Last_Layer + 1
               and then Wr (J) /= null and then Wr (J)'First = 0;

   --  A layer whose homes hold has them below its top.
   procedure Lemma_Layer_Below (J : Natural; X : SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then Wr (J) /= null and then Wr (J)'First = 0
                and then Homes_Layer (J, X),
        Post => Homes_Below (J, X, Top (J))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Homes_Layer);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Homes_Below);
   begin
      Lemma_Decl_Mono (J, Out_Count (P, J));
   end Lemma_Layer_Below;

   --  Homes below a bound hold.
   procedure Lemma_Below_Layer (J : Natural; X : SA.Element_Array; B : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then Wr (J) /= null and then Wr (J)'First = 0
                and then Homes_Below (J, X, B),
        Post => Homes_Layer (J, X)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Homes_Layer);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Homes_Below);
   begin
      null;
   end Lemma_Below_Layer;

   --  Values kept below B1 keep the homes below B1, which are below B2.
   procedure Lemma_Kept
     (J : Natural; Xo, Xn : SA.Element_Array; B1, B2 : Natural)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then Wr'First = 0
                and then Wr'Last = P.Last_Layer + 1
                and then Wr (J) /= null and then Wr (J)'First = 0
                and then Xo'First = 0 and then Xn'First = 0
                and then Xo'Length = Xn'Length
                and then B1 <= B2 and then B1 <= Xo'Length
                and then Homes_Below (J, Xo, B1)
                and then (for all I in 0 .. B1 - 1 => Same (Xn (I), Xo (I))),
        Post => Homes_Below (J, Xn, B2)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Homes_Below);
   begin
      null;
   end Lemma_Kept;

   --  One layer of the construction: layer J's variables are set, those
   --  of the layers before it and of the inputs are kept.
   procedure Step_Build (J : Natural; X : in out SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer and then PC.Valid (P)
                and then X'First = 0 and then X'Length = Max_Vars
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then (for all L in Wr'Range =>
                            Wr (L) /= null and then Wr (L)'First = 0)
                and then Wr (P.Last_Layer + 1)'Length = P.Ninput
                and then Layer_Accepted (P, K, J)
                and then P.Ninput <= First_Var (P, K, J)
                and then (for all I in 0 .. P.Ninput - 1 =>
                            Same (X (I), Wr (P.Last_Layer + 1) (I)))
                and then (for all J2 in J + 1 .. P.Last_Layer =>
                            Homes_Below (J2, X, First_Var (P, K, J))),
        Post => (for all I in 0 .. P.Ninput - 1 =>
                   Same (X (I), Wr (P.Last_Layer + 1) (I)))
                and then (for all J2 in J .. P.Last_Layer =>
                            Homes_Below (J2, X, Top (J)))
   is
      Xo : constant SA.Element_Array := X;
   begin
      PC.Lemma_Valid (P);
      pragma Assert (Len (P, J) <= SA.Max_Terms);
      Lemma_Layer_Accepted_Def (P, K, J);
      Build_Layer (J, X);
      Lemma_Layer_Below (J, X);
      for J2 in J + 1 .. P.Last_Layer loop
         Lemma_Kept (J2, Xo, X, First_Var (P, K, J), Top (J));
         pragma Loop_Invariant
           (for all J3 in J + 1 .. J2 => Homes_Below (J3, X, Top (J)));
      end loop;
   end Step_Build;

   --  The construction of the values: the inputs, then the declared
   --  wires layer by layer from the last.
   procedure Build_All (X : out SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  => PC.Valid (P) and then Accepts (P, K)
                and then X'First = 0 and then X'Length = Max_Vars
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then (for all L in Wr'Range =>
                            Wr (L) /= null and then Wr (L)'First = 0)
                and then Wr (P.Last_Layer + 1)'Length = P.Ninput,
        Post => (for all I in 0 .. P.Ninput - 1 =>
                   Same (X (I), Wr (P.Last_Layer + 1) (I)))
                and then (for all J in 0 .. P.Last_Layer => Homes_Layer (J, X))
   is
   begin
      Lemma_Accepts_Def (P, K);
      PC.Lemma_Valid (P);
      X := [others => Zero];
      for I in 0 .. P.Ninput - 1 loop
         X (I) := Wr (P.Last_Layer + 1) (I);
         pragma Loop_Invariant
           (for all I2 in 0 .. I =>
              Same (X (I2), Wr (P.Last_Layer + 1) (I2)));
      end loop;
      for J in reverse 0 .. P.Last_Layer loop
         pragma Assert (Len (P, J) <= SA.Max_Terms);
         pragma Assert (Layer_Accepted (P, K, J));
         Lemma_Reads_Def (P, K, J);
         if J < P.Last_Layer then
            pragma Assert (Len (P, J + 1) <= SA.Max_Terms);
            pragma Assert (Layer_Accepted (P, K, J + 1));
            Lemma_Layer_Accepted_Def (P, K, J + 1);
            Lemma_Reads_Def (P, K, J + 1);
            pragma Assert (First_Var (P, K, J) = Top (J + 1));
            pragma Assert (First_Var (P, K, J + 1) <= First_Var (P, K, J));
         else
            pragma Assert (First_Var (P, K, J) = P.Ninput);
         end if;
         Step_Build (J, X);
         pragma Loop_Invariant (P.Ninput <= First_Var (P, K, J));
         pragma Loop_Invariant
           (for all I in 0 .. P.Ninput - 1 =>
              Same (X (I), Wr (P.Last_Layer + 1) (I)));
         pragma Loop_Invariant
           (for all J2 in J .. P.Last_Layer => Homes_Below (J2, X, Top (J)));
      end loop;
      for J in 0 .. P.Last_Layer loop
         pragma Assert (Len (P, 0) <= SA.Max_Terms);
         Lemma_Below_Layer (J, X, Top (0));
         pragma Loop_Invariant
           (for all J2 in 0 .. J => Homes_Layer (J2, X));
      end loop;
   end Build_All;

   --  The layers in turn, from the last: the wires each reads have their
   --  meanings, so its wires have theirs and its facts hold.
   procedure Check_All (X : SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  =>
          PC.Valid (P) and then SA.Well_Formed (PC.Expand (P))
          and then Accepts (P, K)
          and then X'First = 0 and then X'Length = Max_Vars
          and then P.Ninput >= 1
          and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
          and then (for all L in Wr'Range =>
                      Wr (L) /= null and then Wr (L)'First = 0)
          and then Wr (P.Last_Layer + 1)'Length = P.Ninput
          and then P.Ninput <= Max_Vars
          and then SA.Same (Wr (P.Last_Layer + 1) (0), SA.One)
          and then (for all J in 0 .. P.Last_Layer =>
                      Wr (J)'Length = Out_Count (P, J)
                      and then SA.Layer_Holds_Seg (PC.Expand (P), Wr (J).all,
                                                   Wr (J + 1).all, J)
                      and then SA.Layer_Z_Seg (PC.Expand (P), Wr (J + 1).all,
                                               J))
          and then (for all G in 0 .. P.Noutput - 1 =>
                      SA.F."=" (Wr (0) (G), Zero))
          and then (for all I in 0 .. P.Ninput - 1 =>
                      Same (X (I), Wr (P.Last_Layer + 1) (I)))
          and then (for all J in 0 .. P.Last_Layer => Homes_Layer (J, X)),
        Post => Facts_Hold (P, K, X)
   is
   begin
      Lemma_Accepts_Def (P, K);
      PC.Lemma_Valid (P);
      pragma Assert (PC.Expand (P).Layers (P.Last_Layer).NW_In = P.Ninput);
      pragma Assert (P.Layers (P.Last_Layer).NW_In = P.Ninput);
      pragma Assert (Same (V_At (X, 0), SA.One));
      for J in reverse 0 .. P.Last_Layer loop
         pragma Assert (Layer_Accepted (P, K, J));
         pragma Assert (Wr (J)'Length = Out_Count (P, J));
         pragma Assert (SA.Layer_Holds_Seg (PC.Expand (P), Wr (J).all,
                                            Wr (J + 1).all, J));
         pragma Assert (SA.Layer_Z_Seg (PC.Expand (P), Wr (J + 1).all, J));
         if J = P.Last_Layer then
            Lemma_Inputs_Mean (X);
         else
            Lemma_Next_Mean (J, X);
         end if;
         Lemma_Layer (J, X);
         pragma Loop_Invariant
           (for all J2 in J .. P.Last_Layer => Layer_Facts (P, K, J2, X));
         pragma Loop_Invariant
           (for all G in 0 .. Out_Count (P, J) - 1 =>
              Same (SA.W_At (Wr (J).all, G),
                    Mean (Out_Shapes (P, K, J, Reads (P, K, J),
                                      First_Var (P, K, J)),
                          Out_Coefs (P, K, J, Reads (P, K, J),
                                     Read_Coefs (P, K, J)),
                          X, G)));
      end loop;
   end Check_All;

   --  One layer's homes, unfolded.
   procedure Lemma_Homes_Layer_Def (J : Natural; X : SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  => J <= P.Last_Layer
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then Wr (J) /= null and then Wr (J)'First = 0
                and then Homes_Layer (J, X),
        Post => (for all G in 0 .. Out_Count (P, J) - 1 =>
                   (if not Linear (P, K, J, Reads (P, K, J), G) then
                      SA.Same (V_At (X, First_Var (P, K, J)
                                        + Declared_Before (P, K, J,
                                                           Reads (P, K, J),
                                                           G)),
                               SA.W_At (Wr (J).all, G))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Homes_Layer);
   begin
      null;
   end Lemma_Homes_Layer_Def;

   --  The homes of the theorem's statement, from those of each layer.
   procedure Lemma_Homes_Hold (X : SA.Element_Array)
   with Ghost => Proof_Only,
        Pre  => P.Ninput <= Max_Vars
                and then X'First = 0 and then X'Length = Max_Vars
                and then Wr'First = 0 and then Wr'Last = P.Last_Layer + 1
                and then (for all L in Wr'Range =>
                            Wr (L) /= null and then Wr (L)'First = 0)
                and then Wr (P.Last_Layer + 1)'Length = P.Ninput
                and then (for all I in 0 .. P.Ninput - 1 =>
                            Same (X (I), Wr (P.Last_Layer + 1) (I)))
                and then (for all J in 0 .. P.Last_Layer =>
                            Homes_Layer (J, X)),
        Post => Homes_Hold (P, K, Wr, X)
   is
   begin
      for J in 0 .. P.Last_Layer loop
         Lemma_Homes_Layer_Def (J, X);
         pragma Loop_Invariant
           (for all J2 in 0 .. J =>
              (for all G in 0 .. Out_Count (P, J2) - 1 =>
                 (if not Linear (P, K, J2, Reads (P, K, J2), G) then
                    SA.Same (V_At (X, First_Var (P, K, J2)
                                      + Declared_Before (P, K, J2,
                                                         Reads (P, K, J2), G)),
                             SA.W_At (Wr (J2).all, G)))));
      end loop;
   end Lemma_Homes_Hold;

begin
   Lemma_Accepts_Def (P, K);
   Build_All (V);
   Check_All (V);
   Lemma_Homes_Hold (V);
end Lemma_Accepts;
