pragma SPARK_Mode (On);

with Interfaces; use Interfaces;

package body Sumcheck_Verifier is

   ----------------------------------------------------------------------
   --  Offset lemmas (the bodies of the offset functions are hidden).
   ----------------------------------------------------------------------

   procedure Lemma_Chal_Step (C : Circuit; J : Natural) with
     Ghost, Global => null,
     Pre  => J <= C.Last_Layer,
     Post => Chal_Off (C, J + 1) = Chal_Off (C, J) + Chal_Size (C, J);

   procedure Lemma_Chal_Step (C : Circuit; J : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Chal_Off);
   begin
      null;
   end Lemma_Chal_Step;

   procedure Lemma_Chal_Mono (C : Circuit; I, J : Natural) with
     Ghost, Global => null,
     Pre  => I <= J and then J <= C.Last_Layer + 1,
     Post => Chal_Off (C, I) <= Chal_Off (C, J),
     Subprogram_Variant => (Decreases => J);

   procedure Lemma_Chal_Mono (C : Circuit; I, J : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Chal_Off);
   begin
      if J > I then
         Lemma_Chal_Mono (C, I, J - 1);
      end if;
   end Lemma_Chal_Mono;

   procedure Lemma_Proof_Step (C : Circuit; J : Natural) with
     Ghost, Global => null,
     Pre  => J <= C.Last_Layer,
     Post => Proof_Off (C, J + 1) = Proof_Off (C, J) + Proof_Size (C, J);

   procedure Lemma_Proof_Step (C : Circuit; J : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Proof_Off);
   begin
      null;
   end Lemma_Proof_Step;

   procedure Lemma_Proof_Mono (C : Circuit; I, J : Natural) with
     Ghost, Global => null,
     Pre  => I <= J and then J <= C.Last_Layer + 1,
     Post => Proof_Off (C, I) <= Proof_Off (C, J),
     Subprogram_Variant => (Decreases => J);

   procedure Lemma_Proof_Mono (C : Circuit; I, J : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Proof_Off);
   begin
      if J > I then
         Lemma_Proof_Mono (C, I, J - 1);
      end if;
   end Lemma_Proof_Mono;

   procedure Lemma_Pad_Step (C : Circuit; J : Natural; Base : Natural) with
     Ghost, Global => null,
     Pre  => J <= C.Last_Layer and then Base <= Max_Wires,
     Post => Pad_Off (C, J + 1, Base) = Pad_Off (C, J, Base) + Pad_Size (C, J);

   procedure Lemma_Pad_Step (C : Circuit; J : Natural; Base : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Pad_Off);
   begin
      null;
   end Lemma_Pad_Step;

   ----------------------------------------------------------------------
   --  Constrain_To_Be_Zero
   ----------------------------------------------------------------------

   procedure Constrain_To_Be_Zero
     (E       : Expression;
      A       : in out Ligero_Terms;
      B       : in out Element_Array;
      B_Count : in out Natural)
   is
      Start : constant Natural := A.Count;
      Cst   : constant Natural := B_Count;
      Coeff_Before      : constant Element_Array := A.Coeff with Ghost;
      Constraint_Before : constant Index_Array := A.Constraint with Ghost;
      Witness_Before    : constant Index_Array := A.Witness with Ghost;
   begin
      for I in 1 .. E.Length loop
         pragma Loop_Invariant (A.Count = Start);
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
              A.Witness (Start + K - 1) = E.Terms (K).V);
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 => A.Constraint (Start + K - 1) = Cst);
         pragma Loop_Invariant
           (for all K in 1 .. I - 1 =>
              Same (A.Coeff (Start + K - 1), E.Terms (K).C));
         pragma Loop_Invariant
           (for all K in 0 .. Start - 1 =>
              A.Witness (K) = Witness_Before (K));
         pragma Loop_Invariant
           (for all K in 0 .. Start - 1 =>
              A.Constraint (K) = Constraint_Before (K));
         pragma Loop_Invariant
           (for all K in 0 .. Start - 1 =>
              Same (A.Coeff (K), Coeff_Before (K)));
         A.Coeff (Start + I - 1)      := E.Terms (I).C;
         A.Constraint (Start + I - 1) := Cst;
         A.Witness (Start + I - 1)    := E.Terms (I).V;
      end loop;
      A.Count := Start + E.Length;
      B (Cst) := E.Known;
      B_Count := Cst + 1;
   end Constrain_To_Be_Zero;

   ----------------------------------------------------------------------
   --  Lemma_Round_Shape
   ----------------------------------------------------------------------

   procedure Lemma_Round_Shape
     (Claim      : Expression;
      Pad0, Pad1 : Natural;
      HP0, HP2   : Element;
      Chal       : Element)
   is
      P0  : constant Expression :=
        Add_Constant (Var (Pad0, Claim.Capacity), HP0);
      S0  : constant Expression := Scale (P0, Lagrange_Basis (Chal) (0));
      S1  : constant Expression :=
        Scale (Sub (Claim, P0), Lagrange_Basis (Chal) (1));
      S2  : constant Expression :=
        Scale (Add_Constant (Var (Pad1, Claim.Capacity), HP2),
               Lagrange_Basis (Chal) (2));
      S01 : constant Expression := Add (S0, S1);
   begin
      Lemma_New_Count_Shared (S0, S1, Pad0);
      pragma Assert (S01.Length <= Claim.Length + 1);
      pragma Assert (Add (S01, S2).Length <= Claim.Length + 2);
   end Lemma_Round_Shape;

   ----------------------------------------------------------------------
   --  Ceil_Lg2
   ----------------------------------------------------------------------

   function Ceil_Lg2 (N : Wire_Count) return Natural is
      L : Natural := 0;
   begin
      while L < 24 and then Shift_Left (Unsigned_64'(1), L) < Unsigned_64 (N)
      loop
         pragma Loop_Variant (Increases => L);
         L := L + 1;
      end loop;
      return L;
   end Ceil_Lg2;

   ----------------------------------------------------------------------
   --  Verify_Layer
   ----------------------------------------------------------------------

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
   is
      Cap   : constant Capacity_Type := State.Capacity;
      Logw  : constant Logw_Type := C.Layers (J).Logw;
      CO    : constant Natural := Chal_Off (C, J);
      PO    : constant Natural := Proof_Off (C, J);
      PB    : constant Natural := Pad_Off (C, J, Base);
      HC0   : Challenge_Vector := [others => Zero];
      HC1   : Challenge_Vector := [others => Zero];
   begin
      --  The blocks of this layer lie inside the records.
      Lemma_Chal_Step (C, J);
      Lemma_Chal_Mono (C, J + 1, C.Last_Layer + 1);
      Lemma_Proof_Step (C, J);
      Lemma_Proof_Mono (C, J + 1, C.Last_Layer + 1);
      Lemma_Pad_Step (C, J, Base);
      declare
         Alpha : constant Element := Ch.Layer (CO);
         Beta  : constant Element := Ch.Layer (CO + 1);
         Claim : Expression (Cap) :=
           Add (State.Claim0, Scale (State.Claim1, Alpha));
      begin
         --  The 2 logw symbolic rounds: round K / 2, hand K mod 2.
         for K in 0 .. 2 * Logw - 1 loop
            pragma Loop_Invariant (Claim.Capacity = Cap);
            pragma Loop_Invariant (Claim.Length <= 2 + 2 * K);
            pragma Loop_Invariant (Below (Claim, PB + 2 * K));
            declare
               Pad0 : constant Natural := PB + 2 * K;
               Chal : constant Element := Ch.Layer (CO + 2 + K);
               HP0  : constant Element := Proof.Evals (PO + 2 * K);
               HP2  : constant Element := Proof.Evals (PO + 2 * K + 1);
            begin
               Lemma_Round_Shape (Claim, Pad0, Pad0 + 1, HP0, HP2, Chal);
               Claim := Symbolic_Round (Claim, Pad0, Pad0 + 1, HP0, HP2, Chal);
               if K mod 2 = 0 then
                  HC0 (K / 2) := Chal;
               else
                  HC1 (K / 2) := Chal;
               end if;
            end;
         end loop;

         declare
            EQQ  : constant Element :=
              Eval_Bound_Quad (Layer_Terms (C, J), State.Logv,
                               State.HC0, State.HC1, HC0, HC1, Logw,
                               Alpha, Beta);
            C0   : constant Natural := PB + 4 * Logw;
            C1   : constant Natural := C0 + 1;
            CR   : constant Natural := C0 + 2;
            Cl0  : constant Element := Proof.Evals (PO + 4 * Logw);
            Cl1  : constant Element := Proof.Evals (PO + 4 * Logw + 1);
            --  (Var c0 * cl1 + Var c1 * cl0 + Var cr + cl0 cl1) * eqq
            Prod : constant Expression :=
              Scale (Add_Constant (Add (Add (Scale (Var (C0, Cap), Cl1),
                                             Scale (Var (C1, Cap), Cl0)),
                                        Var (CR, Cap)),
                                   Cl0 * Cl1),
                     EQQ);
         begin
            Claim := Sub (Claim, Prod);
            Constrain_To_Be_Zero (Claim, A, B, B_Count);
            Lqc := (X => C0, Y => C1, Z => CR);
            State := (Capacity => Cap,
                      Logv     => Logw,
                      Claim0   => Add_Constant (Var (C0, Cap), Cl0),
                      Claim1   => Add_Constant (Var (C1, Cap), Cl1),
                      HC0      => HC0,
                      HC1      => HC1);
         end;
      end;
   end Verify_Layer;

   ----------------------------------------------------------------------
   --  Input_Constraint
   ----------------------------------------------------------------------

   procedure Input_Constraint
     (C       : Circuit;
      Pub     : Element_Array;
      State   : Claims_State;
      Alpha   : Element;
      A       : in out Ligero_Terms;
      B       : in out Element_Array;
      B_Count : in out Natural)
   is
      Cap    : constant Capacity_Type := State.Capacity;
      N      : constant Wire_Count := C.Ninput;
      NP     : constant Wire_Count := C.Npublic;
      Eq_Vec : Element_Array (0 .. N - 1) := [others => Zero];
      Pub_Binding : Element := Zero;
      Mle    : Expression (Cap) := From_Constant (Zero, Cap);
   begin
      for I in 0 .. N - 1 loop
         Eq_Vec (I) := Eq2 (I, State.Logv, State.HC0, State.HC1, Alpha);
      end loop;
      for I in 0 .. NP - 1 loop
         Pub_Binding := Pub_Binding + Eq_Vec (I) * Pub (I);
      end loop;
      Mle := From_Constant (Pub_Binding, Cap);
      for W in 0 .. N - NP - 1 loop
         pragma Loop_Invariant (Mle.Capacity = Cap);
         pragma Loop_Invariant (Mle.Length = W);
         pragma Loop_Invariant (Below (Mle, W));
         Mle := Add_Term (Mle, W, Eq_Vec (NP + W));
      end loop;
      declare
         Got : constant Expression :=
           Add (State.Claim0, Scale (State.Claim1, Alpha));
      begin
         Mle := Sub (Mle, Got);
      end;
      Constrain_To_Be_Zero (Mle, A, B, B_Count);
   end Input_Constraint;

   ----------------------------------------------------------------------
   --  Verifier_Core
   ----------------------------------------------------------------------

   procedure Verifier_Core
     (C       : Circuit;
      Pub     : Element_Array;
      Proof   : Sumcheck_Proof;
      Ch      : Challenges;
      A       : out Ligero_Terms;
      B       : out Element_Array;
      Lqc     : out Lqc_Array)
   is
      Cap     : constant Capacity_Type := Capacity_Of (C);
      Base    : constant Natural := C.Ninput - C.Npublic;
      B_Count : Natural := 0;
      State   : Claims_State (Cap) :=
        (Capacity => Cap,
         Logv     => Ceil_Lg2 (C.Noutput),
         Claim0   => From_Constant (Zero, Cap),
         Claim1   => From_Constant (Zero, Cap),
         HC0      => Ch.G,
         HC1      => Ch.G);
   begin
      A   := (Max        => A.Max,
              Count      => 0,
              Coeff      => [others => Zero],
              Constraint => [others => 0],
              Witness    => [others => 0]);
      B   := [others => Zero];
      Lqc := [others => (X => 0, Y => 0, Z => 0)];
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant (A.Count <= J * (4 * Max_Logw + 5));
         pragma Loop_Invariant (B_Count = J);
         pragma Loop_Invariant (State.Capacity = Cap);
         pragma Loop_Invariant
           (State.Claim0.Length <= 1 and then State.Claim1.Length <= 1);
         pragma Loop_Invariant (Below (State.Claim0, Pad_Off (C, J, Base)));
         pragma Loop_Invariant (Below (State.Claim1, Pad_Off (C, J, Base)));
         pragma Loop_Invariant
           (for all J2 in 0 .. J - 1 =>
              Lqc (J2) = (X => Pad_Off (C, J2, Base) + 4 * C.Layers (J2).Logw,
                          Y => Pad_Off (C, J2, Base) + 4 * C.Layers (J2).Logw
                                 + 1,
                          Z => Pad_Off (C, J2, Base) + 4 * C.Layers (J2).Logw
                                 + 2));
         Verify_Layer (C, J, Proof, Ch, Base, State, A, B, B_Count, Lqc (J));
      end loop;
      Input_Constraint (C, Pub, State, Ch.Alpha_Input, A, B, B_Count);
   end Verifier_Core;

end Sumcheck_Verifier;
