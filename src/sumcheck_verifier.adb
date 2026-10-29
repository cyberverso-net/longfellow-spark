pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Ada.Unchecked_Deallocation;

package body Sumcheck_Verifier is

   --  The eq2 table of the input constraint, on the heap (ADR 0047).
   type Elems_Access is access Element_Array;

   procedure Free_Elems is
     new Ada.Unchecked_Deallocation (Element_Array, Elems_Access);

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

   procedure Lemma_Pad_Step (C : Circuit; J : Natural; Base : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Pad_Off);
   begin
      null;
   end Lemma_Pad_Step;

   procedure Lemma_Pad_Mono (C : Circuit; I, J : Natural; Base : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Pad_Off);
   begin
      if J > I then
         Lemma_Pad_Mono (C, I, J - 1, Base);
      end if;
   end Lemma_Pad_Mono;

   --  The terms Constrain_To_Be_Zero appended from an expression below
   --  Bound are below Bound: the instantiation from the term index K to
   --  the expression index K - Start + 1, made once here.
   procedure Lemma_Terms_Below
     (A     : Ligero_Terms;
      Start : Natural;
      E     : Expression;
      Bound : Natural;
      Cst   : Natural)
   with
     Ghost, Global => null,
     Pre  => Below (E, Bound)
       and then A.Count >= E.Length and then Start = A.Count - E.Length
       and then (for all I in 1 .. E.Length =>
                   A.Witness (Start + I - 1) = E.Terms (I).V)
       and then (for all I in 1 .. E.Length =>
                   A.Constraint (Start + I - 1) = Cst),
     Post => (for all K in Start .. A.Count - 1 =>
                A.Witness (K) < Bound and then A.Constraint (K) = Cst);

   procedure Lemma_Terms_Below
     (A     : Ligero_Terms;
      Start : Natural;
      E     : Expression;
      Bound : Natural;
      Cst   : Natural)
   is
   begin
      for K in Start .. A.Count - 1 loop
         pragma Loop_Invariant
           (for all K2 in Start .. K - 1 =>
              A.Witness (K2) < Bound and then A.Constraint (K2) = Cst);
         pragma Assert (A.Witness (K) = E.Terms (K - Start + 1).V);
         pragma Assert (A.Constraint (K) = Cst);
      end loop;
   end Lemma_Terms_Below;

   procedure Lemma_Pads_Below (C : Circuit) is
      Base : constant Natural := C.Ninput - C.Npublic;
   begin
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant
           (for all J2 in 0 .. J - 1 =>
              Pad_Off (C, J2, Base) + 4 * C.Layers (J2).Logw + 3
              <= Witness_Count (C));
         Lemma_Pad_Step (C, J, Base);
         Lemma_Pad_Mono (C, J + 1, C.Last_Layer + 1, Base);
      end loop;
   end Lemma_Pads_Below;

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
      P1  : constant Expression := Sub (Claim, P0);
   begin
      Lemma_New_Count_Shared (S0, S1, Pad0);
      pragma Assert (S01.Length <= Claim.Length + 1);
      pragma Assert (Add (S01, S2).Length <= Claim.Length + 2);
      --  Variables, step by step: P0 names Pad0, P1 the claim's and Pad0,
      --  S2 names Pad1; Scale keeps positions; Add and Sub unite.
      pragma Assert (Below (P0, Pad1));
      pragma Assert (Below (Claim, Pad1));
      Lemma_Below_Union (Claim, P0, P1, Pad1);
      pragma Assert (Below (S0, Pad1));
      pragma Assert (Below (S1, Pad1));
      Lemma_Below_Union (S0, S1, S01, Pad1);
      pragma Assert (Below (S01, Pad1 + 1));
      pragma Assert (Below (S2, Pad1 + 1));
      declare
         Next : constant Expression := Add (S01, S2);
      begin
         Lemma_Below_Union (S01, S2, Next, Pad1 + 1);
      end;
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
      EQQ_In  : Element;
      State   : in out Claims_State;
      A       : in out Ligero_Terms;
      B       : in out Element_Array;
      B_Count : in out Natural;
      Lqc     : out Lqc_Triple)
   is
      Cap   : constant Capacity_Type := Layer_Capacity;
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
         SC1   : constant Expression := Scale (State.Claim1, Alpha);
         Claim : Expression (Cap) := Add (State.Claim0, SC1);
      begin
         pragma Assert (Below (SC1, PB));
         Lemma_Below_Union (State.Claim0, SC1, Claim, PB);
         --  The 2 logw symbolic rounds: round K / 2, hand K mod 2.
         for K in 0 .. 2 * Logw - 1 loop
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

         --  The bound quad, from Bound_Quads in the verifier and from the
         --  sumcheck in the prover (ADR 0071).
         declare
            EQQ_V : constant Element := EQQ_In;
         begin
            declare
               EQQ  : constant Element := EQQ_V;
               C0   : constant Natural := PB + 4 * Logw;
               C1   : constant Natural := C0 + 1;
               CR   : constant Natural := C0 + 2;
               Cl0  : constant Element := Proof.Evals (PO + 4 * Logw);
               Cl1  : constant Element := Proof.Evals (PO + 4 * Logw + 1);
               --  (Var c0 * cl1 + Var c1 * cl0 + Var cr + cl0 cl1) * eqq,
               --  piece by piece so that its variables are seen below
               --  the next layer's pad offset (the Post on the terms).
               V0   : constant Expression := Scale (Var (C0, Cap), Cl1);
               V1   : constant Expression := Scale (Var (C1, Cap), Cl0);
               V01  : constant Expression := Add (V0, V1);
               V2   : constant Expression := Var (CR, Cap);
               V012 : constant Expression := Add (V01, V2);
               Prod : constant Expression :=
                 Scale (Add_Constant (V012, Cl0 * Cl1), EQQ);
               Before : constant Expression := Claim with Ghost;
            begin
               pragma Assert (Below (V0, CR + 1));
               pragma Assert (Below (V1, CR + 1));
               Lemma_Below_Union (V0, V1, V01, CR + 1);
               pragma Assert (Below (V2, CR + 1));
               Lemma_Below_Union (V01, V2, V012, CR + 1);
               pragma Assert (Below (Prod, CR + 1));
               pragma Assert (Below (Before, CR + 1));
               Claim := Sub (Claim, Prod);
               Lemma_Below_Union (Before, Prod, Claim, CR + 1);
               pragma Assert (CR + 1 = Pad_Off (C, J + 1, Base));
               declare
                  Start : constant Natural := A.Count with Ghost;
                  Cst   : constant Natural := B_Count with Ghost;
               begin
                  Constrain_To_Be_Zero (Claim, A, B, B_Count);
                  Lemma_Terms_Below (A, Start, Claim, CR + 1, Cst);
               end;
               Lqc := (X => C0, Y => C1, Z => CR);
               State := (Logv     => Logw,
                         Claim0   => Add_Constant (Var (C0, Cap), Cl0),
                         Claim1   => Add_Constant (Var (C1, Cap), Cl1),
                         HC0      => HC0,
                         HC1      => HC1);
            end;
         end;
      end;
   end Verify_Layer;

   ----------------------------------------------------------------------
   --  Input_Constraint
   ----------------------------------------------------------------------

   --  The terms of E appended as constraint Cst, without its constant.
   procedure Append_Terms
     (E   : Expression;
      A   : in out Ligero_Terms;
      Cst : Natural)
   with
     Global => null,
     Pre  => E.Length <= A.Max + 1 - A.Count,
     Post => A.Count = A.Count'Old + E.Length
       and then (for all I in 1 .. E.Length =>
                   A.Witness (A.Count'Old + I - 1) = E.Terms (I).V)
       and then (for all I in 1 .. E.Length =>
                   A.Constraint (A.Count'Old + I - 1) = Cst)
       and then (for all I in 1 .. E.Length =>
                   Same (A.Coeff (A.Count'Old + I - 1), E.Terms (I).C))
       and then (for all K in 0 .. A.Count'Old - 1 =>
                   A.Witness (K) = A.Witness'Old (K))
       and then (for all K in 0 .. A.Count'Old - 1 =>
                   A.Constraint (K) = A.Constraint'Old (K))
       and then (for all K in 0 .. A.Count'Old - 1 =>
                   Same (A.Coeff (K), A.Coeff'Old (K)))
   is
      Start : constant Natural := A.Count;
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
   end Append_Terms;

   --  One term per private input W, in input order: witness W,
   --  coefficient Eq2 (npublic + W), constraint Cst.
   procedure Append_Inputs
     (C     : Circuit;
      State : Claims_State;
      Alpha : Element;
      E     : Element_Array;
      A     : in out Ligero_Terms;
      Cst   : Natural)
   with
     Global => null,
     Pre  =>
       (Runtime =>
          A.Max + 1 - A.Count >= C.Ninput - C.Npublic and then E'First = 0
          and then (if State.Logv <= Max_Bindeq_Log
                    then E'Last = Table_Len (State.Logv) - 1),
        Proof_Only =>
          (if State.Logv <= Max_Bindeq_Log then
             (for all X in E'Range =>
                Same (E (X), Beq2 (X, State.Logv, State.HC0, State.HC1,
                                   Alpha))))),
     Post =>
       (Runtime =>
          A.Count = A.Count'Old + (C.Ninput - C.Npublic)
          and then (for all W in 0 .. C.Ninput - C.Npublic - 1 =>
                      A.Witness (A.Count'Old + W) = W
                      and then A.Constraint (A.Count'Old + W) = Cst)
          and then (for all K in A.Count'Old .. A.Count - 1 =>
                      A.Witness (K) = K - A.Count'Old
                      and then A.Constraint (K) = Cst)
          and then (for all K in 0 .. A.Count'Old - 1 =>
                      A.Witness (K) = A.Witness'Old (K)
                      and then A.Constraint (K) = A.Constraint'Old (K)),
        Proof_Only =>
          (for all W in 0 .. C.Ninput - C.Npublic - 1 =>
             Same (A.Coeff (A.Count'Old + W),
                   In_Coef (C.Npublic + W, State, Alpha))))
   is
      Start : constant Natural := A.Count;
      NP    : constant Wire_Count := C.Npublic;
      NW    : constant Natural := C.Ninput - C.Npublic;
      Fast  : constant Boolean := State.Logv <= Max_Bindeq_Log;
      Constraint_Before : constant Index_Array := A.Constraint with Ghost;
      Witness_Before    : constant Index_Array := A.Witness with Ghost;
   begin
      for W in 0 .. NW - 1 loop
         A.Coeff (Start + W) :=
           (if Fast then Pad (E, NP + W)
            else Eq2 (NP + W, State.Logv, State.HC0, State.HC1, Alpha));
         A.Constraint (Start + W) := Cst;
         A.Witness (Start + W)    := W;
         pragma Loop_Invariant (A.Count = Start);
         pragma Loop_Invariant
           (for all K in 0 .. W =>
              A.Witness (Start + K) = K
              and then A.Constraint (Start + K) = Cst);
         pragma Loop_Invariant
           (for all K in Start .. Start + W =>
              A.Witness (K) = K - Start
              and then A.Constraint (K) = Cst);
         pragma Loop_Invariant
           (Proof_Only =>
              (for all K in 0 .. W =>
                 Same (A.Coeff (Start + K), In_Coef (NP + K, State, Alpha))));
         pragma Loop_Invariant
           (for all K in 0 .. Start - 1 =>
              A.Witness (K) = Witness_Before (K)
              and then A.Constraint (K) = Constraint_Before (K));
      end loop;
      A.Count := Start + NW;
   end Append_Inputs;

   procedure Input_Constraint
     (C       : Circuit;
      Pub     : Element_Array;
      State   : Claims_State;
      Alpha   : Element;
      A       : in out Ligero_Terms;
      B       : in out Element_Array;
      B_Count : in out Natural)
   is
      NP    : constant Wire_Count := C.Npublic;
      NW    : constant Natural := C.Ninput - C.Npublic;
      WC    : constant Natural := Witness_Count (C);
      Start : constant Natural := A.Count;
      Cst   : constant Natural := B_Count;
      Fast  : constant Boolean := State.Logv <= Max_Bindeq_Log;
      Binding : Element := Zero;
      --  The eq2 table of the final binding (Phase D, M1); one unused
      --  element when it does not fit.
      E : Elems_Access :=
        new Element_Array'
          (0 .. (if Fast then Table_Len (State.Logv) - 1 else 0) => Zero);
   begin
      if Fast then
         Eq2_Table (State.Logv, State.HC0, State.HC1, Alpha, E.all);
      end if;
      for I in 0 .. NP - 1 loop
         Binding := SA."+" (Binding,
                            SA."*" ((if Fast then Pad (E.all, I)
                                     else Eq2 (I, State.Logv, State.HC0,
                                               State.HC1, Alpha)),
                                    Pub (I)));
         pragma Loop_Invariant
           (Proof_Only =>
              Same (Binding, Pub_Binding_Ref (Pub, State, Alpha, I + 1)));
      end loop;
      pragma Assert
        (Proof_Only =>
           Same (Binding, Pub_Binding_Ref (Pub, State, Alpha, NP)));

      Append_Inputs (C, State, Alpha, E.all, A, Cst);
      Free_Elems (E);
      --  The input terms name witnesses below NW, and NW is below the
      --  witness count: the private inputs come before every pad.
      pragma Assert (NW <= WC);
      pragma Assert
        (for all K in Start .. A.Count - 1 =>
           A.Witness (K) < WC and then A.Constraint (K) = Cst);

      declare
         FC  : constant Expression := From_Constant (Binding, Layer_Capacity);
         SC1 : constant Expression := Scale (State.Claim1, Alpha);
         Got : constant Expression := Add (State.Claim0, SC1);
         T   : constant Expression := Input_Tail (Binding, State, Alpha);
         Mid : constant Natural := A.Count;
      begin
         pragma Assert (SC1.Length = State.Claim1.Length);
         pragma Assert (Got.Length <= 2);
         pragma Assert (T.Length <= Got.Length);
         pragma Assert (Below (SC1, WC));
         Lemma_Below_Union (State.Claim0, SC1, Got, WC);
         pragma Assert (Below (FC, WC));
         Lemma_Below_Union (FC, Got, T, WC);
         Append_Terms (T, A, Cst);
         Lemma_Terms_Below (A, Mid, T, WC, Cst);
         B (Cst) := T.Known;
         B_Count := Cst + 1;
         pragma Assert
           (for all K in Start .. Mid - 1 =>
              A.Witness (K) < WC and then A.Constraint (K) = Cst);
      end;
   end Input_Constraint;

   ----------------------------------------------------------------------
   --  Verifier_Core
   ----------------------------------------------------------------------

   procedure Lemma_BQ_Ref_Frame
     (C        : Circuit;
      Ch1, Ch2 : Challenges;
      J        : Natural;
      Lim      : Natural)
   is
      pragma Unreferenced (Lim);
      Logw : constant Natural := C.Layers (J).Logw;
      Logv : constant Natural := Layer_Logv (C, J);
   begin
      if J > 0 then
         Lemma_Chal_Step (C, J - 1);
      end if;
      if Logv <= Max_Bindeq_Log and then Logw <= Max_Bindeq_Log then
         Lemma_EBQT_Frame
           (Layer_Terms (C, J), Layer_Terms (C, J)'Length, Logv,
            Layer_G (C, Ch1, J, 0), Layer_G (C, Ch1, J, 1),
            Layer_G (C, Ch2, J, 0), Layer_G (C, Ch2, J, 1),
            Hand_Chal (C, Ch1, J, 0), Hand_Chal (C, Ch1, J, 1),
            Hand_Chal (C, Ch2, J, 0), Hand_Chal (C, Ch2, J, 1),
            Logw, Chv (Ch1, Chal_Off (C, J)), Chv (Ch1, Chal_Off (C, J) + 1));
      else
         Lemma_EBQ_Frame
           (Layer_Terms (C, J), Layer_Terms (C, J)'Length, Logv,
            Layer_G (C, Ch1, J, 0), Layer_G (C, Ch1, J, 1),
            Layer_G (C, Ch2, J, 0), Layer_G (C, Ch2, J, 1),
            Hand_Chal (C, Ch1, J, 0), Hand_Chal (C, Ch1, J, 1),
            Hand_Chal (C, Ch2, J, 0), Hand_Chal (C, Ch2, J, 1),
            Logw, Chv (Ch1, Chal_Off (C, J)), Chv (Ch1, Chal_Off (C, J) + 1));
      end if;
   end Lemma_BQ_Ref_Frame;

   procedure Lemma_BQ_Ref_Frame_All
     (C        : Circuit;
      Ch1, Ch2 : Challenges;
      J        : Natural)
   is
   begin
      for J2 in 0 .. J - 1 loop
         Lemma_Chal_Step (C, J2);
         Lemma_Chal_Mono (C, J2 + 1, J);
         Lemma_BQ_Ref_Frame (C, Ch1, Ch2, J2, Chal_Off (C, J));
         pragma Loop_Invariant
           (for all J3 in 0 .. J2 =>
              Same (BQ_Ref (C, Ch1, J3), BQ_Ref (C, Ch2, J3)));
      end loop;
   end Lemma_BQ_Ref_Frame_All;

   procedure Lemma_Hand_Chal
     (C  : Circuit;
      Ch : Challenges;
      J  : Natural;
      H  : Natural;
      V  : Element_Array)
   is
   begin
      null;
   end Lemma_Hand_Chal;

   procedure Lemma_Layer_G_Frame
     (C        : Circuit;
      Ch1, Ch2 : Challenges;
      J        : Natural)
   is
      pragma Unreferenced (Ch1, Ch2);
   begin
      if J > 0 then
         Lemma_Chal_Step (C, J - 1);
      end if;
   end Lemma_Layer_G_Frame;

   procedure Lemma_BQ_Ref_From
     (C        : Circuit;
      Ch       : Challenges;
      J        : Natural;
      Logv     : Natural;
      G0, G1   : Element_Array;
      HC0, HC1 : Element_Array;
      V        : Element)
   is
      pragma Unreferenced (V);
      Logw : constant Natural := C.Layers (J).Logw;
   begin
      Lemma_Hand_Chal (C, Ch, J, 0, HC0);
      Lemma_Hand_Chal (C, Ch, J, 1, HC1);
      if Logv <= Max_Bindeq_Log and then Logw <= Max_Bindeq_Log then
         Lemma_EBQT_Frame
           (Layer_Terms (C, J), Layer_Terms (C, J)'Length, Logv,
            G0, G1, Layer_G (C, Ch, J, 0), Layer_G (C, Ch, J, 1),
            HC0, HC1, Hand_Chal (C, Ch, J, 0), Hand_Chal (C, Ch, J, 1),
            Logw, Ch.Layer (Chal_Off (C, J)), Ch.Layer (Chal_Off (C, J) + 1));
      else
         Lemma_EBQ_Frame
           (Layer_Terms (C, J), Layer_Terms (C, J)'Length, Logv,
            G0, G1, Layer_G (C, Ch, J, 0), Layer_G (C, Ch, J, 1),
            HC0, HC1, Hand_Chal (C, Ch, J, 0), Hand_Chal (C, Ch, J, 1),
            Logw, Ch.Layer (Chal_Off (C, J)), Ch.Layer (Chal_Off (C, J) + 1));
      end if;
   end Lemma_BQ_Ref_From;

   procedure Bound_Quads (C : Circuit; Ch : Challenges; BQ : out Element_Array)
   is
      Logv   : Natural := Ceil_Lg2 (C.Noutput);
      G0, G1 : Challenge_Vector := Ch.G;
   begin
      BQ := [others => Zero];
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant (Logv <= Max_Logw);
         pragma Loop_Invariant
           (Proof_Only =>
              Logv = Layer_Logv (C, J)
              and then (for all R in 0 .. Logv - 1 =>
                          Same (G0 (R), Layer_G (C, Ch, J, 0) (R))
                          and then Same (G1 (R), Layer_G (C, Ch, J, 1) (R)))
              and then (for all J2 in 0 .. J - 1 =>
                          Same (BQ (J2), BQ_Ref (C, Ch, J2))));
         Lemma_Chal_Step (C, J);
         Lemma_Chal_Mono (C, J + 1, C.Last_Layer + 1);
         declare
            Logw : constant Logw_Type := C.Layers (J).Logw;
            CO   : constant Natural := Chal_Off (C, J);
            HC0  : Challenge_Vector := [others => Zero];
            HC1  : Challenge_Vector := [others => Zero];
            V    : Element;
         begin
            for R in 0 .. Logw - 1 loop
               HC0 (R) := Ch.Layer (CO + 2 + 2 * R);
               HC1 (R) := Ch.Layer (CO + 2 + 2 * R + 1);
               pragma Loop_Invariant
                 (for all R2 in 0 .. R =>
                    Same (HC0 (R2), Ch.Layer (CO + 2 + 2 * R2))
                    and then Same (HC1 (R2), Ch.Layer (CO + 2 + 2 * R2 + 1)));
            end loop;
            --  The terms of the layer as a slice of the circuit, passed by
            --  reference: Layer_Terms is the same value, but as a function
            --  result it was copied, the size of the largest layer.
            if Logv <= Max_Bindeq_Log and then Logw <= Max_Bindeq_Log then
               HQ.Bind_Quad
                 (C.Terms (C.Layers (J).First .. C.Layers (J).Last),
                  Logv, G0, G1, HC0, HC1,
                  Logw, Ch.Layer (CO), Ch.Layer (CO + 1), V);
            else
               V := Eval_Bound_Quad
                 (C.Terms (C.Layers (J).First .. C.Layers (J).Last),
                  Logv, G0, G1, HC0, HC1, Logw,
                  Ch.Layer (CO), Ch.Layer (CO + 1));
            end if;
            Lemma_BQ_Ref_From (C, Ch, J, Logv, G0, G1, HC0, HC1, V);
            Lemma_Hand_Chal (C, Ch, J, 0, HC0);
            Lemma_Hand_Chal (C, Ch, J, 1, HC1);
            BQ (J) := V;
            Logv := Logw;
            G0 := HC0;
            G1 := HC1;
         end;
      end loop;
   end Bound_Quads;

   procedure Verifier_Core
     (C       : Circuit;
      Pub     : Element_Array;
      Proof   : Sumcheck_Proof;
      Ch      : Challenges;
      BQ      : Element_Array;
      A       : out Ligero_Terms;
      B       : out Element_Array;
      Lqc     : out Lqc_Array)
   is
      Base    : constant Natural := C.Ninput - C.Npublic;
      B_Count : Natural := 0;
      State   : Claims_State :=
        (Logv     => Ceil_Lg2 (C.Noutput),
         Claim0   => From_Constant (Zero, Layer_Capacity),
         Claim1   => From_Constant (Zero, Layer_Capacity),
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
         pragma Loop_Invariant
           (State.Claim0.Length <= 1 and then State.Claim1.Length <= 1);
         pragma Loop_Invariant (Below (State.Claim0, Pad_Off (C, J, Base)));
         pragma Loop_Invariant (Below (State.Claim1, Pad_Off (C, J, Base)));
         pragma Loop_Invariant
           (for all K in 0 .. A.Count - 1 =>
              A.Witness (K) < Pad_Off (C, J, Base)
              and then A.Constraint (K) < J);
         pragma Loop_Invariant
           (for all J2 in 0 .. J - 1 =>
              Lqc (J2) = (X => Pad_Off (C, J2, Base) + 4 * C.Layers (J2).Logw,
                          Y => Pad_Off (C, J2, Base) + 4 * C.Layers (J2).Logw
                                 + 1,
                          Z => Pad_Off (C, J2, Base) + 4 * C.Layers (J2).Logw
                                 + 2));
         Lemma_Pad_Step (C, J, Base);
         Verify_Layer
           (C, J, Proof, Ch, Base, BQ (J), State, A, B, B_Count, Lqc (J));
      end loop;
      Input_Constraint (C, Pub, State, Ch.Alpha_Input, A, B, B_Count);
   end Verifier_Core;

end Sumcheck_Verifier;
