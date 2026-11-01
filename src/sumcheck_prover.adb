pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;

package body Sumcheck_Prover is

   --  The predicate of Circuit is checked where a circuit enters the
   --  program. Inside this body every predicate check is proved by
   --  GNATprove, and the property does not depend on the formal Fill.
   --  The instances for the command line, compiled with checks (ADR
   --  0068), would otherwise scan the whole circuit at every call that
   --  passes it, once per layer.
   pragma Suppress (Predicate_Check);

   --  The kernels of the bound quad and the invariant of their rounds,
   --  from the instance of the verifier (ADR 0073).
   package HQ renames ST.SV.HQ;
   package BQ renames HQ.BQ with Ghost => Proof_Only;

   subtype Logw_Type is ST.SA.Logw_Type;
   Max_Logw : constant := ST.SA.Max_Logw;

   -------------------------------------------------------------------
   --  Heap buffers (ADR 0047)
   -------------------------------------------------------------------

   type Elems_Access is access Element_Array;
   type Terms_Access is access Term_Array;

   procedure Free_Elems is
     new Ada.Unchecked_Deallocation (Element_Array, Elems_Access);
   procedure Free_Terms is
     new Ada.Unchecked_Deallocation (Term_Array, Terms_Access);

   -------------------------------------------------------------------
   --  The offsets of the core, unfolded one step (as the readers do)
   -------------------------------------------------------------------

   procedure Lemma_Chal_Step (S : Shape; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => J <= S.Last_Layer,
     Post   => ST.SV.Chal_Off (S, J + 1)
               = ST.SV.Chal_Off (S, J) + ST.SV.Chal_Size (S, J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         ST.SV.Chal_Off);
   begin
      null;
   end Lemma_Chal_Step;

   procedure Lemma_Chal_Mono (S : Shape; I, J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => I <= J and then J <= S.Last_Layer + 1,
     Post   => ST.SV.Chal_Off (S, I) <= ST.SV.Chal_Off (S, J),
     Subprogram_Variant => (Decreases => J)
   is
   begin
      if J > I then
         Lemma_Chal_Step (S, J - 1);
         Lemma_Chal_Mono (S, I, J - 1);
      end if;
   end Lemma_Chal_Mono;

   procedure Lemma_Proof_Step (S : Shape; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => J <= S.Last_Layer,
     Post   => ST.SV.Proof_Off (S, J + 1)
               = ST.SV.Proof_Off (S, J) + ST.SV.Proof_Size (S, J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         ST.SV.Proof_Off);
   begin
      null;
   end Lemma_Proof_Step;

   procedure Lemma_Proof_Mono (S : Shape; I, J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => I <= J and then J <= S.Last_Layer + 1,
     Post   => ST.SV.Proof_Off (S, I) <= ST.SV.Proof_Off (S, J),
     Subprogram_Variant => (Decreases => J)
   is
   begin
      if J > I then
         Lemma_Proof_Step (S, J - 1);
         Lemma_Proof_Mono (S, I, J - 1);
      end if;
   end Lemma_Proof_Mono;

   --  Layer J's blocks lie within the three totals.
   procedure Lemma_Layer_Fits (S : Shape; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => J <= S.Last_Layer,
     Post   => ST.SV.Chal_Off (S, J) + ST.SV.Chal_Size (S, J)
               <= ST.SV.Chal_Total (S)
               and then ST.SV.Proof_Off (S, J) + ST.SV.Proof_Size (S, J)
                        <= ST.SV.Proof_Total (S)
               and then ST.SV.Pad_Off (S, J, 0) + ST.SV.Pad_Size (S, J)
                        <= Pad_Total (S)
   is
   begin
      Lemma_Chal_Step (S, J);
      Lemma_Chal_Mono (S, J + 1, S.Last_Layer + 1);
      Lemma_Proof_Step (S, J);
      Lemma_Proof_Mono (S, J + 1, S.Last_Layer + 1);
      ST.SV.Lemma_Pad_Step (S, J, 0);
      ST.SV.Lemma_Pad_Mono (S, J + 1, S.Last_Layer + 1, 0);
   end Lemma_Layer_Fits;

   --  The input wires of layer J are segment J + 1 of the wires buffer.
   procedure Lemma_Segment (S : Shape; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => J <= S.Last_Layer,
     Post   => ST.SA.Off (S, J + 1) + S.Layers (J).NW_In
               <= ST.SA.Total_Wires (S)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", ST.SA.Off);
   begin
      --  Off (S, J + 2) = Off (S, J + 1) + Seg_Size (S, J + 1), with
      --  Seg_Size (S, J + 1) = NW_In of layer J, and Off is monotonic
      --  up to Total_Wires = Off (S, Last_Layer + 2).
      for K in J + 2 .. S.Last_Layer + 2 loop
         pragma Loop_Invariant
           (ST.SA.Off (S, J + 1) + S.Layers (J).NW_In <= ST.SA.Off (S, K));
      end loop;
   end Lemma_Segment;

   -------------------------------------------------------------------
   --  Sample_Pads
   -------------------------------------------------------------------

   procedure Sample_Pads (S : Shape; Pads : out Element_Array) is
      C0, C1 : Element;
   begin
      Pads := [others => Zero];
      for J in 0 .. S.Last_Layer loop
         Lemma_Layer_Fits (S, J);
         declare
            Off  : constant Natural := ST.SV.Pad_Off (S, J, 0);
            Logw : constant Logw_Type := S.Layers (J).Logw;
         begin
            for R in 0 .. Logw - 1 loop
               pragma Loop_Invariant
                 (Off + ST.SV.Pad_Size (S, J) <= Pads'Length);
               for K in 0 .. 3 loop
                  pragma Loop_Invariant
                    (Off + ST.SV.Pad_Size (S, J) <= Pads'Length);
                  SP.Sample_Element (Pads (Off + 4 * R + K));
               end loop;
            end loop;
            SP.Sample_Element (C0);
            SP.Sample_Element (C1);
            Pads (Off + 4 * Logw)     := C0;
            Pads (Off + 4 * Logw + 1) := C1;
            Pads (Off + 4 * Logw + 2) := C0 * C1;
         end;
      end loop;
   end Sample_Pads;

   -------------------------------------------------------------------
   --  Lqc_Triples
   -------------------------------------------------------------------

   procedure Lqc_Triples (S : Shape; Lqc : out ST.SV.Lqc_Array) is
      Base : constant Natural := S.Ninput - S.Npublic;
      Pi   : Natural := Base;
   begin
      Lqc := [others => (X => 0, Y => 0, Z => 0)];
      ST.SV.Lemma_Pads_Below (S);
      for J in 0 .. S.Last_Layer loop
         pragma Loop_Invariant (Pi = ST.SV.Pad_Off (S, J, Base));
         pragma Loop_Invariant
           (for all J2 in 0 .. J - 1 =>
              Lqc (J2) = (X => ST.SV.Pad_Off (S, J2, Base)
                                 + 4 * S.Layers (J2).Logw,
                          Y => ST.SV.Pad_Off (S, J2, Base)
                                 + 4 * S.Layers (J2).Logw + 1,
                          Z => ST.SV.Pad_Off (S, J2, Base)
                                 + 4 * S.Layers (J2).Logw + 2));
         Lqc (J) := (X => Pi + 4 * S.Layers (J).Logw,
                     Y => Pi + 4 * S.Layers (J).Logw + 1,
                     Z => Pi + 4 * S.Layers (J).Logw + 2);
         ST.SV.Lemma_Pad_Step (S, J, Base);
         Pi := Pi + 4 * S.Layers (J).Logw + 3;
      end loop;
   end Lqc_Triples;

   -------------------------------------------------------------------
   --  Round_Evals
   -------------------------------------------------------------------

   --  One step of each reference.
   procedure Lemma_Ev_Step
     (T      : Term_Array;
      Active : Element_Array;
      NA     : Natural;
      Other  : Element_Array;
      NO     : Natural;
      H      : Hand;
      X2     : Element;
      K      : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Active'First = 0 and then NA <= Active'Length
               and then Other'First = 0 and then NO <= Other'Length
               and then K >= 1 and then K <= T'Length,
     Post   =>
       (declare
          Tm   : constant Term := T (T'First + K - 1);
          Hb   : constant Natural := Hand_Index (Tm, H);
          Pair : constant Natural := Hb - Hb mod 2;
          W0   : constant Element := Ref (Active, NA, Pair);
          W1   : constant Element := Ref (Active, NA, Pair + 1);
          Coef : constant Element :=
            Tm.K * Ref (Other, NO, Hand_Index (Tm, 1 - H));
          Wx2  : constant Element := W0 + X2 * (W1 - W0);
        begin
          (if Hb mod 2 = 0 then
             Same (Ev0_Ref (T, Active, NA, Other, NO, H, X2, K),
                   Ev0_Ref (T, Active, NA, Other, NO, H, X2, K - 1)
                   + Coef * W0)
             and then
             Same (Ev2_Ref (T, Active, NA, Other, NO, H, X2, K),
                   Ev2_Ref (T, Active, NA, Other, NO, H, X2, K - 1)
                   + (Coef * (One - X2)) * Wx2)
           else
             Same (Ev0_Ref (T, Active, NA, Other, NO, H, X2, K),
                   Ev0_Ref (T, Active, NA, Other, NO, H, X2, K - 1))
             and then
             Same (Ev2_Ref (T, Active, NA, Other, NO, H, X2, K),
                   Ev2_Ref (T, Active, NA, Other, NO, H, X2, K - 1)
                   + (Coef * X2) * Wx2)))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Ev0_Ref);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Ev2_Ref);
   begin
      null;
   end Lemma_Ev_Step;

   procedure Lemma_Ev_Zero
     (T      : Term_Array;
      Active : Element_Array;
      NA     : Natural;
      Other  : Element_Array;
      NO     : Natural;
      H      : Hand;
      X2     : Element)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Active'First = 0 and then NA <= Active'Length
               and then Other'First = 0 and then NO <= Other'Length,
     Post   => Same (Ev0_Ref (T, Active, NA, Other, NO, H, X2, 0), Zero)
               and then
               Same (Ev2_Ref (T, Active, NA, Other, NO, H, X2, 0), Zero)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Ev0_Ref);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Ev2_Ref);
   begin
      null;
   end Lemma_Ev_Zero;

   procedure Round_Evals
     (T      : Term_Array;
      Active : Element_Array;
      NA     : Natural;
      Other  : Element_Array;
      NO     : Natural;
      H      : Hand;
      X2     : Element;
      Ev0    : out Element;
      Ev2    : out Element)
   is
      One_Minus_X2 : constant Element := One - X2;
      Hb, Pair     : Natural;
      W0, W1, Coef, Wx2 : Element;
   begin
      Ev0 := Zero;
      Ev2 := Zero;
      Lemma_Ev_Zero (T, Active, NA, Other, NO, H, X2);
      for I in T'Range loop
         pragma Loop_Invariant
           (Proof_Only =>
              Same (Ev0, Ev0_Ref (T, Active, NA, Other, NO, H, X2,
                                  I - T'First))
              and then Same (Ev2, Ev2_Ref (T, Active, NA, Other, NO, H, X2,
                                           I - T'First)));
         Hb   := Hand_Index (T (I), H);
         Pair := Hb - Hb mod 2;
         W0   := Ref (Active, NA, Pair);
         W1   := Ref (Active, NA, Pair + 1);
         Coef := T (I).K * Ref (Other, NO, Hand_Index (T (I), 1 - H));
         Wx2  := W0 + X2 * (W1 - W0);
         if Hb mod 2 = 0 then
            Ev0 := Ev0 + Coef * W0;
            Ev2 := Ev2 + (Coef * One_Minus_X2) * Wx2;
         else
            Ev2 := Ev2 + (Coef * X2) * Wx2;
         end if;
         Lemma_Ev_Step (T, Active, NA, Other, NO, H, X2, I - T'First + 1);
      end loop;
   end Round_Evals;

   -------------------------------------------------------------------
   --  Round_Evals_Dense
   -------------------------------------------------------------------

   procedure Lemma_QW_Zero
     (T : Term_Array; Other : Element_Array; NO : Natural; H : Hand)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Other'First = 0 and then NO <= Other'Length,
     Post   => (for all X in Natural =>
                  Same (QW_Ref (T, Other, NO, H, X, 0), Zero))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", QW_Ref);
   begin
      null;
   end Lemma_QW_Zero;

   procedure Lemma_QW_Step
     (T : Term_Array; Other : Element_Array; NO : Natural; H : Hand;
      K : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Other'First = 0 and then NO <= Other'Length
               and then K >= 1 and then K <= T'Length,
     Post   =>
       (for all X in Natural =>
          Same (QW_Ref (T, Other, NO, H, X, K),
                (if Hand_Index (T (T'First + K - 1), H) = X
                 then QW_Ref (T, Other, NO, H, X, K - 1)
                      + T (T'First + K - 1).K
                        * Ref (Other, NO,
                               Hand_Index (T (T'First + K - 1), 1 - H))
                 else QW_Ref (T, Other, NO, H, X, K - 1))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", QW_Ref);
   begin
      null;
   end Lemma_QW_Step;

   procedure Lemma_D_Zero
     (QW : Element_Array; A : Element_Array; NA : Natural; X2 : Element)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => QW'First = 0 and then A'First = 0
               and then NA <= QW'Length and then NA <= A'Length,
     Post   => Same (D0_Ref (QW, A, NA, 0), Zero)
               and then Same (D2_Ref (QW, A, NA, X2, 0), Zero)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", D0_Ref);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", D2_Ref);
   begin
      null;
   end Lemma_D_Zero;

   procedure Lemma_D_Step
     (QW : Element_Array; A : Element_Array; NA : Natural; X2 : Element;
      M  : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => QW'First = 0 and then A'First = 0
               and then NA <= QW'Length and then NA <= A'Length
               and then M >= 1 and then M <= Natural'Last / 2,
     Post   =>
       Same (D0_Ref (QW, A, NA, M),
             D0_Ref (QW, A, NA, M - 1)
             + Ref (QW, NA, 2 * (M - 1)) * Ref (A, NA, 2 * (M - 1)))
       and then
       Same (D2_Ref (QW, A, NA, X2, M),
             D2_Ref (QW, A, NA, X2, M - 1)
             + (Ref (QW, NA, 2 * (M - 1))
                + X2 * (Ref (QW, NA, 2 * M - 1)
                        - Ref (QW, NA, 2 * (M - 1))))
               * (Ref (A, NA, 2 * (M - 1))
                  + X2 * (Ref (A, NA, 2 * M - 1)
                          - Ref (A, NA, 2 * (M - 1)))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", D0_Ref);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", D2_Ref);
   begin
      null;
   end Lemma_D_Step;

   -------------------------------------------------------------------
   --  The round evaluations from three sums (ADR 0070): a0 = sum q0 w0,
   --  s1 = sum q1 w1 and a2 = sum dq dw, with dq = q1 - q0 and
   --  dw = w1 - w0. Each pair contributes
   --  (q0 + x dq) (w0 + x dw) = a0 + x (s1 - a0 - a2) + x^2 a2 to p (x),
   --  and the combination is additive, so p (P2) is Comb of the sums.
   --  These identities are the Lemma_Comb_*_F of Sumcheck_Algebra,
   --  proved in Ring_Laws on the hidden wrappers. The prover computes
   --  only a0 and a2, two products per pair, and takes s1 from the
   --  claim of the round (ADR 0075); D1_Ref is the s1 of the proof.
   -------------------------------------------------------------------

   function Comb (X, A0, S1, A2 : Element) return Element
     renames ST.SA.Comb_F;

   procedure Lemma_D13_Step
     (QW : Element_Array; A : Element_Array; NA : Natural; M : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => QW'First = 0 and then A'First = 0
               and then NA <= QW'Length and then NA <= A'Length
               and then M <= Natural'Last / 2,
     Post   =>
       (if M = 0 then
          Same (D1_Ref (QW, A, NA, M), Zero)
          and then Same (Dd_Ref (QW, A, NA, M), Zero)
        else
          Same (D1_Ref (QW, A, NA, M),
                D1_Ref (QW, A, NA, M - 1)
                + Ref (QW, NA, 2 * M - 1) * Ref (A, NA, 2 * M - 1))
          and then
          Same (Dd_Ref (QW, A, NA, M),
                Dd_Ref (QW, A, NA, M - 1)
                + (Ref (QW, NA, 2 * M - 1) - Ref (QW, NA, 2 * (M - 1)))
                  * (Ref (A, NA, 2 * M - 1) - Ref (A, NA, 2 * (M - 1)))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", D1_Ref);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Dd_Ref);
   begin
      null;
   end Lemma_D13_Step;

   procedure Lemma_D2_Split
     (QW : Element_Array; A : Element_Array; NA : Natural; X2 : Element;
      M  : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => QW'First = 0 and then A'First = 0
               and then NA <= QW'Length and then NA <= A'Length
               and then M <= Natural'Last / 2,
     Post   => Same (D2_Ref (QW, A, NA, X2, M),
                     Comb (X2, D0_Ref (QW, A, NA, M), D1_Ref (QW, A, NA, M),
                           Dd_Ref (QW, A, NA, M))),
     Subprogram_Variant => (Decreases => M)
   is
   begin
      Lemma_D13_Step (QW, A, NA, M);
      if M = 0 then
         Lemma_D_Zero (QW, A, NA, X2);
         ST.SA.Lemma_Comb_Zero_F (X2);
      else
         Lemma_D2_Split (QW, A, NA, X2, M - 1);
         Lemma_D_Step (QW, A, NA, X2, M);
         ST.SA.Lemma_Comb_Add_F
           (X2, D0_Ref (QW, A, NA, M - 1), D1_Ref (QW, A, NA, M - 1),
            Dd_Ref (QW, A, NA, M - 1),
            Ref (QW, NA, 2 * (M - 1)) * Ref (A, NA, 2 * (M - 1)),
            Ref (QW, NA, 2 * M - 1) * Ref (A, NA, 2 * M - 1),
            (Ref (QW, NA, 2 * M - 1) - Ref (QW, NA, 2 * (M - 1)))
            * (Ref (A, NA, 2 * M - 1) - Ref (A, NA, 2 * (M - 1))));
         ST.SA.Lemma_Comb_Pair_F
           (X2, Ref (QW, NA, 2 * (M - 1)), Ref (QW, NA, 2 * M - 1),
            Ref (A, NA, 2 * (M - 1)), Ref (A, NA, 2 * M - 1));
      end if;
   end Lemma_D2_Split;

   procedure Round_Evals_Dense
     (T      : Term_Array;
      Active : Element_Array;
      NA     : Natural;
      Other  : Element_Array;
      NO     : Natural;
      H      : Hand;
      X2     : Element;
      Sum    : Element;
      QW     : in out Element_Array;
      Ev0    : out Element;
      Ev2    : out Element;
      Lead   : out Element)
   is
      Hb : Natural;
      Q0, Q1, W0, W1 : Element;
   begin
      for X in 0 .. NA - 1 loop
         QW (X) := Zero;
         pragma Loop_Invariant
           (Proof_Only => (for all Y in 0 .. X => Same (QW (Y), Zero)));
      end loop;
      Lemma_QW_Zero (T, Other, NO, H);

      --  The scatter: one product per term. The index of a term of a
      --  well-formed circuit is always below NA; the guard keeps the
      --  write in range otherwise, and QW_Ref agrees below NA.
      for I in T'Range loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all X in 0 .. NA - 1 =>
                 Same (QW (X), QW_Ref (T, Other, NO, H, X, I - T'First))));
         Hb := Hand_Index (T (I), H);
         if Hb < NA then
            QW (Hb) :=
              QW (Hb) + T (I).K * Ref (Other, NO, Hand_Index (T (I), 1 - H));
         end if;
         Lemma_QW_Step (T, Other, NO, H, I - T'First + 1);
      end loop;
      pragma Assert
        (Proof_Only =>
           (for all X in 0 .. NA - 1 =>
              Same (QW (X), QW_Ref (T, Other, NO, H, X, T'Length))));

      --  The pairs: the two sums, two products per pair, then p (P2)
      --  with p (1) = Sum - p (0) (prover.rs, quad_round_poly; ADR 0070,
      --  0075).
      Ev0  := Zero;
      Lead := Zero;
      Lemma_D_Zero (QW, Active, NA, X2);
      Lemma_D13_Step (QW, Active, NA, 0);
      for M in 0 .. (NA + 1) / 2 - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              Same (Ev0, D0_Ref (QW, Active, NA, M))
              and then Same (Lead, Dd_Ref (QW, Active, NA, M)));
         Q0 := Ref (QW, NA, 2 * M);
         Q1 := Ref (QW, NA, 2 * M + 1);
         W0 := Ref (Active, NA, 2 * M);
         W1 := Ref (Active, NA, 2 * M + 1);
         Ev0  := Ev0 + Q0 * W0;
         Lead := Lead + (Q1 - Q0) * (W1 - W0);
         Lemma_D_Step (QW, Active, NA, X2, M + 1);
         Lemma_D13_Step (QW, Active, NA, M + 1);
      end loop;
      Ev2 := Comb (X2, Ev0, Sum - Ev0, Lead);
      Lemma_D2_Split (QW, Active, NA, X2, (NA + 1) / 2);
      ST.SA.Lemma_Cancel_L_F
        (Ev0, D1_Ref (QW, Active, NA, (NA + 1) / 2));
   end Round_Evals_Dense;

   procedure Update_Terms (T : in out Term_Array; H : Hand; X : Element) is
      One_Minus_X : constant Element := One - X;
   begin
      for I in T'Range loop
         if Hand_Index (T (I), H) mod 2 = 0 then
            T (I).K := T (I).K * One_Minus_X;
         else
            T (I).K := T (I).K * X;
         end if;
         if H = 0 then
            T (I).H0 := T (I).H0 / 2;
         else
            T (I).H1 := T (I).H1 / 2;
         end if;
      end loop;
   end Update_Terms;

   -------------------------------------------------------------------
   --  Prove
   -------------------------------------------------------------------

   --  bind of hand H: A (0 .. N - 1) into B (0 .. (N + 1) / 2 - 1).
   procedure Bind_Hand
     (A : Element_Array; B : Elems_Access; N : in out Natural; X : Element)
   with
     Global => null,
     Pre    => B /= null
               and then A'First = 0 and then B'First = 0
               and then N <= A'Length and then N <= B'Length
               and then N <= ST.SA.Max_Wires,
     Post   => N = (N'Old + 1) / 2;

   procedure Bind_Hand
     (A : Element_Array; B : Elems_Access; N : in out Natural; X : Element)
   is
      M : constant Natural := (N + 1) / 2;
   begin
      if N > 0 then
         ST.SA.Bind (A (0 .. N - 1), X, B (0 .. M - 1));
      end if;
      N := M;
   end Bind_Hand;

   --  One hand of round R: the challenge stored at R in the challenges
   --  of the hand (C0 for hand 0, C1 for hand 1), then Bind_H on the
   --  first NT terms, with the invariant of the rounds carried over to
   --  the next hand (ADR 0071).
   procedure Bind_Round
     (T      : in out Term_Array;
      NT     : in out Natural;
      H      : Hand;
      Chal   : Element;
      R      : Natural;
      C0, C1 : in out Element_Array;
      Layer  : in out Element_Array;
      Off    : Natural;
      Tab    : Boolean;
      T0     : Term_Array;
      Logv   : Natural;
      G0, G1 : Element_Array;
      Alpha  : Element;
      Beta   : Element)
   with
     Global => null,
     Pre    =>
       (Runtime    =>
          NT <= T'Length
          and then C0'First = 0 and then C1'First = 0
          and then R < C0'Length and then R < C1'Length
          and then R < Max_Logw
          and then Layer'First = 0
          and then Off <= Layer'Last
          and then 3 + 2 * R <= Layer'Last - Off,
        Proof_Only =>
          (for all R2 in 0 .. R - 1 =>
             Same (C0 (R2), Layer (Off + 2 + 2 * R2))
             and then Same (C1 (R2), Layer (Off + 2 + 2 * R2 + 1)))
          and then (if H = 1 then Same (C0 (R), Layer (Off + 2 + 2 * R)))
          and then
          (if Tab then
             G0'First = 0 and then G1'First = 0
             and then Logv <= G0'Length and then Logv <= G1'Length
             and then Logv <= ST.SA.Max_Bindeq_Log
             and then BQ.Inv (T, NT, BQ.Bound_Array (T0, Logv, G0, G1, Alpha,
                                                     Beta), C0,
                              (if H = 0 then R else R + 1), C1, R))),
     Post   =>
       (Runtime    => NT <= T'Length,
        Proof_Only =>
          Same (Layer (Off + 2 + 2 * R + H), Chal)
          and then (for all K in Layer'Range =>
                      (if K /= Off + 2 + 2 * R + H
                       then Same (Layer (K), Layer'Old (K))))
          and then (for all R2 in 0 .. R =>
                      Same (C0 (R2), Layer (Off + 2 + 2 * R2)))
          and then (for all R2 in 0 .. (if H = 0 then R - 1 else R) =>
                      Same (C1 (R2), Layer (Off + 2 + 2 * R2 + 1)))
          and then
          (if H = 0
           then Same (C0 (R), Chal)
                and then (for all I in C0'Range =>
                            (if I /= R then Same (C0 (I), C0'Old (I))))
                and then (for all I in C1'Range => Same (C1 (I), C1'Old (I)))
           else Same (C1 (R), Chal)
                and then (for all I in C1'Range =>
                            (if I /= R then Same (C1 (I), C1'Old (I))))
                and then (for all I in C0'Range => Same (C0 (I), C0'Old (I))))
          and then
          (if Tab then
             BQ.Inv (T, NT, BQ.Bound_Array (T0, Logv, G0, G1, Alpha, Beta), C0,
                     R + 1, C1,
                     (if H = 0 then R else R + 1))))
   is
      Old : constant Term_Array := T (T'First .. T'First + NT - 1)
      with Ghost => Proof_Only;
      Sav : constant Element_Array := (if H = 0 then C0 else C1)
      with Ghost => Proof_Only;
      NB  : Natural;
   begin
      Layer (Off + 2 + 2 * R + H) := Chal;
      if H = 0 then
         C0 (R) := Chal;
      else
         C1 (R) := Chal;
      end if;
      if Tab then
         if H = 0 then
            BQ.Lemma_Inv_Frame (T, NT, BQ.Bound_Array (T0, Logv, G0, G1, Alpha,
              Beta), Sav, C0, R, C1, C1, R);
            BQ.Lemma_Inv_Slice (T, Old, NT, BQ.Bound_Array (T0, Logv, G0, G1,
              Alpha, Beta), C0, R, C1, R);
         else
            BQ.Lemma_Inv_Frame (T, NT, BQ.Bound_Array (T0, Logv, G0, G1, Alpha,
              Beta), C0, C0, R + 1, Sav, C1, R);
            BQ.Lemma_Inv_Slice (T, Old, NT, BQ.Bound_Array (T0, Logv, G0, G1,
              Alpha, Beta), C0, R + 1, C1, R);
         end if;
      end if;
      HQ.Bind_H (T (T'First .. T'First + NT - 1), H, Chal, NB);
      if Tab then
         BQ.Lemma_Corners_W (Old, T (T'First .. T'First + NT - 1), H, Chal,
                             NB);
         if H = 0 then
            BQ.Lemma_Inv_Step0
              (Old, T (T'First .. T'First + NT - 1), NB, BQ.Bound_Array (T0,
                Logv, G0, G1, Alpha, Beta), C0, R, C1, R);
            BQ.Lemma_Inv_Slice
              (T (T'First .. T'First + NT - 1), T, NB, BQ.Bound_Array (T0,
                Logv, G0, G1, Alpha, Beta), C0, R + 1, C1, R);
         else
            BQ.Lemma_Inv_Step1
              (Old, T (T'First .. T'First + NT - 1), NB, BQ.Bound_Array (T0,
                Logv, G0, G1, Alpha, Beta),
               C0, R + 1, C1, R);
            BQ.Lemma_Inv_Slice
              (T (T'First .. T'First + NT - 1), T, NB, BQ.Bound_Array (T0,
                Logv, G0, G1, Alpha, Beta),
               C0, R + 1, C1, R + 1);
         end if;
      end if;
      NT := NB;
   end Bind_Round;

   --  The claim of the rounds (ADR 0075), tracked as upstream's layer
   --  does: claim0 + alpha claim1 at the start of a layer, then p at the
   --  challenge after each round. Procedures of their own with no
   --  postcondition, so that the contracts of their products stay out of
   --  the proof of Prove_Layer; nothing about the claim is proved.
   procedure First_Claim (Cl0, Cl1, Alpha : Element; Sum : out Element)
   with Global => null;

   procedure First_Claim (Cl0, Cl1, Alpha : Element; Sum : out Element) is
   begin
      Sum := Cl0 + Alpha * Cl1;
   end First_Claim;

   procedure Next_Claim (Chal, Ev0, Lead : Element; Sum : in out Element)
   with Global => null;

   procedure Next_Claim (Chal, Ev0, Lead : Element; Sum : in out Element) is
   begin
      Sum := Comb (Chal, Ev0, Sum - Ev0, Lead);
   end Next_Claim;

   --  One layer of sumcheck_prove: the binding of g, the 2 logw rounds
   --  of the two hands, the claims; Logv, Cur0 and Cur1 move on to the
   --  next layer, and so do the unpadded claims Cl0 and Cl1, from which
   --  the claim of each round is tracked as upstream does (ADR 0075). A subprogram of its own, so that the proof of a layer
   --  sees only this context (ADR 0071).
   procedure Prove_Layer
     (C          : Circuit;
      J          : Natural;
      Wires      : Element_Array;
      Pads       : Element_Array;
      Logv       : in out Natural;
      Cur0, Cur1 : in out Element_Array;
      Nxt0, Nxt1 : in out Element_Array;
      Cl0, Cl1   : in out Element;
      Proof      : in out Sumcheck_Proof;
      Ch         : in out Challenges;
      BQJ        : out Element)
   with
     Always_Terminates => not ST.SA.F.Sampling_Rejects,
     Pre  =>
       (Runtime =>
       J <= C.Last_Layer
       and then Wires'First = 0
       and then Wires'Length = ST.SA.Total_Wires (Shape_Of (C))
       and then Pads'First = 0 and then Pads'Length = Pad_Total (Shape_Of (C))
       and then Logv <= Max_Logw
       and then Cur0'First = 0 and then Cur0'Last = Max_Logw - 1
       and then Cur1'First = 0 and then Cur1'Last = Max_Logw - 1
       and then Nxt0'First = 0 and then Nxt0'Last = Max_Logw - 1
       and then Nxt1'First = 0 and then Nxt1'Last = Max_Logw - 1
       and then Proof.Last + 1 = ST.SV.Proof_Total (Shape_Of (C))
       and then Ch.Last + 1 = ST.SV.Chal_Total (Shape_Of (C)),
        Proof_Only =>
          Logv = ST.SV.Layer_Logv (Shape_Of (C), J)
          and then (for all R in 0 .. Logv - 1 =>
                      Same (Cur0 (R),
                            ST.SV.Layer_G (Shape_Of (C), Ch, J, 0) (R))
                      and then
                      Same (Cur1 (R),
                            ST.SV.Layer_G (Shape_Of (C), Ch, J, 1) (R)))),
     Post =>
       (Runtime    => Logv <= Max_Logw,
        Proof_Only =>
          Same (BQJ, ST.SV.BQ_Ref (C, Ch, J))
          and then Logv = C.Layers (J).Logw
          and then (for all R in 0 .. Logv - 1 =>
                      Same (Cur0 (R),
                            ST.SV.Hand_Chal (Shape_Of (C), Ch, J, 0) (R))
                      and then
                      Same (Cur1 (R),
                            ST.SV.Hand_Chal (Shape_Of (C), Ch, J, 1) (R)))
          and then Ch.Last = Ch'Old.Last
          and then (for all R in 0 .. Max_Logw - 1 =>
                      Same (Ch.G (R), Ch'Old.G (R)))
          and then (for all K in 0 .. Ch.Last =>
                      (if K < ST.SV.Chal_Off (Shape_Of (C), J)
                       then Same (Ch.Layer (K), Ch'Old.Layer (K)))))
   is
      S     : constant Shape := Shape_Of (C);
      Ch_In : constant Challenges := Ch with Ghost => Proof_Only;
      Alpha, Beta, Chal, Ev0, Ev2, Lead, P0, P2V, Sum : Element;
      N0, N1, NT : Natural;
   begin
      Lemma_Layer_Fits (S, J);
      Lemma_Segment (S, J);
      declare
         Logw  : constant Logw_Type := C.Layers (J).Logw;
         NW    : constant Natural := C.Layers (J).NW_In;
         Seg   : constant Natural := ST.SA.Off (S, J + 1);
         Off_P : constant Natural := ST.SV.Proof_Off (S, J);
         Off_C : constant Natural := ST.SV.Chal_Off (S, J);
         Off_D : constant Natural := ST.SV.Pad_Off (S, J, 0);
         First : constant Positive := C.Layers (J).First;
         Last  : constant Natural := C.Layers (J).Last;
         T  : Terms_Access := new Term_Array'(C.Terms (First .. Last));
         A0 : Elems_Access := new Element_Array'(0 .. NW - 1 => Zero);
         A1 : Elems_Access := new Element_Array'(0 .. NW - 1 => Zero);
         B0 : Elems_Access := new Element_Array'(0 .. NW - 1 => Zero);
         B1 : Elems_Access := new Element_Array'(0 .. NW - 1 => Zero);
         Q  : Elems_Access := new Element_Array'(0 .. NW - 1 => Zero);
         --  The bound quad of the layer (ADR 0071), with the terms of
         --  the layer, the terms bound with g, and the challenges
         --  before each draw, for the proof.
         Tab  : constant Boolean :=
           Logv <= ST.SA.Max_Bindeq_Log
           and then Logw <= ST.SA.Max_Bindeq_Log;
         BQ_J : Element := Zero;
      begin
         for I in 0 .. NW - 1 loop
            pragma Loop_Invariant (A0 /= null and then A1 /= null);
            pragma Loop_Invariant (A0'Length = NW and then A1'Length = NW);
            A0 (I) := Wires (Seg + I);
            A1 (I) := Wires (Seg + I);
         end loop;
         N0 := NW;
         N1 := NW;
         ST.Begin_Layer (Alpha, Beta);
         Ch.Layer (Off_C)     := Alpha;
         Ch.Layer (Off_C + 1) := Beta;
         --  The claim of the first round (prover.rs, layer).
         First_Claim (Cl0, Cl1, Alpha, Sum);
         --  bind_g with the eq2 table when it fits, then the runs of
         --  equal hands merged: NT terms from here on.
         if Logv <= ST.SA.Max_Bindeq_Log then
            declare
               E : Elems_Access := new Element_Array'
                 (0 .. ST.SA.Table_Len (Logv) - 1 => Zero);
            begin
               ST.SA.Eq2_Table (Logv, Cur0, Cur1, Alpha, E.all);
               HQ.Bind_G_T (T.all, E.all, Beta);
               BQ.Lemma_T1_Bound
                 (C.Terms (First .. Last), T.all, E.all, Logv, Cur0, Cur1,
                  Alpha, Beta);
               Free_Elems (E);
            end;
         else
            ST.SA.Bind_G (T.all, Logv, Cur0, Cur1, Alpha, Beta);
         end if;
         HQ.Merge_Terms
           (T.all, NT, Tab, C.Terms (First .. Last), Logv, Cur0, Cur1, Alpha,
            Beta,
            Nxt0, Nxt1);
         for R in 0 .. Logw - 1 loop
            pragma Loop_Invariant
              (T /= null and then A0 /= null and then A1 /= null
               and then B0 /= null and then B1 /= null
               and then Q /= null);
            pragma Loop_Invariant
              (A0'First = 0 and then A1'First = 0
               and then B0'First = 0 and then B1'First = 0
               and then Q'First = 0
               and then A0'Length = NW and then A1'Length = NW
               and then B0'Length = NW and then B1'Length = NW
               and then Q'Length = NW);
            pragma Loop_Invariant (N0 <= NW and then N1 <= NW);
            pragma Loop_Invariant (NT <= T'Length);
            pragma Loop_Invariant (T'First = First and then T'Last = Last);
            pragma Loop_Invariant
              (Proof_Only =>
                 (if Tab
                  then BQ.Inv (T.all, NT,
                               BQ.Bound_Array (C.Terms (First .. Last), Logv,
                                               Cur0, Cur1, Alpha, Beta),
                               Nxt0, R, Nxt1, R)));
            pragma Loop_Invariant (Proof.Last + 1 = ST.SV.Proof_Total (S));
            pragma Loop_Invariant (Ch.Last + 1 = ST.SV.Chal_Total (S));
            pragma Loop_Invariant (Proof_Only => Ch.Last = Ch_In.Last);
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all R2 in 0 .. Max_Logw - 1 =>
                    Same (Ch.G (R2), Ch_In.G (R2))));
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all K in 0 .. Ch.Last =>
                    (if K < Off_C
                     then Same (Ch.Layer (K), Ch_In.Layer (K)))));
            pragma Loop_Invariant
              (Proof_Only =>
                 Same (Ch.Layer (Off_C), Alpha)
                 and then Same (Ch.Layer (Off_C + 1), Beta));
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all R2 in 0 .. R - 1 =>
                    Same (Nxt0 (R2), Ch.Layer (Off_C + 2 + 2 * R2))));
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all R2 in 0 .. R - 1 =>
                    Same (Nxt1 (R2), Ch.Layer (Off_C + 2 + 2 * R2 + 1))));
            --  Hand 0 on A0 against A1, then hand 1 on A1 against the
            --  bound A0, as the reference does.
            Round_Evals_Dense
              (T (T'First .. T'First + NT - 1), A0.all, N0, A1.all, N1, 0,
               P2, Sum, Q.all, Ev0, Ev2, Lead);
            P0  := Ev0 - Pads (Off_D + 4 * R);
            P2V := Ev2 - Pads (Off_D + 4 * R + 1);
            ST.Round_Poly (P0, P2V, Chal);
            --  The claim of the next round: p at the challenge.
            Next_Claim (Chal, Ev0, Lead, Sum);
            Proof.Evals (Off_P + 4 * R)     := P0;
            Proof.Evals (Off_P + 4 * R + 1) := P2V;
            Bind_Hand (A0.all, B0, N0, Chal);
            declare
               Tmp : Elems_Access := A0;
            begin
               A0 := B0;
               B0 := Tmp;
            end;
            Bind_Round
              (T.all, NT, 0, Chal, R, Nxt0, Nxt1, Ch.Layer, Off_C,
               Tab, C.Terms (First .. Last), Logv, Cur0, Cur1, Alpha, Beta);
            Round_Evals_Dense
              (T (T'First .. T'First + NT - 1), A1.all, N1, A0.all, N0, 1,
               P2, Sum, Q.all, Ev0, Ev2, Lead);
            P0  := Ev0 - Pads (Off_D + 4 * R + 2);
            P2V := Ev2 - Pads (Off_D + 4 * R + 3);
            ST.Round_Poly (P0, P2V, Chal);
            Next_Claim (Chal, Ev0, Lead, Sum);
            Proof.Evals (Off_P + 4 * R + 2) := P0;
            Proof.Evals (Off_P + 4 * R + 3) := P2V;
            Bind_Hand (A1.all, B1, N1, Chal);
            declare
               Tmp : Elems_Access := A1;
            begin
               A1 := B1;
               B1 := Tmp;
            end;
            Bind_Round
              (T.all, NT, 1, Chal, R, Nxt0, Nxt1, Ch.Layer, Off_C,
               Tab, C.Terms (First .. Last), Logv, Cur0, Cur1, Alpha, Beta);
         end loop;
         --  The bound quad: the coefficients left at hands (0, 0).
         pragma Assert
           (Proof_Only =>
              (if Tab
               then BQ.Inv (T.all, NT, BQ.Bound_Array (C.Terms (First .. Last),
                 Logv, Cur0, Cur1, Alpha, Beta),
                            Nxt0, Logw, Nxt1, Logw)));
         BQ.Lemma_W_Zero (T.all, 0, 0, 0);
         for I in 0 .. NT - 1 loop
            BQ.Lemma_W_Step (T.all, I, 0, 0, 0);
            if T (T'First + I).H0 = 0 and then T (T'First + I).H1 = 0 then
               ST.SA.Lemma_Add_W (BQ_J, T (T'First + I).K);
               BQ_J := BQ_J + T (T'First + I).K;
            end if;
            pragma Loop_Invariant
              (Proof_Only => Same (BQ_J, BQ.W_Sum (T.all, I + 1, 0, 0, 0)));
         end loop;
         if Tab then
            BQ.Lemma_Inv_At
              (T.all, NT, BQ.Bound_Array (C.Terms (First .. Last), Logv, Cur0,
                                          Cur1, Alpha, Beta),
               Nxt0, Logw, Nxt1, Logw, 0, 0);
            BQ.Lemma_Hands_Below (C.Terms (First .. Last), NW, Logw);
            BQ.Lemma_V_End
              (BQ.Bound_Array (C.Terms (First .. Last), Logv, Cur0, Cur1,
                               Alpha, Beta), C.Terms (First .. Last),
               Last - First + 1, Logv, Cur0, Cur1, Nxt0, Nxt1, Logw,
               Alpha, Beta);
         end if;
         pragma Assert
           (Proof_Only =>
              (if Tab
               then Same (BQ_J,
                          ST.SA.EBQT_Ref (C.Terms (First .. Last),
                                          Last - First + 1, Logv,
                                          Cur0, Cur1, Nxt0, Nxt1, Logw,
                                          Alpha, Beta))));
         --  The bound quad of the layer: the terms left at hands (0, 0)
         --  when the tables fit, term by term otherwise, as the verifier.
         pragma Assert
           (Proof_Only =>
              (for all R in 0 .. Logw - 1 =>
                 Same (Nxt0 (R), Ch.Layer (Off_C + 2 + 2 * R))));
         pragma Assert
           (Proof_Only =>
              (for all R in 0 .. Logw - 1 =>
                 Same (Nxt1 (R), Ch.Layer (Off_C + 2 + 2 * R + 1))));
         ST.SV.Lemma_Layer_G_Frame (S, Ch_In, Ch, J);
         pragma Assert
           (Proof_Only =>
              (for all R in 0 .. Logv - 1 =>
                 Same (Cur0 (R), ST.SV.Layer_G (S, Ch, J, 0) (R))
                 and then Same (Cur1 (R), ST.SV.Layer_G (S, Ch, J, 1) (R))));
         if Tab then
            BQJ := BQ_J;
         else
            BQJ := ST.SA.Eval_Bound_Quad
              (C.Terms (First .. Last), Logv, Cur0, Cur1, Nxt0, Nxt1, Logw,
               Alpha, Beta);
         end if;
         ST.SV.Lemma_BQ_Ref_From
           (C, Ch, J, Logv, Cur0, Cur1, Nxt0, Nxt1, BQJ);
         Cl0 := Ref (A0.all, N0, 0);
         Cl1 := Ref (A1.all, N1, 0);
         P0  := Cl0 - Pads (Off_D + 4 * Logw);
         P2V := Cl1 - Pads (Off_D + 4 * Logw + 1);
         Proof.Evals (Off_P + 4 * Logw)     := P0;
         Proof.Evals (Off_P + 4 * Logw + 1) := P2V;
         ST.End_Layer (P0, P2V);
         Logv := Logw;
         Cur0 := Nxt0;
         Cur1 := Nxt1;
         ST.SV.Lemma_Hand_Chal (S, Ch, J, 0, Cur0);
         ST.SV.Lemma_Hand_Chal (S, Ch, J, 1, Cur1);
         Free_Terms (T);
         Free_Elems (A0);
         Free_Elems (A1);
         Free_Elems (B0);
         Free_Elems (B1);
         Free_Elems (Q);
      end;
   end Prove_Layer;

   procedure Prove
     (C     : Circuit;
      Wires : Element_Array;
      Pads  : Element_Array;
      Proof : out Sumcheck_Proof;
      Ch    : out Challenges;
      BQ    : out Element_Array)
   is
      S    : constant Shape := Shape_Of (C);
      Logv : Natural := ST.SV.Ceil_Lg2 (C.Noutput);
      Cur0, Cur1 : Element_Array (0 .. Max_Logw - 1);
      Nxt0, Nxt1 : Element_Array (0 .. Max_Logw - 1) := [others => Zero];
      --  The unpadded claims of the previous layer, zero before the
      --  first (prover.rs, prove_core).
      Cl0, Cl1 : Element := Zero;
   begin
      Proof := (Last => Proof.Last, Evals => [others => Zero]);
      Ch := (Last        => Ch.Last,
             G           => [others => Zero],
             Layer       => [others => Zero],
             Alpha_Input => Zero);
      ST.Begin_Circuit (Ch.G);
      BQ := [others => Zero];
      Cur0 := Ch.G;
      Cur1 := Ch.G;
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant (Logv <= Max_Logw);
         pragma Loop_Invariant (Proof.Last + 1 = ST.SV.Proof_Total (S));
         pragma Loop_Invariant (Ch.Last + 1 = ST.SV.Chal_Total (S));
         pragma Loop_Invariant
           (Proof_Only =>
              Logv = ST.SV.Layer_Logv (S, J)
              and then (for all R in 0 .. Logv - 1 =>
                          Same (Cur0 (R), ST.SV.Layer_G (S, Ch, J, 0) (R))
                          and then
                          Same (Cur1 (R), ST.SV.Layer_G (S, Ch, J, 1) (R)))
              and then (for all J2 in 0 .. J - 1 =>
                          Same (BQ (J2), ST.SV.BQ_Ref (C, Ch, J2))));
         declare
            Ch_Before : constant Challenges := Ch with Ghost => Proof_Only;
         begin
            Prove_Layer (C, J, Wires, Pads, Logv, Cur0, Cur1, Nxt0, Nxt1,
                         Cl0, Cl1, Proof, Ch, BQ (J));
            ST.SV.Lemma_BQ_Ref_Frame_All (C, Ch, Ch_Before, J);
         end;
      end loop;
      declare
         Ch_Before : constant Challenges := Ch with Ghost => Proof_Only;
      begin
         ST.Sample (Ch.Alpha_Input);
         ST.SV.Lemma_BQ_Ref_Frame_All (C, Ch, Ch_Before, C.Last_Layer + 1);
      end;
   end Prove;

end Sumcheck_Prover;
