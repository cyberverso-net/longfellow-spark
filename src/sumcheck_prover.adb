pragma SPARK_Mode (On);

with Interfaces;

with Ada.Unchecked_Deallocation;

package body Sumcheck_Prover is

   --  The predicate of Circuit is checked where a circuit enters the
   --  program. Inside this body every predicate check is proved by
   --  GNATprove, and the property does not depend on the formal Fill.
   --  The instances for the command line, compiled with checks (ADR
   --  0068), would otherwise scan the whole circuit at every call that
   --  passes it, once per layer.
   pragma Suppress (Predicate_Check);

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

   procedure Lemma_Chal_Step (C : Circuit; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => J <= C.Last_Layer,
     Post   => ST.SV.Chal_Off (C, J + 1)
               = ST.SV.Chal_Off (C, J) + ST.SV.Chal_Size (C, J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         ST.SV.Chal_Off);
   begin
      null;
   end Lemma_Chal_Step;

   procedure Lemma_Chal_Mono (C : Circuit; I, J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => I <= J and then J <= C.Last_Layer + 1,
     Post   => ST.SV.Chal_Off (C, I) <= ST.SV.Chal_Off (C, J),
     Subprogram_Variant => (Decreases => J)
   is
   begin
      if J > I then
         Lemma_Chal_Step (C, J - 1);
         Lemma_Chal_Mono (C, I, J - 1);
      end if;
   end Lemma_Chal_Mono;

   procedure Lemma_Proof_Step (C : Circuit; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => J <= C.Last_Layer,
     Post   => ST.SV.Proof_Off (C, J + 1)
               = ST.SV.Proof_Off (C, J) + ST.SV.Proof_Size (C, J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         ST.SV.Proof_Off);
   begin
      null;
   end Lemma_Proof_Step;

   procedure Lemma_Proof_Mono (C : Circuit; I, J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => I <= J and then J <= C.Last_Layer + 1,
     Post   => ST.SV.Proof_Off (C, I) <= ST.SV.Proof_Off (C, J),
     Subprogram_Variant => (Decreases => J)
   is
   begin
      if J > I then
         Lemma_Proof_Step (C, J - 1);
         Lemma_Proof_Mono (C, I, J - 1);
      end if;
   end Lemma_Proof_Mono;

   --  Layer J's blocks lie within the three totals.
   procedure Lemma_Layer_Fits (C : Circuit; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => J <= C.Last_Layer,
     Post   => ST.SV.Chal_Off (C, J) + ST.SV.Chal_Size (C, J)
               <= ST.SV.Chal_Total (C)
               and then ST.SV.Proof_Off (C, J) + ST.SV.Proof_Size (C, J)
                        <= ST.SV.Proof_Total (C)
               and then ST.SV.Pad_Off (C, J, 0) + ST.SV.Pad_Size (C, J)
                        <= Pad_Total (C)
   is
   begin
      Lemma_Chal_Step (C, J);
      Lemma_Chal_Mono (C, J + 1, C.Last_Layer + 1);
      Lemma_Proof_Step (C, J);
      Lemma_Proof_Mono (C, J + 1, C.Last_Layer + 1);
      ST.SV.Lemma_Pad_Step (C, J, 0);
      ST.SV.Lemma_Pad_Mono (C, J + 1, C.Last_Layer + 1, 0);
   end Lemma_Layer_Fits;

   --  The input wires of layer J are segment J + 1 of the wires buffer.
   procedure Lemma_Segment (C : Circuit; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => J <= C.Last_Layer,
     Post   => ST.SA.Off (C, J + 1) + C.Layers (J).NW_In
               <= ST.SA.Total_Wires (C)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", ST.SA.Off);
   begin
      --  Off (C, J + 2) = Off (C, J + 1) + Seg_Size (C, J + 1), with
      --  Seg_Size (C, J + 1) = NW_In of layer J, and Off is monotonic
      --  up to Total_Wires = Off (C, Last_Layer + 2).
      for K in J + 2 .. C.Last_Layer + 2 loop
         pragma Loop_Invariant
           (ST.SA.Off (C, J + 1) + C.Layers (J).NW_In <= ST.SA.Off (C, K));
      end loop;
   end Lemma_Segment;

   -------------------------------------------------------------------
   --  Sample_Pads
   -------------------------------------------------------------------

   procedure Sample_Pads (C : Circuit; Pads : out Element_Array) is
      C0, C1 : Element;
   begin
      Pads := [others => Zero];
      for J in 0 .. C.Last_Layer loop
         Lemma_Layer_Fits (C, J);
         declare
            Off  : constant Natural := ST.SV.Pad_Off (C, J, 0);
            Logw : constant Logw_Type := C.Layers (J).Logw;
         begin
            for R in 0 .. Logw - 1 loop
               pragma Loop_Invariant
                 (Off + ST.SV.Pad_Size (C, J) <= Pads'Length);
               for K in 0 .. 3 loop
                  pragma Loop_Invariant
                    (Off + ST.SV.Pad_Size (C, J) <= Pads'Length);
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

   procedure Lqc_Triples (C : Circuit; Lqc : out ST.SV.Lqc_Array) is
      Base : constant Natural := C.Ninput - C.Npublic;
      Pi   : Natural := Base;
   begin
      Lqc := [others => (X => 0, Y => 0, Z => 0)];
      ST.SV.Lemma_Pads_Below (C);
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant (Pi = ST.SV.Pad_Off (C, J, Base));
         pragma Loop_Invariant
           (for all J2 in 0 .. J - 1 =>
              Lqc (J2) = (X => ST.SV.Pad_Off (C, J2, Base)
                                 + 4 * C.Layers (J2).Logw,
                          Y => ST.SV.Pad_Off (C, J2, Base)
                                 + 4 * C.Layers (J2).Logw + 1,
                          Z => ST.SV.Pad_Off (C, J2, Base)
                                 + 4 * C.Layers (J2).Logw + 2));
         Lqc (J) := (X => Pi + 4 * C.Layers (J).Logw,
                     Y => Pi + 4 * C.Layers (J).Logw + 1,
                     Z => Pi + 4 * C.Layers (J).Logw + 2);
         ST.SV.Lemma_Pad_Step (C, J, Base);
         Pi := Pi + 4 * C.Layers (J).Logw + 3;
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
   --  The round evaluations from three sums, three products per pair
   --  (ADR 0070): a0 = sum q0 w0, s1 = sum q1 w1 and a2 = sum dq dw,
   --  with dq = q1 - q0 and dw = w1 - w0. Each pair contributes
   --  (q0 + x dq) (w0 + x dw) = a0 + x (s1 - a0 - a2) + x^2 a2 to p (x),
   --  and the combination is additive, so p (P2) is Comb of the sums.
   --  These identities are the Lemma_Comb_*_F of Sumcheck_Algebra,
   --  proved in Ring_Laws on the hidden wrappers.
   -------------------------------------------------------------------

   function Comb (X, A0, S1, A2 : Element) return Element
     renames ST.SA.Comb_F;

   --  p (1) over the first M pairs.
   function D1_Ref
     (QW : Element_Array; A : Element_Array; NA : Natural; M : Natural)
      return Element
   is
     (if M = 0 then Zero
      else D1_Ref (QW, A, NA, M - 1)
           + Ref (QW, NA, 2 * M - 1) * Ref (A, NA, 2 * M - 1))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => QW'First = 0 and then A'First = 0
               and then NA <= QW'Length and then NA <= A'Length
               and then M <= Natural'Last / 2,
        Subprogram_Variant => (Decreases => M);

   --  The leading coefficient over the first M pairs.
   function Dd_Ref
     (QW : Element_Array; A : Element_Array; NA : Natural; M : Natural)
      return Element
   is
     (if M = 0 then Zero
      else Dd_Ref (QW, A, NA, M - 1)
           + (Ref (QW, NA, 2 * M - 1) - Ref (QW, NA, 2 * (M - 1)))
             * (Ref (A, NA, 2 * M - 1) - Ref (A, NA, 2 * (M - 1))))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => QW'First = 0 and then A'First = 0
               and then NA <= QW'Length and then NA <= A'Length
               and then M <= Natural'Last / 2,
        Subprogram_Variant => (Decreases => M);

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
      QW     : in out Element_Array;
      Ev0    : out Element;
      Ev2    : out Element)
   is
      Hb : Natural;
      Q0, Q1, W0, W1 : Element;
      S1, A2 : Element;
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

      --  The pairs: the three sums, three products per pair, then
      --  p (P2) from them (prover.rs, quad_round_poly; ADR 0070).
      Ev0 := Zero;
      S1  := Zero;
      A2  := Zero;
      Lemma_D_Zero (QW, Active, NA, X2);
      Lemma_D13_Step (QW, Active, NA, 0);
      for M in 0 .. (NA + 1) / 2 - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              Same (Ev0, D0_Ref (QW, Active, NA, M))
              and then Same (S1, D1_Ref (QW, Active, NA, M))
              and then Same (A2, Dd_Ref (QW, Active, NA, M)));
         Q0 := Ref (QW, NA, 2 * M);
         Q1 := Ref (QW, NA, 2 * M + 1);
         W0 := Ref (Active, NA, 2 * M);
         W1 := Ref (Active, NA, 2 * M + 1);
         Ev0 := Ev0 + Q0 * W0;
         S1  := S1 + Q1 * W1;
         A2  := A2 + (Q1 - Q0) * (W1 - W0);
         Lemma_D_Step (QW, Active, NA, X2, M + 1);
         Lemma_D13_Step (QW, Active, NA, M + 1);
      end loop;
      Ev2 := Comb (X2, Ev0, S1, A2);
      Lemma_D2_Split (QW, Active, NA, X2, (NA + 1) / 2);
   end Round_Evals_Dense;

   procedure Bind_G_T (T : in out Term_Array; E : Element_Array;
                       Beta : Element)
   is
      EG : Element;
   begin
      for I in T'Range loop
         pragma Loop_Invariant
           (for all J in T'First .. I - 1 =>
              Same (T (J).K,
                    (if T'Loop_Entry (J).K = Zero
                     then Beta * Ref (E, E'Length, T'Loop_Entry (J).G)
                     else T'Loop_Entry (J).K
                          * Ref (E, E'Length, T'Loop_Entry (J).G)))
              and then T (J).G = 0
              and then T (J).H0 = T'Loop_Entry (J).H0
              and then T (J).H1 = T'Loop_Entry (J).H1);
         pragma Loop_Invariant
           (for all J in I .. T'Last => T (J) = T'Loop_Entry (J));
         EG := Ref (E, E'Length, T (I).G);
         if T (I).K = Zero then
            T (I).K := Beta * EG;
         else
            T (I).K := T (I).K * EG;
         end if;
         T (I).G := 0;
      end loop;
   end Bind_G_T;

   --  The same term: the same hands and output wire, the same
   --  coefficient by Same (the equality of the field may not be the
   --  logical one).
   function Same_Term (A, B : Term) return Boolean is
     (Same (A.K, B.K) and then A.G = B.G
      and then A.H0 = B.H0 and then A.H1 = B.H1)
   with Ghost => Proof_Only, Global => null;

   procedure Lemma_Run_Id_Zero (T : Term_Array)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => T'Length >= 1,
     Post   => Run_Id (T, 0) = 0
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Run_Id);
   begin
      null;
   end Lemma_Run_Id_Zero;

   procedure Lemma_Run_Id_Step (T : Term_Array; I : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => I >= 1 and then I < T'Length,
     Post   =>
       Run_Id (T, I)
       = (if Same_Hands (T (T'First + I - 1), T (T'First + I))
          then Run_Id (T, I - 1)
          else Run_Id (T, I - 1) + 1)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Run_Id);
   begin
      null;
   end Lemma_Run_Id_Step;

   procedure Lemma_Run_Sum_Step (T : Term_Array; N : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N >= 1 and then N <= T'Length,
     Post   =>
       (for all X in Natural =>
          Same (Run_Sum (T, X, N),
                (if Run_Id (T, N - 1) = X
                 then Run_Sum (T, X, N - 1) + T (T'First + N - 1).K
                 else Run_Sum (T, X, N - 1))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Run_Sum);
   begin
      null;
   end Lemma_Run_Sum_Step;

   --  A run not reached yet has the coefficient zero.
   procedure Lemma_Run_Sum_Zero (T : Term_Array; X : Natural; N : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N <= T'Length
               and then (N = 0 or else X > Run_Id (T, N - 1)),
     Post   => Same (Run_Sum (T, X, N), Zero),
     Subprogram_Variant => (Decreases => N)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Run_Sum);
   begin
      if N >= 1 then
         if N >= 2 then
            Lemma_Run_Id_Step (T, N - 1);
         end if;
         Lemma_Run_Sum_Zero (T, X, N - 1);
      end if;
   end Lemma_Run_Sum_Zero;

   procedure Merge_Runs (T : in out Term_Array; N : out Natural) is
      T0 : constant Term_Array := T with Ghost => Proof_Only;
      W  : Natural := 0;
   begin
      if T'Length = 0 then
         N := 0;
         return;
      end if;
      Lemma_Run_Id_Zero (T0);
      Lemma_Run_Sum_Zero (T0, 0, 0);
      Lemma_Run_Sum_Step (T0, 1);
      T (T'First).K := Zero + T (T'First).K;
      for I in 1 .. T'Length - 1 loop
         pragma Loop_Invariant (W <= I - 1);
         pragma Loop_Invariant (Proof_Only => W = Run_Id (T0, I - 1));
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J in I .. T'Length - 1 =>
                 Same_Term (T (T'First + J), T0 (T'First + J))));
         pragma Loop_Invariant
           (Proof_Only =>
              Same_Hands (T (T'First + W), T0 (T'First + I - 1)));
         pragma Loop_Invariant
           (Proof_Only =>
              (for all X in 0 .. W =>
                 Same (T (T'First + X).K, Run_Sum (T0, X, I))));
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J in 0 .. I - 1 =>
                 Run_Id (T0, J) <= W
                 and then Same_Hands (T (T'First + Run_Id (T0, J)),
                                      T0 (T'First + J))));
         pragma Assert
           (Proof_Only => Same_Term (T (T'First + I), T0 (T'First + I)));
         Lemma_Run_Id_Step (T0, I);
         Lemma_Run_Sum_Step (T0, I + 1);
         if Same_Hands (T (T'First + W), T (T'First + I)) then
            pragma Assert (Proof_Only => Run_Id (T0, I) = W);
            pragma Assert
              (Proof_Only =>
                 Same (Run_Sum (T0, W, I + 1),
                       Run_Sum (T0, W, I) + T0 (T'First + I).K));
            declare
               V : constant Element :=
                 T (T'First + W).K + T (T'First + I).K;
            begin
               pragma Assert
                 (Proof_Only => Same (V, Run_Sum (T0, W, I + 1)));
               T (T'First + W).K := V;
            end;
            pragma Assert
              (Proof_Only =>
                 (for all J in I + 1 .. T'Length - 1 =>
                    Same_Term (T (T'First + J), T0 (T'First + J))));
            pragma Assert
              (Proof_Only =>
                 Same (T (T'First + W).K, Run_Sum (T0, W, I + 1)));
            pragma Assert
              (Proof_Only =>
                 (for all X in 0 .. W - 1 =>
                    Same (T (T'First + X).K, Run_Sum (T0, X, I + 1))));
         else
            W := W + 1;
            pragma Assert (Proof_Only => Run_Id (T0, I) = W);
            Lemma_Run_Sum_Zero (T0, W, I);
            pragma Assert
              (Proof_Only =>
                 Same (Run_Sum (T0, W, I + 1),
                       Zero + T0 (T'First + I).K));
            declare
               V : constant Element := Zero + T (T'First + I).K;
            begin
               pragma Assert
                 (Proof_Only => Same (V, Run_Sum (T0, W, I + 1)));
               T (T'First + W) := (K  => V,
                                   G  => T (T'First + I).G,
                                   H0 => T (T'First + I).H0,
                                   H1 => T (T'First + I).H1);
            end;
            pragma Assert
              (Proof_Only =>
                 (for all J in I + 1 .. T'Length - 1 =>
                    Same_Term (T (T'First + J), T0 (T'First + J))));
            pragma Assert
              (Proof_Only =>
                 Same (T (T'First + W).K, Run_Sum (T0, W, I + 1)));
            pragma Assert
              (Proof_Only =>
                 (for all X in 0 .. W - 1 =>
                    Same (T (T'First + X).K, Run_Sum (T0, X, I + 1))));
         end if;
      end loop;
      N := W + 1;
   end Merge_Runs;

   procedure Lemma_Rd_Zero (T : Term_Array; H : Hand)
   with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Rd (T, H, 0) = 0
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Rd);
   begin
      null;
   end Lemma_Rd_Zero;

   procedure Lemma_Rd_Step (T : Term_Array; H : Hand; K : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => K >= 1,
     Post   =>
       Rd (T, H, K)
       = (if Rd (T, H, K - 1) >= T'Length then Rd (T, H, K - 1)
          elsif Two (T, Rd (T, H, K - 1), H) then Rd (T, H, K - 1) + 2
          else Rd (T, H, K - 1) + 1)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Rd);
   begin
      null;
   end Lemma_Rd_Step;

   --  Two and Corner_K read only the terms at P and P + 1.
   procedure Lemma_Corner_Frame
     (T, T0 : Term_Array; P : Natural; H : Hand; R : Element)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => T'First = T0'First and then T'Length = T0'Length
               and then P < T'Length
               and then Same_Term (T (T'First + P), T0 (T0'First + P))
               and then (if P + 1 < T'Length
                         then Same_Term (T (T'First + P + 1),
                                         T0 (T0'First + P + 1))),
     Post   => Two (T, P, H) = Two (T0, P, H)
               and then Same (Corner_K (T, P, H, R), Corner_K (T0, P, H, R))
   is
   begin
      null;
   end Lemma_Corner_Frame;

   procedure Bind_H (T : in out Term_Array; H : Hand; R : Element;
                     N : out Natural)
   is
      T0 : constant Term_Array := T with Ghost => Proof_Only;
      P  : Natural := 0;
      W  : Natural := 0;
      Tm : Term;
   begin
      Lemma_Rd_Zero (T0, H);
      while P < T'Length loop
         pragma Loop_Invariant (W <= P and then P <= T'Length);
         pragma Loop_Invariant
           (Proof_Only =>
              Rd (T0, H, W) = P
              and then
              (for all J in P .. T'Length - 1 =>
                 Same_Term (T (T'First + J), T0 (T'First + J)))
              and then
              (for all K in 0 .. W - 1 =>
                 Rd (T0, H, K) < T'Length
                 and then
                 Same (T (T'First + K).K,
                       Corner_K (T0, Rd (T0, H, K), H, R))
                 and then
                 Hand_Index (T (T'First + K), H)
                 = Hand_Index (T0 (T'First + Rd (T0, H, K)), H) / 2
                 and then
                 Hand_Index (T (T'First + K), 1 - H)
                 = Hand_Index (T0 (T'First + Rd (T0, H, K)), 1 - H)));
         pragma Loop_Variant (Increases => P);
         pragma Assert
           (Proof_Only => Same_Term (T (T'First + P), T0 (T'First + P)));
         if P + 1 < T'Length then
            declare
               Q : constant Natural := P + 1 with Ghost => Proof_Only;
            begin
               pragma Assert
                 (Proof_Only =>
                    Same_Term (T (T'First + Q), T0 (T'First + Q)));
            end;
         end if;
         Lemma_Corner_Frame (T, T0, P, H, R);
         Tm := T (T'First + P);
         Tm.K := Corner_K (T, P, H, R);
         if H = 0 then
            Tm.H0 := Tm.H0 / 2;
         else
            Tm.H1 := Tm.H1 / 2;
         end if;
         Lemma_Rd_Step (T0, H, W + 1);
         if Two (T, P, H) then
            P := P + 2;
         else
            P := P + 1;
         end if;
         T (T'First + W) := Tm;
         W := W + 1;
      end loop;
      --  The halved hand of the postcondition, from the invariant on
      --  its own, as a smaller goal than the whole conjunction.
      pragma Assert
        (Proof_Only =>
           (for all K in 0 .. W - 1 =>
              Hand_Index (T (T'First + K), H)
              = Hand_Index (T0 (T'First + Rd (T0, H, K)), H) / 2));
      N := W;
   end Bind_H;

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

   --  ceil_lg2 of the reference: 0 for N <= 1, else the least K with
   --  2^K >= N; bounded by Max_Logw for a well-formed circuit's widths
   --  by the caller's use (Noutput <= Max_Wires = 2^24).
   -------------------------------------------------------------------
   --  The bound quad of a layer (ADR 0071). The coefficients of the
   --  terms, summed by hands, are kept round by round: Bind_G_T and
   --  Merge_Runs give the sums of Bound_KT, each Bind_H turns the low
   --  bit of a hand into the factor of its challenge. After the last
   --  round the sum at hands (0, 0) is EBQT_Ref.
   -------------------------------------------------------------------

   --  The sums are taken with the wrappers of Sumcheck_Algebra, so that
   --  the contracts of the field stay out of these proofs.
   package BQ with Ghost => Proof_Only is

      function "+" (A, B : Element) return Element renames ST.SA."+";
      function "-" (A, B : Element) return Element renames ST.SA."-";
      function "*" (A, B : Element) return Element renames ST.SA."*";

      subtype U64 is Interfaces.Unsigned_64;
      use type U64;
      function Shl (V : U64; N : Natural) return U64
        renames Interfaces.Shift_Left;

      --  The factor of challenge C for the low bit of X.
      function Fac (X : Natural; C : Element) return Element is
        (if X mod 2 = 0 then One - C else C)
      with Ghost => Proof_Only, Global => null;

      --  X without its K low bits.
      function Shr (X : Natural; K : Natural) return Natural is
        (if K = 0 then X else Shr (X, K - 1) / 2)
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Post => Shr'Result <= X,
           Subprogram_Variant => (Decreases => K);

      --  The factors of C (0 .. R - 1) for the low R bits of X, the low
      --  bit with C (0) first, as Bindeq_Ref reads them.
      function Pre_F (C : Element_Array; R : Natural; X : Natural)
         return Element
      is
        (if R = 0 then One
         else Pre_F (C, R - 1, X) * Fac (Shr (X, R - 1), C (R - 1)))
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Pre => C'First = 0 and then R <= C'Length,
           Subprogram_Variant => (Decreases => R);

      --  The sum of the coefficients of the first N terms whose hand H is
      --  A and whose other hand is B.
      function W_Sum (T : Term_Array; N : Natural; H : Hand; A, B : Natural)
         return Element
      is
        (if N = 0 then Zero
         elsif Hand_Index (T (T'First + N - 1), H) = A
           and then Hand_Index (T (T'First + N - 1), 1 - H) = B
         then W_Sum (T, N - 1, H, A, B) + T (T'First + N - 1).K
         else W_Sum (T, N - 1, H, A, B))
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Pre => N <= T'Length,
           Subprogram_Variant => (Decreases => N);

      --  The sum, over the first N terms whose hands without their R0 and
      --  R1 low bits are A and B, of the coefficient times the factors of
      --  the challenges C0 (0 .. R0 - 1) and C1 (0 .. R1 - 1).
      function V_Sum
        (T  : Term_Array;
         N  : Natural;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural) return Element
      is
        (if N = 0 then Zero
         elsif Shr (T (T'First + N - 1).H0, R0) = A
           and then Shr (T (T'First + N - 1).H1, R1) = B
         then V_Sum (T, N - 1, C0, R0, C1, R1, A, B)
              + (T (T'First + N - 1).K
                 * Pre_F (C0, R0, T (T'First + N - 1).H0))
                * Pre_F (C1, R1, T (T'First + N - 1).H1)
         else V_Sum (T, N - 1, C0, R0, C1, R1, A, B))
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Pre => N <= T'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length,
           Subprogram_Variant => (Decreases => N);

      --  The coefficient of the corner read at P, bound at R, in the
      --  form of the wrappers: Corner_K, with the affine interpolation
      --  written (1 - R) k0 + R k1.
      function Corner_W (T : Term_Array; P : Natural; H : Hand; R : Element)
         return Element
      is
        (if Two (T, P, H)
         then (One - R) * T (T'First + P).K + R * T (T'First + P + 1).K
         elsif Hand_Index (T (T'First + P), H) mod 2 = 0
         then (One - R) * T (T'First + P).K
         else R * T (T'First + P).K)
      with Ghost => Proof_Only, Global => null,
           Pre => P < T'Length;

      --  Run_Sum with the wrapper addition.
      function Run_Sum_W (T : Term_Array; X : Natural; N : Natural)
         return Element
      is
        (if N = 0 then Zero
         elsif Run_Id (T, N - 1) = X
         then Run_Sum_W (T, X, N - 1) + T (T'First + N - 1).K
         else Run_Sum_W (T, X, N - 1))
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Pre => N <= T'Length,
           Subprogram_Variant => (Decreases => N);

      procedure Lemma_Corner_To_W
        (T : Term_Array; P : Natural; H : Hand; R : Element)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => P < T'Length,
        Post   => Same (Corner_K (T, P, H, R), Corner_W (T, P, H, R));

      --  The postcondition of Bind_H, its corners in the wrapper form.
      procedure Lemma_Corners_W
        (Old, New_T : Term_Array;
         H          : Hand;
         R          : Element;
         NB         : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    =>
          New_T'First = Old'First and then New_T'Length = Old'Length
          and then NB <= New_T'Length
          and then
          (for all K in 0 .. NB - 1 =>
             Rd (Old, H, K) < Old'Length
             and then
             Same (New_T (New_T'First + K).K,
                   Corner_K (Old, Rd (Old, H, K), H, R))),
        Post   =>
          (for all K in 0 .. NB - 1 =>
             Same (New_T (New_T'First + K).K,
                   Corner_W (Old, Rd (Old, H, K), H, R)));

      procedure Lemma_Run_Sum_W (T : Term_Array; X : Natural; N : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length,
        Post   => Same (Run_Sum (T, X, N), Run_Sum_W (T, X, N)),
        Subprogram_Variant => (Decreases => N);

      --  The postcondition of Merge_Runs, its sums in the wrapper form.
      procedure Lemma_Run_Sums_W (Tm, T1 : Term_Array; NT : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    =>
          NT <= Tm'Length
          and then
          (for all X in 0 .. NT - 1 =>
             Same (Tm (Tm'First + X).K, Run_Sum (T1, X, T1'Length))),
        Post   =>
          (for all X in 0 .. NT - 1 =>
             Same (Tm (Tm'First + X).K, Run_Sum_W (T1, X, T1'Length)));

      procedure Lemma_Run_Sum_W_Step (T : Term_Array; N : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N >= 1 and then N <= T'Length,
        Post   =>
          (for all X in Natural =>
             Same (Run_Sum_W (T, X, N),
                   (if Run_Id (T, N - 1) = X
                    then Run_Sum_W (T, X, N - 1) + T (T'First + N - 1).K
                    else Run_Sum_W (T, X, N - 1))));

      --  A run not reached yet has the coefficient zero.
      procedure Lemma_Run_Sum_W_Zero (T : Term_Array; X : Natural; N : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length
                  and then (N = 0 or else X > Run_Id (T, N - 1)),
        Post   => Same (Run_Sum_W (T, X, N), Zero),
        Subprogram_Variant => (Decreases => N);

      procedure Lemma_Shr_Step (X : Natural; K : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => K < Natural'Last,
        Post   => Shr (X, 0) = X and then Shr (X, K + 1) = Shr (X, K) / 2;

      procedure Lemma_Pre_Step (C : Element_Array; R : Natural; X : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => C'First = 0 and then R < C'Length,
        Post   => Same (Pre_F (C, 0, X), One)
                  and then Same (Pre_F (C, R + 1, X),
                                 Pre_F (C, R, X) * Fac (Shr (X, R), C (R)));

      procedure Lemma_Pre_Zero (C : Element_Array; X : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => C'First = 0,
        Post   => Same (Pre_F (C, 0, X), One);

      --  The hand H = 1 sums are the hand 0 sums with A and B swapped.
      procedure Lemma_W_Swap (T : Term_Array; N : Natural; A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length,
        Post   => Same (W_Sum (T, N, 1, A, B), W_Sum (T, N, 0, B, A)),
        Subprogram_Variant => (Decreases => N);

      --  A sum at a hand index no wire reaches is zero.
      procedure Lemma_W_Out (T : Term_Array; N : Natural; H : Hand;
                             A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length and then A >= ST.SA.Max_Wires,
        Post   => Same (W_Sum (T, N, H, A, B), Zero),
        Subprogram_Variant => (Decreases => N);

      procedure Lemma_V_Out
        (T  : Term_Array;
         N  : Natural;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length
                  and then (A >= ST.SA.Max_Wires or else B >= ST.SA.Max_Wires),
        Post   => Same (V_Sum (T, N, C0, R0, C1, R1, A, B), Zero),
        Subprogram_Variant => (Decreases => N);

      --  One step of Lemma_Bind_H_Sum: the merged term K - 1 and the one
      --  or two corners it reads.
      procedure Lemma_Bind_H_Step
        (T0, T : Term_Array;
         H     : Hand;
         R     : Element;
         K     : Natural;
         A, B  : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    =>
          T'First = T0'First and then T'Length = T0'Length
          and then K >= 1 and then K <= T'Length
          and then A < ST.SA.Max_Wires
          and then Rd (T0, H, K - 1) < T0'Length
          and then
          Same (T (T'First + K - 1).K, Corner_W (T0, Rd (T0, H, K - 1), H, R))
          and then
          Hand_Index (T (T'First + K - 1), H)
          = Hand_Index (T0 (T0'First + Rd (T0, H, K - 1)), H) / 2
          and then
          Hand_Index (T (T'First + K - 1), 1 - H)
          = Hand_Index (T0 (T0'First + Rd (T0, H, K - 1)), 1 - H)
          and then
          Same (W_Sum (T, K - 1, H, A, B),
                (One - R) * W_Sum (T0, Rd (T0, H, K - 1), H, 2 * A, B)
                + R * W_Sum (T0, Rd (T0, H, K - 1), H, 2 * A + 1, B)),
        Post   =>
          Same (W_Sum (T, K, H, A, B),
                (One - R) * W_Sum (T0, Rd (T0, H, K), H, 2 * A, B)
                + R * W_Sum (T0, Rd (T0, H, K), H, 2 * A + 1, B));

      --  One Bind_H of hand H at R, read off its postcondition: the sums
      --  of the first K merged terms are the sums of the corners they
      --  read, split by the parity of hand H.
      procedure Lemma_Bind_H_Sum
        (T0, T : Term_Array;
         H     : Hand;
         R     : Element;
         N, K  : Natural;
         A, B  : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    =>
          T'First = T0'First and then T'Length = T0'Length
          and then K <= N and then N <= T'Length
          and then A < ST.SA.Max_Wires
          and then Rd (T0, H, N) = T0'Length
          and then
          (for all J in 0 .. N - 1 =>
             Rd (T0, H, J) < T0'Length
             and then
             Same (T (T'First + J).K, Corner_W (T0, Rd (T0, H, J), H, R))
             and then
             Hand_Index (T (T'First + J), H)
             = Hand_Index (T0 (T0'First + Rd (T0, H, J)), H) / 2
             and then
             Hand_Index (T (T'First + J), 1 - H)
             = Hand_Index (T0 (T0'First + Rd (T0, H, J)), 1 - H)),
        Post   =>
          Same (W_Sum (T, K, H, A, B),
                (One - R) * W_Sum (T0, Rd (T0, H, K), H, 2 * A, B)
                + R * W_Sum (T0, Rd (T0, H, K), H, 2 * A + 1, B)),
        Subprogram_Variant => (Decreases => K);

      --  Binding hand 0 at C0 (R0) splits the sums by the parity of the
      --  hand without its R0 low bits.
      procedure Lemma_V_Step0
        (T  : Term_Array;
         N  : Natural;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length
                  and then C0'First = 0 and then R0 < C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length
                  and then A < ST.SA.Max_Wires,
        Post   =>
          Same (V_Sum (T, N, C0, R0 + 1, C1, R1, A, B),
                (One - C0 (R0)) * V_Sum (T, N, C0, R0, C1, R1, 2 * A, B)
                + C0 (R0) * V_Sum (T, N, C0, R0, C1, R1, 2 * A + 1, B)),
        Subprogram_Variant => (Decreases => N);

      procedure Lemma_V_Step1
        (T  : Term_Array;
         N  : Natural;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 < C1'Length
                  and then B < ST.SA.Max_Wires,
        Post   =>
          Same (V_Sum (T, N, C0, R0, C1, R1 + 1, A, B),
                (One - C1 (R1)) * V_Sum (T, N, C0, R0, C1, R1, A, 2 * B)
                + C1 (R1) * V_Sum (T, N, C0, R0, C1, R1, A, 2 * B + 1)),
        Subprogram_Variant => (Decreases => N);

      --  Pre_F and V_Sum read only the challenges they bind.
      procedure Lemma_Pre_Frame (C, D : Element_Array; R : Natural;
                                 X : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => C'First = 0 and then D'First = 0
                  and then R <= C'Length and then R <= D'Length
                  and then (for all I in 0 .. R - 1 => Same (C (I), D (I))),
        Post   => Same (Pre_F (C, R, X), Pre_F (D, R, X)),
        Subprogram_Variant => (Decreases => R);

      procedure Lemma_V_Frame
        (T      : Term_Array;
         N      : Natural;
         C0, D0 : Element_Array;
         R0     : Natural;
         C1, D1 : Element_Array;
         R1     : Natural;
         A      : Natural;
         B      : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length
                  and then C0'First = 0 and then D0'First = 0
                  and then R0 <= C0'Length and then R0 <= D0'Length
                  and then C1'First = 0 and then D1'First = 0
                  and then R1 <= C1'Length and then R1 <= D1'Length
                  and then (for all I in 0 .. R0 - 1 => Same (C0 (I), D0 (I)))
                  and then (for all I in 0 .. R1 - 1 => Same (C1 (I), D1 (I))),
        Post   => Same (V_Sum (T, N, C0, R0, C1, R1, A, B),
                        V_Sum (T, N, D0, R0, D1, R1, A, B)),
        Subprogram_Variant => (Decreases => N);

      --  Before any round the factors are One.
      procedure Lemma_V_W0
        (T      : Term_Array;
         N      : Natural;
         C0, C1 : Element_Array;
         A, B   : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length and then C0'First = 0 and then C1'First = 0,
        Post   => Same (V_Sum (T, N, C0, 0, C1, 0, A, B), W_Sum (T, N, 0, A,
                                                                 B)),
        Subprogram_Variant => (Decreases => N);

      --  The merged terms, by hands: the sum over the first X runs whose
      --  hands in Tm are A and B of their coefficients after the first M
      --  terms of T.
      function Z_Sum (Tm, T : Term_Array; X, M : Natural; A, B : Natural)
         return Element
      is
        (if X = 0 then Zero
         elsif Tm (Tm'First + X - 1).H0 = A
           and then Tm (Tm'First + X - 1).H1 = B
         then Z_Sum (Tm, T, X - 1, M, A, B) + Run_Sum_W (T, X - 1, M)
         else Z_Sum (Tm, T, X - 1, M, A, B))
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Pre => X <= Tm'Length and then M <= T'Length,
           Subprogram_Variant => (Decreases => X);

      --  Term M changes only the run it belongs to.
      procedure Lemma_Z_Frame (Tm, T : Term_Array; X, M : Natural; A,
                               B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => X <= Tm'Length and then M < T'Length
                  and then Run_Id (T, M) >= X,
        Post   => Same (Z_Sum (Tm, T, X, M + 1, A, B), Z_Sum (Tm, T, X, M, A,
                                                              B)),
        Subprogram_Variant => (Decreases => X);

      --  One step of Lemma_Merge_Sum: term M - 1 joins its run.
      procedure Lemma_Merge_Step
        (Tm, T : Term_Array; M : Natural; A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => M >= 2 and then M <= T'Length
                  and then Run_Id (T, M - 2) < Tm'Length
                  and then Run_Id (T, M - 1) < Tm'Length
                  and then Same_Hands (Tm (Tm'First + Run_Id (T, M - 1)),
                                       T (T'First + M - 1))
                  and then
                  Same (W_Sum (T, M - 1, 0, A, B),
                        Z_Sum (Tm, T, Run_Id (T, M - 2) + 1, M - 1, A, B)),
        Post   =>
          Same (W_Sum (T, M, 0, A, B),
                Z_Sum (Tm, T, Run_Id (T, M - 1) + 1, M, A, B));

      --  The sums by hands of the first M terms are those of their runs.
      procedure Lemma_Merge_Sum (Tm, T : Term_Array; M : Natural; A,
                                 B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => T'Length >= 1 and then M <= T'Length
                  and then Tm'Length >= Run_Id (T, T'Length - 1) + 1
                  and then
                  (for all I in 0 .. T'Length - 1 =>
                     Run_Id (T, I) < Tm'Length
                     and then Same_Hands (Tm (Tm'First + Run_Id (T, I)),
                                          T (T'First + I))),
        Post   =>
          Same (W_Sum (T, M, 0, A, B),
                Z_Sum (Tm, T, (if M = 0 then 0 else Run_Id (T, M - 1) + 1), M,
                       A, B)),
        Subprogram_Variant => (Decreases => M);

      --  After Merge_Runs the sums of the runs are those of Tm.
      procedure Lemma_Z_Tm (Tm, T : Term_Array; X : Natural; A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => X <= Tm'Length
                  and then
                  (for all Y in 0 .. X - 1 =>
                     Same (Tm (Tm'First + Y).K, Run_Sum_W (T, Y, T'Length))),
        Post   => Same (Z_Sum (Tm, T, X, T'Length, A, B), W_Sum (Tm, X, 0, A,
                                                                 B)),
        Subprogram_Variant => (Decreases => X);

      --  The factors of the low L bits are those of Bindeq_Ref.
      procedure Lemma_Pre_Bindeq (C : Element_Array; L, K : Natural;
                                  X : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => C'First = 0 and then L <= C'Length
                  and then L <= ST.SA.Max_Bindeq_Log and then K <= L,
        Post   =>
          Same (Pre_F (C, K, X) * ST.SA.Bindeq_Ref (C (0 .. L - 1), K, Shr (X,
            K)),
                ST.SA.Bindeq_Ref (C (0 .. L - 1), 0, X)),
        Subprogram_Variant => (Decreases => K);

      procedure Lemma_Pre_Beq (C : Element_Array; L : Natural; X : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => C'First = 0 and then L <= C'Length
                  and then L <= ST.SA.Max_Bindeq_Log
                  and then X < ST.SA.Table_Len (L),
        Post   => Same (Pre_F (C, L, X), ST.SA.Beq (C, L, X));

      procedure Lemma_Table_Len_Step (L : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => L >= 1 and then L <= ST.SA.Max_Bindeq_Log,
        Post   => ST.SA.Table_Len (L) = 2 * ST.SA.Table_Len (L - 1)
                  and then ST.SA.Table_Len (0) = 1;

      --  An index below 2^L has no bit left after L shifts.
      procedure Lemma_Shr_Below (X : Natural; L, K : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => K <= L and then L <= ST.SA.Max_Bindeq_Log
                  and then X < ST.SA.Table_Len (L),
        Post   => Shr (X, K) < ST.SA.Table_Len (L - K),
        Subprogram_Variant => (Decreases => K);

      --  After L rounds of both hands, the sum at hands (0, 0) is the
      --  bound quad of the layer.
      procedure Lemma_V_End
        (T1, T0 : Term_Array;
         N      : Natural;
         Logv   : Natural;
         G0, G1 : Element_Array;
         C0, C1 : Element_Array;
         L      : Natural;
         Alpha  : Element;
         Beta   : Element)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    =>
          T1'First = T0'First and then T1'Length = T0'Length
          and then N <= T0'Length
          and then G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= ST.SA.Max_Bindeq_Log
          and then C0'First = 0 and then C1'First = 0
          and then L <= C0'Length and then L <= C1'Length
          and then L <= ST.SA.Max_Bindeq_Log
          and then
          (for all I in T0'Range =>
             Same (T1 (I).K, ST.SA.Bound_KT (T0 (I), Logv, G0, G1, Alpha,
                                             Beta))
             and then T1 (I).H0 = T0 (I).H0 and then T1 (I).H1 = T0 (I).H1
             and then T0 (I).H0 < ST.SA.Table_Len (L)
             and then T0 (I).H1 < ST.SA.Table_Len (L)),
        Post   =>
          Same (V_Sum (T1, N, C0, L, C1, L, 0, 0),
                ST.SA.EBQT_Ref (T0, N, Logv, G0, G1, C0, C1, L, Alpha, Beta)),
        Subprogram_Variant => (Decreases => N);

      --  The invariant of the rounds: for every pair of hands, the sum
      --  of the coefficients of the first N terms of S equals the sum
      --  over the bound terms T1 with the factors of the challenges
      --  drawn so far.
      function Inv
        (S  : Term_Array;
         N  : Natural;
         T1 : Term_Array;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural) return Boolean
      is
        (for all A in 0 .. ST.SA.Max_Wires - 1 =>
           (for all B in 0 .. ST.SA.Max_Wires - 1 =>
              Same (W_Sum (S, N, 0, A, B),
                    V_Sum (T1, T1'Length, C0, R0, C1, R1, A, B))))
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Pre => N <= S'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length;

      procedure Lemma_Inv_At
        (S  : Term_Array;
         N  : Natural;
         T1 : Term_Array;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= S'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length
                  and then A < ST.SA.Max_Wires and then B < ST.SA.Max_Wires
                  and then Inv (S, N, T1, C0, R0, C1, R1),
        Post   => Same (W_Sum (S, N, 0, A, B),
                        V_Sum (T1, T1'Length, C0, R0, C1, R1, A, B));

      --  W_Sum reads only the first N terms.
      procedure Lemma_W_Slice (S, U : Term_Array; N : Natural; A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => S'First = U'First and then N <= S'Length
                  and then N <= U'Length
                  and then (for all I in 0 .. N - 1 =>
                              Same (S (S'First + I).K, U (U'First + I).K)
                              and then Same_Hands (S (S'First + I),
                                                   U (U'First + I))),
        Post   => Same (W_Sum (S, N, 0, A, B), W_Sum (U, N, 0, A, B)),
        Subprogram_Variant => (Decreases => N);

      procedure Lemma_Inv_Slice
        (S, U : Term_Array;
         N    : Natural;
         T1   : Term_Array;
         C0   : Element_Array;
         R0   : Natural;
         C1   : Element_Array;
         R1   : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    => S'First = U'First and then N <= S'Length
                  and then N <= U'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length
                  and then (for all I in 0 .. N - 1 =>
                              Same (S (S'First + I).K, U (U'First + I).K)
                              and then Same_Hands (S (S'First + I),
                                                   U (U'First + I)))
                  and then Inv (S, N, T1, C0, R0, C1, R1),
        Post   => Inv (U, N, T1, C0, R0, C1, R1);

      --  After Merge_Runs, before any round.
      procedure Lemma_Inv_Base
        (Tm, T1 : Term_Array;
         NT     : Natural;
         C0, C1 : Element_Array)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    => Tm'First = T1'First and then Tm'Length = T1'Length
                  and then C0'First = 0 and then C1'First = 0
                  and then NT <= Tm'Length
                  and then NT = (if T1'Length = 0 then 0
                                 else Run_Id (T1, T1'Length - 1) + 1)
                  and then
                  (for all X in 0 .. NT - 1 =>
                     Same (Tm (Tm'First + X).K, Run_Sum_W (T1, X, T1'Length)))
                  and then
                  (for all I in 0 .. T1'Length - 1 =>
                     Same_Hands (Tm (Tm'First + Run_Id (T1, I)),
                                 T1 (T1'First + I))),
        Post   => Inv (Tm, NT, T1, C0, 0, C1, 0);

      --  A challenge drawn at R0 or beyond does not change the invariant.
      procedure Lemma_Inv_Frame
        (S      : Term_Array;
         N      : Natural;
         T1     : Term_Array;
         C0, D0 : Element_Array;
         R0     : Natural;
         C1, D1 : Element_Array;
         R1     : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    => N <= S'Length
                  and then C0'First = 0 and then D0'First = 0
                  and then R0 <= C0'Length and then R0 <= D0'Length
                  and then C1'First = 0 and then D1'First = 0
                  and then R1 <= C1'Length and then R1 <= D1'Length
                  and then (for all I in 0 .. R0 - 1 => Same (C0 (I), D0 (I)))
                  and then (for all I in 0 .. R1 - 1 => Same (C1 (I), D1 (I)))
                  and then Inv (S, N, T1, C0, R0, C1, R1),
        Post   => Inv (S, N, T1, D0, R0, D1, R1);

      --  One Bind_H of hand 0 at C0 (R0), then of hand 1 at C1 (R1).
      procedure Lemma_Inv_Step0
        (Old, New_T : Term_Array;
         NB         : Natural;
         T1         : Term_Array;
         C0         : Element_Array;
         R0         : Natural;
         C1         : Element_Array;
         R1         : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    =>
          New_T'First = Old'First and then New_T'Length = Old'Length
          and then NB <= New_T'Length
          and then C0'First = 0 and then R0 < C0'Length
          and then C1'First = 0 and then R1 <= C1'Length
          and then Rd (Old, 0, NB) = Old'Length
          and then
          (for all K in 0 .. NB - 1 =>
             Rd (Old, 0, K) < Old'Length
             and then
             Same (New_T (New_T'First + K).K,
                   Corner_W (Old, Rd (Old, 0, K), 0, C0 (R0)))
             and then
             Hand_Index (New_T (New_T'First + K), 0)
             = Hand_Index (Old (Old'First + Rd (Old, 0, K)), 0) / 2
             and then
             Hand_Index (New_T (New_T'First + K), 1)
             = Hand_Index (Old (Old'First + Rd (Old, 0, K)), 1))
          and then Inv (Old, Old'Length, T1, C0, R0, C1, R1),
        Post   => Inv (New_T, NB, T1, C0, R0 + 1, C1, R1);

      procedure Lemma_Inv_Step1
        (Old, New_T : Term_Array;
         NB         : Natural;
         T1         : Term_Array;
         C0         : Element_Array;
         R0         : Natural;
         C1         : Element_Array;
         R1         : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    =>
          New_T'First = Old'First and then New_T'Length = Old'Length
          and then NB <= New_T'Length
          and then C0'First = 0 and then R0 <= C0'Length
          and then C1'First = 0 and then R1 < C1'Length
          and then Rd (Old, 1, NB) = Old'Length
          and then
          (for all K in 0 .. NB - 1 =>
             Rd (Old, 1, K) < Old'Length
             and then
             Same (New_T (New_T'First + K).K,
                   Corner_W (Old, Rd (Old, 1, K), 1, C1 (R1)))
             and then
             Hand_Index (New_T (New_T'First + K), 1)
             = Hand_Index (Old (Old'First + Rd (Old, 1, K)), 1) / 2
             and then
             Hand_Index (New_T (New_T'First + K), 0)
             = Hand_Index (Old (Old'First + Rd (Old, 1, K)), 0))
          and then Inv (Old, Old'Length, T1, C0, R0, C1, R1),
        Post   => Inv (New_T, NB, T1, C0, R0, C1, R1 + 1);

      procedure Lemma_W_Step (T : Term_Array; N : Natural; H : Hand;
                              A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N < T'Length,
        Post   =>
          Same (W_Sum (T, 0, H, A, B), Zero)
          and then
          Same (W_Sum (T, N + 1, H, A, B),
                (if Hand_Index (T (T'First + N), H) = A
                   and then Hand_Index (T (T'First + N), 1 - H) = B
                 then W_Sum (T, N, H, A, B) + T (T'First + N).K
                 else W_Sum (T, N, H, A, B)));

      procedure Lemma_W_Zero (T : Term_Array; H : Hand; A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Post   => Same (W_Sum (T, 0, H, A, B), Zero);

      --  2^L as a word.
      procedure Lemma_TL_Shift (L : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => L <= ST.SA.Max_Bindeq_Log,
        Post   => U64 (ST.SA.Table_Len (L)) = Shl (1, L),
        Subprogram_Variant => (Decreases => L);

      --  The hands of a layer that fits are below 2^Logw.
      procedure Lemma_Hands_Below (T : Term_Array; NW : Natural; L : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => L <= ST.SA.Max_Bindeq_Log
                  and then U64 (NW) <= Shl (1, L)
                  and then (for all I in T'Range =>
                              T (I).H0 < NW and then T (I).H1 < NW),
        Post   => (for all I in T'Range =>
                     T (I).H0 < ST.SA.Table_Len (L)
                     and then T (I).H1 < ST.SA.Table_Len (L));

      --  Bind_G_T with the eq2 table gives Bound_KT.
      procedure Lemma_T1_Bound
        (T0, T1 : Term_Array;
         E      : Element_Array;
         Logv   : Natural;
         G0, G1 : Element_Array;
         Alpha  : Element;
         Beta   : Element)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    =>
          T1'First = T0'First and then T1'Last = T0'Last
          and then G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= ST.SA.Max_Bindeq_Log
          and then E'First = 0 and then E'Last = ST.SA.Table_Len (Logv) - 1
          and then (for all X in E'Range =>
                      Same (E (X), ST.SA.Beq2 (X, Logv, G0, G1, Alpha)))
          and then
          (for all I in T1'Range =>
             Same (T1 (I).K,
                   (if T0 (I).K = Zero
                    then ST.SA.F."*" (Beta, Ref (E, E'Length, T0 (I).G))
                    else ST.SA.F."*" (T0 (I).K, Ref (E, E'Length, T0 (I).G))))
             and then T1 (I).H0 = T0 (I).H0
             and then T1 (I).H1 = T0 (I).H1),
        Post   =>
          (for all I in T1'Range =>
             Same (T1 (I).K,
                   ST.SA.Bound_KT (T0 (I), Logv, G0, G1, Alpha, Beta)));

      --  The terms of the layer with g bound: the coefficient Bound_KT,
      --  g zero, the same hands. The invariant of the rounds is stated on
      --  it, so that it reads only the circuit and the challenges.
      function Bound_Array
        (T0     : Term_Array;
         Logv   : Natural;
         G0, G1 : Element_Array;
         Alpha  : Element;
         Beta   : Element) return Term_Array
      is
        ([for I in T0'Range =>
            (K  => ST.SA.Bound_KT (T0 (I), Logv, G0, G1, Alpha, Beta),
             G  => 0,
             H0 => T0 (I).H0,
             H1 => T0 (I).H1)])
      with Ghost => Proof_Only,
           Global => null,
           Pre  => G0'First = 0 and then G1'First = 0
                   and then Logv <= G0'Length and then Logv <= G1'Length
                   and then Logv <= ST.SA.Max_Bindeq_Log,
           Post => Bound_Array'Result'First = T0'First
                   and then Bound_Array'Result'Last = T0'Last;

      --  V_Sum reads only the coefficients and the hands.
      procedure Lemma_V_Coef
        (T, U : Term_Array;
         N    : Natural;
         C0   : Element_Array;
         R0   : Natural;
         C1   : Element_Array;
         R1   : Natural;
         A    : Natural;
         B    : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => T'First = U'First and then N <= T'Length
                  and then N <= U'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length
                  and then
                  (for all I in 0 .. N - 1 =>
                     Same (T (T'First + I).K, U (U'First + I).K)
                     and then T (T'First + I).H0 = U (U'First + I).H0
                     and then T (T'First + I).H1 = U (U'First + I).H1),
        Post   => Same (V_Sum (T, N, C0, R0, C1, R1, A, B),
                        V_Sum (U, N, C0, R0, C1, R1, A, B)),
        Subprogram_Variant => (Decreases => N);

      procedure Lemma_Inv_Coef
        (S     : Term_Array;
         N     : Natural;
         T1, U : Term_Array;
         C0    : Element_Array;
         R0    : Natural;
         C1    : Element_Array;
         R1    : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    => T1'First = U'First and then T1'Length = U'Length
                  and then N <= S'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length
                  and then
                  (for all I in 0 .. T1'Length - 1 =>
                     Same (T1 (T1'First + I).K, U (U'First + I).K)
                     and then T1 (T1'First + I).H0 = U (U'First + I).H0
                     and then T1 (T1'First + I).H1 = U (U'First + I).H1)
                  and then Inv (S, N, T1, C0, R0, C1, R1),
        Post   => Inv (S, N, U, C0, R0, C1, R1);

   end BQ;

   package body BQ is

      procedure Lemma_Corner_To_W
        (T : Term_Array; P : Natural; H : Hand; R : Element)
      is
      begin
         if Two (T, P, H) then
            ST.SA.Lemma_Corner_Two_W
              (T (T'First + P).K, T (T'First + P + 1).K, R);
         elsif Hand_Index (T (T'First + P), H) mod 2 = 0 then
            ST.SA.Lemma_Corner_Even_W (T (T'First + P).K, R);
         else
            ST.SA.Lemma_Corner_Odd_W (T (T'First + P).K, R);
         end if;
      end Lemma_Corner_To_W;

      procedure Lemma_Corners_W
        (Old, New_T : Term_Array;
         H          : Hand;
         R          : Element;
         NB         : Natural)
      is
      begin
         for K in 0 .. NB - 1 loop
            Lemma_Corner_To_W (Old, Rd (Old, H, K), H, R);
            pragma Loop_Invariant
              (for all K2 in 0 .. K =>
                 Same (New_T (New_T'First + K2).K,
                       Corner_W (Old, Rd (Old, H, K2), H, R)));
         end loop;
      end Lemma_Corners_W;

      procedure Lemma_Run_Sum_W (T : Term_Array; X : Natural; N : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Run_Sum);
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Run_Sum_W);
      begin
         if N > 0 then
            Lemma_Run_Sum_W (T, X, N - 1);
            ST.SA.Lemma_Add_W (Run_Sum (T, X, N - 1), T (T'First + N - 1).K);
         end if;
      end Lemma_Run_Sum_W;

      procedure Lemma_Run_Sums_W (Tm, T1 : Term_Array; NT : Natural) is
      begin
         for X in 0 .. NT - 1 loop
            Lemma_Run_Sum_W (T1, X, T1'Length);
            pragma Loop_Invariant
              (for all X2 in 0 .. X =>
                 Same (Tm (Tm'First + X2).K, Run_Sum_W (T1, X2, T1'Length)));
         end loop;
      end Lemma_Run_Sums_W;

      procedure Lemma_Run_Sum_W_Step (T : Term_Array; N : Natural) is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Run_Sum_W);
      begin
         null;
      end Lemma_Run_Sum_W_Step;

      procedure Lemma_Run_Sum_W_Zero (T : Term_Array; X : Natural; N : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Run_Sum_W);
      begin
         if N >= 1 then
            if N >= 2 then
               Lemma_Run_Id_Step (T, N - 1);
            end if;
            Lemma_Run_Sum_W_Zero (T, X, N - 1);
         end if;
      end Lemma_Run_Sum_W_Zero;

      procedure Lemma_Shr_Step (X : Natural; K : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Shr);
      begin
         null;
      end Lemma_Shr_Step;

      procedure Lemma_Pre_Step (C : Element_Array; R : Natural; X : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Pre_F);
      begin
         null;
      end Lemma_Pre_Step;

      procedure Lemma_Pre_Zero (C : Element_Array; X : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Pre_F);
      begin
         null;
      end Lemma_Pre_Zero;

      procedure Lemma_W_Swap (T : Term_Array; N : Natural; A, B : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", W_Sum);
      begin
         if N > 0 then
            Lemma_W_Swap (T, N - 1, A, B);
         end if;
      end Lemma_W_Swap;

      procedure Lemma_W_Out (T : Term_Array; N : Natural; H : Hand;
                             A, B : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", W_Sum);
      begin
         if N > 0 then
            Lemma_W_Out (T, N - 1, H, A, B);
         end if;
      end Lemma_W_Out;

      procedure Lemma_V_Out
        (T  : Term_Array;
         N  : Natural;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", V_Sum);
      begin
         if N > 0 then
            Lemma_V_Out (T, N - 1, C0, R0, C1, R1, A, B);
         end if;
      end Lemma_V_Out;

      procedure Lemma_Bind_H_Step
        (T0, T : Term_Array;
         H     : Hand;
         R     : Element;
         K     : Natural;
         A, B  : Natural)
      is
         pragma Unreferenced (T);
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", W_Sum);
         P   : constant Natural := Rd (T0, H, K - 1);
         X0  : constant Natural := Hand_Index (T0 (T0'First + P), H);
         Y0  : constant Natural := Hand_Index (T0 (T0'First + P), 1 - H);
         Kp  : constant Element := T0 (T0'First + P).K;
         Wo0 : constant Element := W_Sum (T0, P, H, 2 * A, B);
         Wo1 : constant Element := W_Sum (T0, P, H, 2 * A + 1, B);
      begin
         Lemma_Rd_Step (T0, H, K);
         if Two (T0, P, H) then
            if X0 / 2 = A and then Y0 = B then
               ST.SA.RL.Lemma_Split_LR
                 (One - R, R, Wo0, Wo1, Kp, T0 (T0'First + P + 1).K);
            end if;
         elsif X0 / 2 = A and then Y0 = B then
            if X0 mod 2 = 0 then
               ST.SA.RL.Lemma_Split_L (One - R, R, Wo0, Wo1, Kp);
            else
               ST.SA.RL.Lemma_Split_R (One - R, R, Wo0, Wo1, Kp);
            end if;
         end if;
      end Lemma_Bind_H_Step;

      procedure Lemma_Bind_H_Sum
        (T0, T : Term_Array;
         H     : Hand;
         R     : Element;
         N, K  : Natural;
         A, B  : Natural)
      is
      begin
         if K = 0 then
            Lemma_Rd_Zero (T0, H);
            Lemma_W_Zero (T, H, A, B);
            Lemma_W_Zero (T0, H, 2 * A, B);
            Lemma_W_Zero (T0, H, 2 * A + 1, B);
            ST.SA.RL.Lemma_Split_Zero (One - R, R);
         else
            Lemma_Bind_H_Sum (T0, T, H, R, N, K - 1, A, B);
            Lemma_Bind_H_Step (T0, T, H, R, K, A, B);
         end if;
      end Lemma_Bind_H_Sum;

      procedure Lemma_V_Step0
        (T  : Term_Array;
         N  : Natural;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", V_Sum);
         Cr : constant Element := C0 (R0);
      begin
         if N = 0 then
            ST.SA.RL.Lemma_Split_Zero (One - Cr, Cr);
         else
            Lemma_V_Step0 (T, N - 1, C0, R0, C1, R1, A, B);
            declare
               Tm : constant Term := T (T'First + N - 1);
               X  : constant Natural := Shr (Tm.H0, R0);
               P0 : constant Element := Pre_F (C0, R0, Tm.H0);
               P1 : constant Element := Pre_F (C1, R1, Tm.H1);
               V0 : constant Element := V_Sum (T, N - 1, C0, R0, C1, R1, 2 * A,
                                               B);
               V1 : constant Element :=
                 V_Sum (T, N - 1, C0, R0, C1, R1, 2 * A + 1, B);
            begin
               Lemma_Shr_Step (Tm.H0, R0);
               Lemma_Pre_Step (C0, R0, Tm.H0);
               if X / 2 = A and then Shr (Tm.H1, R1) = B then
                  if X mod 2 = 0 then
                     ST.SA.RL.Lemma_Move_L (Tm.K, P0, One - Cr, P1);
                     ST.SA.RL.Lemma_Split_L
                       (One - Cr, Cr, V0, V1, (Tm.K * P0) * P1);
                  else
                     ST.SA.RL.Lemma_Move_L (Tm.K, P0, Cr, P1);
                     ST.SA.RL.Lemma_Split_R
                       (One - Cr, Cr, V0, V1, (Tm.K * P0) * P1);
                  end if;
               end if;
            end;
         end if;
      end Lemma_V_Step0;

      procedure Lemma_V_Step1
        (T  : Term_Array;
         N  : Natural;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", V_Sum);
         Cr : constant Element := C1 (R1);
      begin
         if N = 0 then
            ST.SA.RL.Lemma_Split_Zero (One - Cr, Cr);
         else
            Lemma_V_Step1 (T, N - 1, C0, R0, C1, R1, A, B);
            declare
               Tm : constant Term := T (T'First + N - 1);
               Y  : constant Natural := Shr (Tm.H1, R1);
               P0 : constant Element := Pre_F (C0, R0, Tm.H0);
               P1 : constant Element := Pre_F (C1, R1, Tm.H1);
               V0 : constant Element := V_Sum (T, N - 1, C0, R0, C1, R1, A,
                                               2 * B);
               V1 : constant Element :=
                 V_Sum (T, N - 1, C0, R0, C1, R1, A, 2 * B + 1);
            begin
               Lemma_Shr_Step (Tm.H1, R1);
               Lemma_Pre_Step (C1, R1, Tm.H1);
               if Shr (Tm.H0, R0) = A and then Y / 2 = B then
                  if Y mod 2 = 0 then
                     ST.SA.RL.Lemma_Move_R (Tm.K, P0, P1, One - Cr);
                     ST.SA.RL.Lemma_Split_L
                       (One - Cr, Cr, V0, V1, (Tm.K * P0) * P1);
                  else
                     ST.SA.RL.Lemma_Move_R (Tm.K, P0, P1, Cr);
                     ST.SA.RL.Lemma_Split_R
                       (One - Cr, Cr, V0, V1, (Tm.K * P0) * P1);
                  end if;
               end if;
            end;
         end if;
      end Lemma_V_Step1;

      procedure Lemma_Pre_Frame (C, D : Element_Array; R : Natural;
                                 X : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Pre_F);
      begin
         if R > 0 then
            Lemma_Pre_Frame (C, D, R - 1, X);
         end if;
      end Lemma_Pre_Frame;

      procedure Lemma_V_Frame
        (T      : Term_Array;
         N      : Natural;
         C0, D0 : Element_Array;
         R0     : Natural;
         C1, D1 : Element_Array;
         R1     : Natural;
         A      : Natural;
         B      : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", V_Sum);
      begin
         if N > 0 then
            Lemma_V_Frame (T, N - 1, C0, D0, R0, C1, D1, R1, A, B);
            Lemma_Pre_Frame (C0, D0, R0, T (T'First + N - 1).H0);
            Lemma_Pre_Frame (C1, D1, R1, T (T'First + N - 1).H1);
         end if;
      end Lemma_V_Frame;

      procedure Lemma_V_W0
        (T      : Term_Array;
         N      : Natural;
         C0, C1 : Element_Array;
         A, B   : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", V_Sum);
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", W_Sum);
      begin
         if N > 0 then
            Lemma_V_W0 (T, N - 1, C0, C1, A, B);
            Lemma_Shr_Step (T (T'First + N - 1).H0, 0);
            Lemma_Shr_Step (T (T'First + N - 1).H1, 0);
            Lemma_Pre_Zero (C0, T (T'First + N - 1).H0);
            Lemma_Pre_Zero (C1, T (T'First + N - 1).H1);
            ST.SA.RL.Lemma_One_Twice (T (T'First + N - 1).K);
         end if;
      end Lemma_V_W0;

      procedure Lemma_Z_Frame (Tm, T : Term_Array; X, M : Natural; A,
                               B : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Z_Sum);
      begin
         if X > 0 then
            Lemma_Z_Frame (Tm, T, X - 1, M, A, B);
            Lemma_Run_Sum_W_Step (T, M + 1);
         end if;
      end Lemma_Z_Frame;

      procedure Lemma_Merge_Step
        (Tm, T : Term_Array; M : Natural; A, B : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", W_Sum);
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Z_Sum);
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Run_Sum_W);
         R  : constant Natural := Run_Id (T, M - 1);
         Ki : constant Element := T (T'First + M - 1).K;
      begin
         Lemma_Run_Id_Step (T, M - 1);
         Lemma_Run_Sum_W_Step (T, M);
         Lemma_Z_Frame (Tm, T, R, M - 1, A, B);
         if R = Run_Id (T, M - 2) then
            ST.SA.RL.Lemma_Assoc_Add
              (Z_Sum (Tm, T, R, M - 1, A, B), Run_Sum_W (T, R, M - 1), Ki);
         else
            Lemma_Run_Sum_W_Zero (T, R, M - 1);
            ST.SA.RL.Lemma_Zero_Add_Once (Ki);
         end if;
      end Lemma_Merge_Step;

      procedure Lemma_Merge_Sum (Tm, T : Term_Array; M : Natural; A,
                                 B : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", W_Sum);
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Z_Sum);
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Run_Sum_W);
      begin
         if M = 0 then
            null;
         elsif M = 1 then
            Lemma_Run_Id_Zero (T);
            Lemma_Run_Sum_W_Step (T, 1);
            ST.SA.RL.Lemma_Zero_Add_Once (T (T'First).K);
         else
            Lemma_Merge_Sum (Tm, T, M - 1, A, B);
            Lemma_Merge_Step (Tm, T, M, A, B);
         end if;
      end Lemma_Merge_Sum;

      procedure Lemma_Z_Tm (Tm, T : Term_Array; X : Natural; A, B : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", W_Sum);
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Z_Sum);
      begin
         if X > 0 then
            Lemma_Z_Tm (Tm, T, X - 1, A, B);
         end if;
      end Lemma_Z_Tm;

      procedure Lemma_Pre_Bindeq (C : Element_Array; L, K : Natural;
                                  X : Natural)
      is
      begin
         if K = 0 then
            Lemma_Pre_Zero (C, X);
            Lemma_Shr_Step (X, 0);
            ST.SA.RL.Lemma_One_Mul (ST.SA.Bindeq_Ref (C (0 .. L - 1), 0, X));
         else
            Lemma_Pre_Bindeq (C, L, K - 1, X);
            Lemma_Pre_Step (C, K - 1, X);
            Lemma_Shr_Step (X, K - 1);
            ST.SA.RL.Lemma_Assoc_Mul
              (Pre_F (C, K - 1, X), Fac (Shr (X, K - 1), C (K - 1)),
               ST.SA.Bindeq_Ref (C (0 .. L - 1), K, Shr (X, K)));
         end if;
      end Lemma_Pre_Bindeq;

      procedure Lemma_Pre_Beq (C : Element_Array; L : Natural; X : Natural)
      is
      begin
         Lemma_Pre_Bindeq (C, L, L, X);
         ST.SA.RL.Lemma_Mul_One_Once (Pre_F (C, L, X));
      end Lemma_Pre_Beq;

      procedure Lemma_Table_Len_Step (L : Natural)
      is
      begin
         null;
      end Lemma_Table_Len_Step;

      procedure Lemma_Shr_Below (X : Natural; L, K : Natural)
      is
      begin
         Lemma_Shr_Step (X, 0);
         if K > 0 then
            Lemma_Shr_Below (X, L, K - 1);
            Lemma_Shr_Step (X, K - 1);
            Lemma_Table_Len_Step (L - K + 1);
         end if;
      end Lemma_Shr_Below;

      procedure Lemma_V_End
        (T1, T0 : Term_Array;
         N      : Natural;
         Logv   : Natural;
         G0, G1 : Element_Array;
         C0, C1 : Element_Array;
         L      : Natural;
         Alpha  : Element;
         Beta   : Element)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", V_Sum);
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body",
            ST.SA.EBQT_Ref);
      begin
         if N > 0 then
            Lemma_V_End (T1, T0, N - 1, Logv, G0, G1, C0, C1, L, Alpha, Beta);
            declare
               I : constant Positive := T0'First + N - 1;
            begin
               Lemma_Shr_Below (T0 (I).H0, L, L);
               Lemma_Shr_Below (T0 (I).H1, L, L);
               Lemma_Pre_Beq (C0, L, T0 (I).H0);
               Lemma_Pre_Beq (C1, L, T0 (I).H1);
            end;
         end if;
      end Lemma_V_End;

      procedure Lemma_Inv_At
        (S  : Term_Array;
         N  : Natural;
         T1 : Term_Array;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Inv);
      begin
         null;
      end Lemma_Inv_At;

      procedure Lemma_W_Slice (S, U : Term_Array; N : Natural; A, B : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", W_Sum);
      begin
         if N > 0 then
            Lemma_W_Slice (S, U, N - 1, A, B);
         end if;
      end Lemma_W_Slice;

      procedure Lemma_Inv_Slice
        (S, U : Term_Array;
         N    : Natural;
         T1   : Term_Array;
         C0   : Element_Array;
         R0   : Natural;
         C1   : Element_Array;
         R1   : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Inv);
      begin
         for A in 0 .. ST.SA.Max_Wires - 1 loop
            for B in 0 .. ST.SA.Max_Wires - 1 loop
               Lemma_W_Slice (S, U, N, A, B);
               pragma Loop_Invariant
                 (for all B2 in 0 .. B =>
                    Same (W_Sum (U, N, 0, A, B2),
                          V_Sum (T1, T1'Length, C0, R0, C1, R1, A, B2)));
            end loop;
            pragma Loop_Invariant
              (for all A2 in 0 .. A =>
                 (for all B2 in 0 .. ST.SA.Max_Wires - 1 =>
                    Same (W_Sum (U, N, 0, A2, B2),
                          V_Sum (T1, T1'Length, C0, R0, C1, R1, A2, B2))));
         end loop;
      end Lemma_Inv_Slice;

      procedure Lemma_Inv_Base
        (Tm, T1 : Term_Array;
         NT     : Natural;
         C0, C1 : Element_Array)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Inv);
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", W_Sum);
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", V_Sum);
      begin
         for A in 0 .. ST.SA.Max_Wires - 1 loop
            for B in 0 .. ST.SA.Max_Wires - 1 loop
               if T1'Length >= 1 then
                  Lemma_Merge_Sum (Tm, T1, T1'Length, A, B);
                  Lemma_Z_Tm (Tm, T1, NT, A, B);
               end if;
               Lemma_V_W0 (T1, T1'Length, C0, C1, A, B);
               pragma Loop_Invariant
                 (for all B2 in 0 .. B =>
                    Same (W_Sum (Tm, NT, 0, A, B2),
                          V_Sum (T1, T1'Length, C0, 0, C1, 0, A, B2)));
            end loop;
            pragma Loop_Invariant
              (for all A2 in 0 .. A =>
                 (for all B2 in 0 .. ST.SA.Max_Wires - 1 =>
                    Same (W_Sum (Tm, NT, 0, A2, B2),
                          V_Sum (T1, T1'Length, C0, 0, C1, 0, A2, B2))));
         end loop;
      end Lemma_Inv_Base;

      procedure Lemma_Inv_Frame
        (S      : Term_Array;
         N      : Natural;
         T1     : Term_Array;
         C0, D0 : Element_Array;
         R0     : Natural;
         C1, D1 : Element_Array;
         R1     : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Inv);
      begin
         for A in 0 .. ST.SA.Max_Wires - 1 loop
            for B in 0 .. ST.SA.Max_Wires - 1 loop
               Lemma_V_Frame (T1, T1'Length, C0, D0, R0, C1, D1, R1, A, B);
               pragma Loop_Invariant
                 (for all B2 in 0 .. B =>
                    Same (W_Sum (S, N, 0, A, B2),
                          V_Sum (T1, T1'Length, D0, R0, D1, R1, A, B2)));
            end loop;
            pragma Loop_Invariant
              (for all A2 in 0 .. A =>
                 (for all B2 in 0 .. ST.SA.Max_Wires - 1 =>
                    Same (W_Sum (S, N, 0, A2, B2),
                          V_Sum (T1, T1'Length, D0, R0, D1, R1, A2, B2))));
         end loop;
      end Lemma_Inv_Frame;

      procedure Lemma_Inv_Step0
        (Old, New_T : Term_Array;
         NB         : Natural;
         T1         : Term_Array;
         C0         : Element_Array;
         R0         : Natural;
         C1         : Element_Array;
         R1         : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Inv);
      begin
         for A in 0 .. ST.SA.Max_Wires - 1 loop
            for B in 0 .. ST.SA.Max_Wires - 1 loop
               Lemma_Bind_H_Sum (Old, New_T, 0, C0 (R0), NB, NB, A, B);
               Lemma_V_Step0 (T1, T1'Length, C0, R0, C1, R1, A, B);
               if 2 * A + 1 >= ST.SA.Max_Wires then
                  Lemma_W_Out (Old, Old'Length, 0, 2 * A, B);
                  Lemma_W_Out (Old, Old'Length, 0, 2 * A + 1, B);
                  Lemma_V_Out (T1, T1'Length, C0, R0, C1, R1, 2 * A, B);
                  Lemma_V_Out (T1, T1'Length, C0, R0, C1, R1, 2 * A + 1, B);
               end if;
               pragma Loop_Invariant
                 (for all B2 in 0 .. B =>
                    Same (W_Sum (New_T, NB, 0, A, B2),
                          V_Sum (T1, T1'Length, C0, R0 + 1, C1, R1, A, B2)));
            end loop;
            pragma Loop_Invariant
              (for all A2 in 0 .. A =>
                 (for all B2 in 0 .. ST.SA.Max_Wires - 1 =>
                    Same (W_Sum (New_T, NB, 0, A2, B2),
                          V_Sum (T1, T1'Length, C0, R0 + 1, C1, R1,
                                 A2, B2))));
         end loop;
      end Lemma_Inv_Step0;

      procedure Lemma_Inv_Step1
        (Old, New_T : Term_Array;
         NB         : Natural;
         T1         : Term_Array;
         C0         : Element_Array;
         R0         : Natural;
         C1         : Element_Array;
         R1         : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Inv);
      begin
         for A in 0 .. ST.SA.Max_Wires - 1 loop
            for B in 0 .. ST.SA.Max_Wires - 1 loop
               Lemma_Bind_H_Sum (Old, New_T, 1, C1 (R1), NB, NB, B, A);
               Lemma_W_Swap (New_T, NB, B, A);
               if 2 * B + 1 >= ST.SA.Max_Wires then
                  Lemma_W_Out (Old, Old'Length, 1, 2 * B, A);
                  Lemma_W_Out (Old, Old'Length, 1, 2 * B + 1, A);
                  Lemma_V_Out (T1, T1'Length, C0, R0, C1, R1, A, 2 * B);
                  Lemma_V_Out (T1, T1'Length, C0, R0, C1, R1, A, 2 * B + 1);
               else
                  Lemma_W_Swap (Old, Old'Length, 2 * B, A);
                  Lemma_W_Swap (Old, Old'Length, 2 * B + 1, A);
               end if;
               Lemma_V_Step1 (T1, T1'Length, C0, R0, C1, R1, A, B);
               pragma Loop_Invariant
                 (for all B2 in 0 .. B =>
                    Same (W_Sum (New_T, NB, 0, A, B2),
                          V_Sum (T1, T1'Length, C0, R0, C1, R1 + 1, A, B2)));
            end loop;
            pragma Loop_Invariant
              (for all A2 in 0 .. A =>
                 (for all B2 in 0 .. ST.SA.Max_Wires - 1 =>
                    Same (W_Sum (New_T, NB, 0, A2, B2),
                          V_Sum (T1, T1'Length, C0, R0, C1, R1 + 1,
                                 A2, B2))));
         end loop;
      end Lemma_Inv_Step1;

      procedure Lemma_W_Step (T : Term_Array; N : Natural; H : Hand;
                              A, B : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", W_Sum);
      begin
         null;
      end Lemma_W_Step;

      procedure Lemma_W_Zero (T : Term_Array; H : Hand; A, B : Natural) is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", W_Sum);
      begin
         null;
      end Lemma_W_Zero;

      procedure Lemma_TL_Shift (L : Natural) is
      begin
         if L = 0 then
            Lemma_Table_Len_Step (1);
         else
            Lemma_TL_Shift (L - 1);
            Lemma_Table_Len_Step (L);
            pragma Assert (Shl (1, L) = 2 * Shl (1, L - 1));
         end if;
      end Lemma_TL_Shift;

      procedure Lemma_Hands_Below (T : Term_Array; NW : Natural; L : Natural)
      is
         pragma Unreferenced (T, NW);
      begin
         Lemma_TL_Shift (L);
      end Lemma_Hands_Below;

      procedure Lemma_T1_Bound
        (T0, T1 : Term_Array;
         E      : Element_Array;
         Logv   : Natural;
         G0, G1 : Element_Array;
         Alpha  : Element;
         Beta   : Element)
      is
      begin
         for I in T1'Range loop
            if T0 (I).K = Zero then
               ST.SA.Lemma_Mul_W (Beta, Ref (E, E'Length, T0 (I).G));
            else
               ST.SA.Lemma_Mul_W (T0 (I).K, Ref (E, E'Length, T0 (I).G));
            end if;
            pragma Loop_Invariant
              (for all J in T1'First .. I =>
                 Same (T1 (J).K,
                       ST.SA.Bound_KT (T0 (J), Logv, G0, G1, Alpha, Beta)));
         end loop;
      end Lemma_T1_Bound;

      procedure Lemma_V_Coef
        (T, U : Term_Array;
         N    : Natural;
         C0   : Element_Array;
         R0   : Natural;
         C1   : Element_Array;
         R1   : Natural;
         A    : Natural;
         B    : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", V_Sum);
      begin
         if N > 0 then
            Lemma_V_Coef (T, U, N - 1, C0, R0, C1, R1, A, B);
         end if;
      end Lemma_V_Coef;

      procedure Lemma_Inv_Coef
        (S     : Term_Array;
         N     : Natural;
         T1, U : Term_Array;
         C0    : Element_Array;
         R0    : Natural;
         C1    : Element_Array;
         R1    : Natural)
      is
         pragma Annotate
           (GNATprove, Unhide_Info, "Expression_Function_Body", Inv);
      begin
         for A in 0 .. ST.SA.Max_Wires - 1 loop
            for B in 0 .. ST.SA.Max_Wires - 1 loop
               Lemma_V_Coef (T1, U, T1'Length, C0, R0, C1, R1, A, B);
               pragma Loop_Invariant
                 (for all B2 in 0 .. B =>
                    Same (W_Sum (S, N, 0, A, B2),
                          V_Sum (U, U'Length, C0, R0, C1, R1, A, B2)));
            end loop;
            pragma Loop_Invariant
              (for all A2 in 0 .. A =>
                 (for all B2 in 0 .. ST.SA.Max_Wires - 1 =>
                    Same (W_Sum (S, N, 0, A2, B2),
                          V_Sum (U, U'Length, C0, R0, C1, R1, A2, B2))));
         end loop;
      end Lemma_Inv_Coef;
   end BQ;

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

   --  The terms after a round of hand H with challenge X: k scaled by
   --  1 - x for an even wire index of that hand, by x for an odd one;
   --  the index halved (sumcheck_prove_layer).
   --  Merge_Runs, with the invariant of the rounds at round 0 when the
   --  tables are in use (ADR 0071). T0 is the layer of the circuit.
   procedure Merge_Terms
     (T      : in out Term_Array;
      NT     : out Natural;
      Tab    : Boolean;
      T0     : Term_Array;
      Logv   : Natural;
      G0, G1 : Element_Array;
      Alpha  : Element;
      Beta   : Element;
      C0, C1 : Element_Array)
   with
     Global => null,
     Pre    =>
       (Proof_Only =>
          (if Tab then
             G0'First = 0 and then G1'First = 0
             and then Logv <= G0'Length and then Logv <= G1'Length
             and then Logv <= ST.SA.Max_Bindeq_Log
             and then C0'First = 0 and then C1'First = 0
             and then T'First = T0'First and then T'Last = T0'Last
             and then
             (for all I in T'Range =>
                Same (T (I).K,
                      ST.SA.Bound_KT (T0 (I), Logv, G0, G1, Alpha, Beta))
                and then T (I).H0 = T0 (I).H0
                and then T (I).H1 = T0 (I).H1))),
     Post   =>
       (Runtime    => NT <= T'Length,
        Proof_Only =>
          (if Tab then BQ.Inv (T, NT, BQ.Bound_Array (T0, Logv, G0, G1, Alpha,
                                                      Beta), C0, 0, C1, 0)))
   is
      T1 : constant Term_Array := T with Ghost => Proof_Only;
   begin
      Merge_Runs (T, NT);
      if Tab then
         BQ.Lemma_Run_Sums_W (T, T1, NT);
         BQ.Lemma_Inv_Base (T, T1, NT, C0, C1);
         BQ.Lemma_Inv_Coef (T, NT, T1, BQ.Bound_Array (T0, Logv, G0, G1, Alpha,
                                                       Beta), C0, 0, C1, 0);
      end if;
   end Merge_Terms;

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
      Bind_H (T (T'First .. T'First + NT - 1), H, Chal, NB);
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

   --  One layer of sumcheck_prove: the binding of g, the 2 logw rounds
   --  of the two hands, the claims; Logv, Cur0 and Cur1 move on to the
   --  next layer. A subprogram of its own, so that the proof of a layer
   --  sees only this context (ADR 0071).
   procedure Prove_Layer
     (C          : Circuit;
      J          : Natural;
      Wires      : Element_Array;
      Pads       : Element_Array;
      Logv       : in out Natural;
      Cur0, Cur1 : in out Element_Array;
      Nxt0, Nxt1 : in out Element_Array;
      Proof      : in out Sumcheck_Proof;
      Ch         : in out Challenges;
      BQJ        : out Element)
   with
     Always_Terminates => not ST.SA.F.Sampling_Rejects,
     Pre  =>
       (Runtime =>
       J <= C.Last_Layer
       and then Wires'First = 0 and then Wires'Length = ST.SA.Total_Wires (C)
       and then Pads'First = 0 and then Pads'Length = Pad_Total (C)
       and then Logv <= Max_Logw
       and then Cur0'First = 0 and then Cur0'Last = Max_Logw - 1
       and then Cur1'First = 0 and then Cur1'Last = Max_Logw - 1
       and then Nxt0'First = 0 and then Nxt0'Last = Max_Logw - 1
       and then Nxt1'First = 0 and then Nxt1'Last = Max_Logw - 1
       and then Proof.Last + 1 = ST.SV.Proof_Total (C)
       and then Ch.Last + 1 = ST.SV.Chal_Total (C),
        Proof_Only =>
          Logv = ST.SV.Layer_Logv (C, J)
          and then (for all R in 0 .. Logv - 1 =>
                      Same (Cur0 (R), ST.SV.Layer_G (C, Ch, J, 0) (R))
                      and then Same (Cur1 (R), ST.SV.Layer_G (C, Ch, J,
                                                              1) (R)))),
     Post =>
       (Runtime    => Logv <= Max_Logw,
        Proof_Only =>
          Same (BQJ, ST.SV.BQ_Ref (C, Ch, J))
          and then Logv = C.Layers (J).Logw
          and then (for all R in 0 .. Logv - 1 =>
                      Same (Cur0 (R), ST.SV.Hand_Chal (C, Ch, J, 0) (R))
                      and then Same (Cur1 (R), ST.SV.Hand_Chal (C, Ch, J,
                                                                1) (R)))
          and then Ch.Last = Ch'Old.Last
          and then (for all R in 0 .. Max_Logw - 1 =>
                      Same (Ch.G (R), Ch'Old.G (R)))
          and then (for all K in 0 .. Ch.Last =>
                      (if K < ST.SV.Chal_Off (C, J)
                       then Same (Ch.Layer (K), Ch'Old.Layer (K)))))
   is
      Ch_In : constant Challenges := Ch with Ghost => Proof_Only;
      Alpha, Beta, Chal, Ev0, Ev2, P0, P2V : Element;
      N0, N1, NT : Natural;
   begin
      Lemma_Layer_Fits (C, J);
      Lemma_Segment (C, J);
      declare
         Logw  : constant Logw_Type := C.Layers (J).Logw;
         NW    : constant Natural := C.Layers (J).NW_In;
         Seg   : constant Natural := ST.SA.Off (C, J + 1);
         Off_P : constant Natural := ST.SV.Proof_Off (C, J);
         Off_C : constant Natural := ST.SV.Chal_Off (C, J);
         Off_D : constant Natural := ST.SV.Pad_Off (C, J, 0);
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
         --  bind_g with the eq2 table when it fits, then the runs of
         --  equal hands merged: NT terms from here on.
         if Logv <= ST.SA.Max_Bindeq_Log then
            declare
               E : Elems_Access := new Element_Array'
                 (0 .. ST.SA.Table_Len (Logv) - 1 => Zero);
            begin
               ST.SA.Eq2_Table (Logv, Cur0, Cur1, Alpha, E.all);
               Bind_G_T (T.all, E.all, Beta);
               BQ.Lemma_T1_Bound
                 (C.Terms (First .. Last), T.all, E.all, Logv, Cur0, Cur1,
                  Alpha, Beta);
               Free_Elems (E);
            end;
         else
            ST.SA.Bind_G (T.all, Logv, Cur0, Cur1, Alpha, Beta);
         end if;
         Merge_Terms
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
            pragma Loop_Invariant (Proof.Last + 1 = ST.SV.Proof_Total (C));
            pragma Loop_Invariant (Ch.Last + 1 = ST.SV.Chal_Total (C));
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
               P2, Q.all, Ev0, Ev2);
            P0  := Ev0 - Pads (Off_D + 4 * R);
            P2V := Ev2 - Pads (Off_D + 4 * R + 1);
            ST.Round_Poly (P0, P2V, Chal);
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
               P2, Q.all, Ev0, Ev2);
            P0  := Ev0 - Pads (Off_D + 4 * R + 2);
            P2V := Ev2 - Pads (Off_D + 4 * R + 3);
            ST.Round_Poly (P0, P2V, Chal);
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
         ST.SV.Lemma_Layer_G_Frame (C, Ch_In, Ch, J);
         pragma Assert
           (Proof_Only =>
              (for all R in 0 .. Logv - 1 =>
                 Same (Cur0 (R), ST.SV.Layer_G (C, Ch, J, 0) (R))
                 and then Same (Cur1 (R), ST.SV.Layer_G (C, Ch, J, 1) (R))));
         if Tab then
            BQJ := BQ_J;
         else
            BQJ := ST.SA.Eval_Bound_Quad
              (C.Terms (First .. Last), Logv, Cur0, Cur1, Nxt0, Nxt1, Logw,
               Alpha, Beta);
         end if;
         ST.SV.Lemma_BQ_Ref_From
           (C, Ch, J, Logv, Cur0, Cur1, Nxt0, Nxt1, BQJ);
         P0  := Ref (A0.all, N0, 0) - Pads (Off_D + 4 * Logw);
         P2V := Ref (A1.all, N1, 0) - Pads (Off_D + 4 * Logw + 1);
         Proof.Evals (Off_P + 4 * Logw)     := P0;
         Proof.Evals (Off_P + 4 * Logw + 1) := P2V;
         ST.End_Layer (P0, P2V);
         Logv := Logw;
         Cur0 := Nxt0;
         Cur1 := Nxt1;
         ST.SV.Lemma_Hand_Chal (C, Ch, J, 0, Cur0);
         ST.SV.Lemma_Hand_Chal (C, Ch, J, 1, Cur1);
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
      Logv : Natural := ST.SV.Ceil_Lg2 (C.Noutput);
      Cur0, Cur1 : Element_Array (0 .. Max_Logw - 1);
      Nxt0, Nxt1 : Element_Array (0 .. Max_Logw - 1) := [others => Zero];
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
         pragma Loop_Invariant (Proof.Last + 1 = ST.SV.Proof_Total (C));
         pragma Loop_Invariant (Ch.Last + 1 = ST.SV.Chal_Total (C));
         pragma Loop_Invariant
           (Proof_Only =>
              Logv = ST.SV.Layer_Logv (C, J)
              and then (for all R in 0 .. Logv - 1 =>
                          Same (Cur0 (R), ST.SV.Layer_G (C, Ch, J, 0) (R))
                          and then
                          Same (Cur1 (R), ST.SV.Layer_G (C, Ch, J, 1) (R)))
              and then (for all J2 in 0 .. J - 1 =>
                          Same (BQ (J2), ST.SV.BQ_Ref (C, Ch, J2))));
         declare
            Ch_Before : constant Challenges := Ch with Ghost => Proof_Only;
         begin
            Prove_Layer (C, J, Wires, Pads, Logv, Cur0, Cur1, Nxt0, Nxt1,
                         Proof, Ch, BQ (J));
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
