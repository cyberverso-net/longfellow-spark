pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;

package body Sumcheck_Prover is

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

      --  The pairs: p (0) and p (P2), three products per pair.
      Ev0 := Zero;
      Ev2 := Zero;
      Lemma_D_Zero (QW, Active, NA, X2);
      for M in 0 .. (NA + 1) / 2 - 1 loop
         pragma Loop_Invariant
           (Proof_Only =>
              Same (Ev0, D0_Ref (QW, Active, NA, M))
              and then Same (Ev2, D2_Ref (QW, Active, NA, X2, M)));
         Q0 := Ref (QW, NA, 2 * M);
         Q1 := Ref (QW, NA, 2 * M + 1);
         W0 := Ref (Active, NA, 2 * M);
         W1 := Ref (Active, NA, 2 * M + 1);
         Ev0 := Ev0 + Q0 * W0;
         Ev2 := Ev2 + (Q0 + X2 * (Q1 - Q0)) * (W0 + X2 * (W1 - W0));
         Lemma_D_Step (QW, Active, NA, X2, M + 1);
      end loop;
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
   function Ceil_Lg2 (N : Natural) return Natural with
     Global => null,
     Pre    => N <= ST.SA.Max_Wires,
     Post   => Ceil_Lg2'Result <= 24;

   function Ceil_Lg2 (N : Natural) return Natural is
      P : Natural := 1;
   begin
      if N <= 1 then
         return 0;
      end if;
      for K in 0 .. 24 loop
         if P >= N then
            return K;
         end if;
         pragma Assert (P < N);
         P := 2 * P;
      end loop;
      return 24;
   end Ceil_Lg2;

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
   procedure Prove
     (C     : Circuit;
      Wires : Element_Array;
      Pads  : Element_Array;
      Proof : out Sumcheck_Proof;
      Ch    : out Challenges)
   is
      Logv : Natural := Ceil_Lg2 (C.Noutput);
      Cur0, Cur1 : Element_Array (0 .. Max_Logw - 1);
      Nxt0, Nxt1 : Element_Array (0 .. Max_Logw - 1) := [others => Zero];
      Alpha, Beta, Chal, Ev0, Ev2, P0, P2V : Element;
      N0, N1, NT, NB : Natural;
   begin
      Proof := (Last => Proof.Last, Evals => [others => Zero]);
      Ch := (Last        => Ch.Last,
             G           => [others => Zero],
             Layer       => [others => Zero],
             Alpha_Input => Zero);
      ST.Begin_Circuit (Ch.G);
      Cur0 := Ch.G;
      Cur1 := Ch.G;
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant (Logv <= Max_Logw);
         pragma Loop_Invariant (Proof.Last + 1 = ST.SV.Proof_Total (C));
         pragma Loop_Invariant (Ch.Last + 1 = ST.SV.Chal_Total (C));
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
                  Free_Elems (E);
               end;
            else
               ST.SA.Bind_G (T.all, Logv, Cur0, Cur1, Alpha, Beta);
            end if;
            Merge_Runs (T.all, NT);
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
               pragma Loop_Invariant (Proof.Last + 1 = ST.SV.Proof_Total (C));
               pragma Loop_Invariant (Ch.Last + 1 = ST.SV.Chal_Total (C));
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
               Ch.Layer (Off_C + 2 + 2 * R) := Chal;
               Nxt0 (R) := Chal;
               Bind_Hand (A0.all, B0, N0, Chal);
               declare
                  Tmp : Elems_Access := A0;
               begin
                  A0 := B0;
                  B0 := Tmp;
               end;
               Bind_H (T (T'First .. T'First + NT - 1), 0, Chal, NB);
               NT := NB;
               Round_Evals_Dense
                 (T (T'First .. T'First + NT - 1), A1.all, N1, A0.all, N0, 1,
                  P2, Q.all, Ev0, Ev2);
               P0  := Ev0 - Pads (Off_D + 4 * R + 2);
               P2V := Ev2 - Pads (Off_D + 4 * R + 3);
               ST.Round_Poly (P0, P2V, Chal);
               Proof.Evals (Off_P + 4 * R + 2) := P0;
               Proof.Evals (Off_P + 4 * R + 3) := P2V;
               Ch.Layer (Off_C + 2 + 2 * R + 1) := Chal;
               Nxt1 (R) := Chal;
               Bind_Hand (A1.all, B1, N1, Chal);
               declare
                  Tmp : Elems_Access := A1;
               begin
                  A1 := B1;
                  B1 := Tmp;
               end;
               Bind_H (T (T'First .. T'First + NT - 1), 1, Chal, NB);
               NT := NB;
            end loop;
            P0  := Ref (A0.all, N0, 0) - Pads (Off_D + 4 * Logw);
            P2V := Ref (A1.all, N1, 0) - Pads (Off_D + 4 * Logw + 1);
            Proof.Evals (Off_P + 4 * Logw)     := P0;
            Proof.Evals (Off_P + 4 * Logw + 1) := P2V;
            ST.End_Layer (P0, P2V);
            Logv := Logw;
            Cur0 := Nxt0;
            Cur1 := Nxt1;
            Free_Terms (T);
            Free_Elems (A0);
            Free_Elems (A1);
            Free_Elems (B0);
            Free_Elems (B1);
            Free_Elems (Q);
         end;
      end loop;
      ST.Sample (Ch.Alpha_Input);
   end Prove;

end Sumcheck_Prover;
