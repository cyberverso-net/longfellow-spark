pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;

package body Sumcheck_HQuad is

   --  Heap buffers (ADR 0047): the copy of the terms and the eq2 table
   --  of Bind_Quad.
   type Elems_Access is access Element_Array;
   type Terms_Access is access Term_Array;

   procedure Free_Elems is
     new Ada.Unchecked_Deallocation (Element_Array, Elems_Access);
   procedure Free_Terms is
     new Ada.Unchecked_Deallocation (Term_Array, Terms_Access);

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

   package body BQ is

      procedure Lemma_Corner_To_W
        (T : Term_Array; P : Natural; H : Hand; R : Element)
      is
      begin
         if Two (T, P, H) then
            SA.Lemma_Corner_Two_W
              (T (T'First + P).K, T (T'First + P + 1).K, R);
         elsif Hand_Index (T (T'First + P), H) mod 2 = 0 then
            SA.Lemma_Corner_Even_W (T (T'First + P).K, R);
         else
            SA.Lemma_Corner_Odd_W (T (T'First + P).K, R);
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
            SA.Lemma_Add_W (Run_Sum (T, X, N - 1), T (T'First + N - 1).K);
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
               SA.RL.Lemma_Split_LR
                 (One - R, R, Wo0, Wo1, Kp, T0 (T0'First + P + 1).K);
            end if;
         elsif X0 / 2 = A and then Y0 = B then
            if X0 mod 2 = 0 then
               SA.RL.Lemma_Split_L (One - R, R, Wo0, Wo1, Kp);
            else
               SA.RL.Lemma_Split_R (One - R, R, Wo0, Wo1, Kp);
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
            SA.RL.Lemma_Split_Zero (One - R, R);
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
            SA.RL.Lemma_Split_Zero (One - Cr, Cr);
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
                     SA.RL.Lemma_Move_L (Tm.K, P0, One - Cr, P1);
                     SA.RL.Lemma_Split_L
                       (One - Cr, Cr, V0, V1, (Tm.K * P0) * P1);
                  else
                     SA.RL.Lemma_Move_L (Tm.K, P0, Cr, P1);
                     SA.RL.Lemma_Split_R
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
            SA.RL.Lemma_Split_Zero (One - Cr, Cr);
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
                     SA.RL.Lemma_Move_R (Tm.K, P0, P1, One - Cr);
                     SA.RL.Lemma_Split_L
                       (One - Cr, Cr, V0, V1, (Tm.K * P0) * P1);
                  else
                     SA.RL.Lemma_Move_R (Tm.K, P0, P1, Cr);
                     SA.RL.Lemma_Split_R
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
            SA.RL.Lemma_One_Twice (T (T'First + N - 1).K);
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
            SA.RL.Lemma_Assoc_Add
              (Z_Sum (Tm, T, R, M - 1, A, B), Run_Sum_W (T, R, M - 1), Ki);
         else
            Lemma_Run_Sum_W_Zero (T, R, M - 1);
            SA.RL.Lemma_Zero_Add_Once (Ki);
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
            SA.RL.Lemma_Zero_Add_Once (T (T'First).K);
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
            SA.RL.Lemma_One_Mul (SA.Bindeq_Ref (C (0 .. L - 1), 0, X));
         else
            Lemma_Pre_Bindeq (C, L, K - 1, X);
            Lemma_Pre_Step (C, K - 1, X);
            Lemma_Shr_Step (X, K - 1);
            SA.RL.Lemma_Assoc_Mul
              (Pre_F (C, K - 1, X), Fac (Shr (X, K - 1), C (K - 1)),
               SA.Bindeq_Ref (C (0 .. L - 1), K, Shr (X, K)));
         end if;
      end Lemma_Pre_Bindeq;

      procedure Lemma_Pre_Beq (C : Element_Array; L : Natural; X : Natural)
      is
      begin
         Lemma_Pre_Bindeq (C, L, L, X);
         SA.RL.Lemma_Mul_One_Once (Pre_F (C, L, X));
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
            SA.EBQT_Ref);
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
         for A in 0 .. SA.Max_Wires - 1 loop
            for B in 0 .. SA.Max_Wires - 1 loop
               Lemma_W_Slice (S, U, N, A, B);
               pragma Loop_Invariant
                 (for all B2 in 0 .. B =>
                    Same (W_Sum (U, N, 0, A, B2),
                          V_Sum (T1, T1'Length, C0, R0, C1, R1, A, B2)));
            end loop;
            pragma Loop_Invariant
              (for all A2 in 0 .. A =>
                 (for all B2 in 0 .. SA.Max_Wires - 1 =>
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
         for A in 0 .. SA.Max_Wires - 1 loop
            for B in 0 .. SA.Max_Wires - 1 loop
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
                 (for all B2 in 0 .. SA.Max_Wires - 1 =>
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
         for A in 0 .. SA.Max_Wires - 1 loop
            for B in 0 .. SA.Max_Wires - 1 loop
               Lemma_V_Frame (T1, T1'Length, C0, D0, R0, C1, D1, R1, A, B);
               pragma Loop_Invariant
                 (for all B2 in 0 .. B =>
                    Same (W_Sum (S, N, 0, A, B2),
                          V_Sum (T1, T1'Length, D0, R0, D1, R1, A, B2)));
            end loop;
            pragma Loop_Invariant
              (for all A2 in 0 .. A =>
                 (for all B2 in 0 .. SA.Max_Wires - 1 =>
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
         for A in 0 .. SA.Max_Wires - 1 loop
            for B in 0 .. SA.Max_Wires - 1 loop
               Lemma_Bind_H_Sum (Old, New_T, 0, C0 (R0), NB, NB, A, B);
               Lemma_V_Step0 (T1, T1'Length, C0, R0, C1, R1, A, B);
               if 2 * A + 1 >= SA.Max_Wires then
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
                 (for all B2 in 0 .. SA.Max_Wires - 1 =>
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
         for A in 0 .. SA.Max_Wires - 1 loop
            for B in 0 .. SA.Max_Wires - 1 loop
               Lemma_Bind_H_Sum (Old, New_T, 1, C1 (R1), NB, NB, B, A);
               Lemma_W_Swap (New_T, NB, B, A);
               if 2 * B + 1 >= SA.Max_Wires then
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
                 (for all B2 in 0 .. SA.Max_Wires - 1 =>
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
               SA.Lemma_Mul_W (Beta, Ref (E, E'Length, T0 (I).G));
            else
               SA.Lemma_Mul_W (T0 (I).K, Ref (E, E'Length, T0 (I).G));
            end if;
            pragma Loop_Invariant
              (for all J in T1'First .. I =>
                 Same (T1 (J).K,
                       SA.Bound_KT (T0 (J), Logv, G0, G1, Alpha, Beta)));
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
         for A in 0 .. SA.Max_Wires - 1 loop
            for B in 0 .. SA.Max_Wires - 1 loop
               Lemma_V_Coef (T1, U, T1'Length, C0, R0, C1, R1, A, B);
               pragma Loop_Invariant
                 (for all B2 in 0 .. B =>
                    Same (W_Sum (S, N, 0, A, B2),
                          V_Sum (U, U'Length, C0, R0, C1, R1, A, B2)));
            end loop;
            pragma Loop_Invariant
              (for all A2 in 0 .. A =>
                 (for all B2 in 0 .. SA.Max_Wires - 1 =>
                    Same (W_Sum (S, N, 0, A2, B2),
                          V_Sum (U, U'Length, C0, R0, C1, R1, A2, B2))));
         end loop;
      end Lemma_Inv_Coef;

      procedure Lemma_Shr_Above (X : Natural; L, K : Natural) is
      begin
         Lemma_Shr_Step (X, 0);
         if K > 0 then
            Lemma_Shr_Above (X, L, K - 1);
            Lemma_Shr_Step (X, K - 1);
            Lemma_Table_Len_Step (L - K + 1);
         end if;
      end Lemma_Shr_Above;

      procedure Lemma_V_End_All
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
            SA.EBQT_Ref);
      begin
         if N > 0 then
            Lemma_V_End_All
              (T1, T0, N - 1, Logv, G0, G1, C0, C1, L, Alpha, Beta);
            declare
               I  : constant Positive := T0'First + N - 1;
               KB : constant Element :=
                 SA.Bound_KT (T0 (I), Logv, G0, G1, Alpha, Beta);
               S  : constant Element :=
                 SA.EBQT_Ref (T0, N - 1, Logv, G0, G1, C0, C1, L,
                              Alpha, Beta);
            begin
               if T0 (I).H0 < SA.Table_Len (L)
                 and then T0 (I).H1 < SA.Table_Len (L)
               then
                  Lemma_Shr_Below (T0 (I).H0, L, L);
                  Lemma_Shr_Below (T0 (I).H1, L, L);
                  Lemma_Pre_Beq (C0, L, T0 (I).H0);
                  Lemma_Pre_Beq (C1, L, T0 (I).H1);
                  --  The inductive step of both sums, the same term added.
                  pragma Assert
                    (Same (SA.EBQT_Ref (T0, N, Logv, G0, G1, C0, C1, L,
                                        Alpha, Beta),
                           S + (KB * SA.Beq (C0, L, T0 (I).H0))
                               * SA.Beq (C1, L, T0 (I).H1)));
                  pragma Assert
                    (Same (V_Sum (T1, N, C0, L, C1, L, 0, 0),
                           V_Sum (T1, N - 1, C0, L, C1, L, 0, 0)
                           + (T1 (I).K * Pre_F (C0, L, T1 (I).H0))
                             * Pre_F (C1, L, T1 (I).H1)));
               elsif T0 (I).H0 >= SA.Table_Len (L) then
                  Lemma_Shr_Above (T0 (I).H0, L, L);
                  SA.RL.Lemma_Zero_Mul_Twice
                    (KB, SA.Beq (C1, L, T0 (I).H1));
                  SA.RL.Lemma_Add_Zero_Once (S);
                  pragma Assert
                    (Same (V_Sum (T1, N, C0, L, C1, L, 0, 0),
                           V_Sum (T1, N - 1, C0, L, C1, L, 0, 0)));
               else
                  Lemma_Shr_Above (T0 (I).H1, L, L);
                  SA.RL.Lemma_Zero_Mul_R (KB * SA.Beq (C0, L, T0 (I).H0));
                  SA.RL.Lemma_Add_Zero_Once (S);
                  pragma Assert
                    (Same (V_Sum (T1, N, C0, L, C1, L, 0, 0),
                           V_Sum (T1, N - 1, C0, L, C1, L, 0, 0)));
               end if;
            end;
         end if;
      end Lemma_V_End_All;

   end BQ;

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

   --  One hand of round R in Bind_Quad: Bind_H on the first NT terms at
   --  the challenge of that hand, with the invariant of the rounds
   --  carried over to the next hand.
   procedure Bind_Step
     (T        : in out Term_Array;
      NT       : in out Natural;
      H        : Hand;
      R        : Natural;
      HC0, HC1 : Element_Array;
      T0       : Term_Array;
      Logv     : Natural;
      G0, G1   : Element_Array;
      Alpha    : Element;
      Beta     : Element)
   with
     Global => null,
     Pre    =>
       (Runtime    =>
          NT <= T'Length
          and then HC0'First = 0 and then HC1'First = 0
          and then R < HC0'Length and then R < HC1'Length,
        Proof_Only =>
          G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= SA.Max_Bindeq_Log
          and then
          BQ.Inv (T, NT, BQ.Bound_Array (T0, Logv, G0, G1, Alpha, Beta),
                  HC0, (if H = 0 then R else R + 1), HC1, R)),
     Post   =>
       (Runtime    => NT <= T'Length,
        Proof_Only =>
          BQ.Inv (T, NT, BQ.Bound_Array (T0, Logv, G0, G1, Alpha, Beta),
                  HC0, R + 1, HC1, (if H = 0 then R else R + 1)))
   is
      Chal : constant Element := (if H = 0 then HC0 (R) else HC1 (R));
      Old  : constant Term_Array := T (T'First .. T'First + NT - 1)
      with Ghost => Proof_Only;
      NB   : Natural;
   begin
      BQ.Lemma_Inv_Slice
        (T, Old, NT, BQ.Bound_Array (T0, Logv, G0, G1, Alpha, Beta),
         HC0, (if H = 0 then R else R + 1), HC1, R);
      Bind_H (T (T'First .. T'First + NT - 1), H, Chal, NB);
      BQ.Lemma_Corners_W (Old, T (T'First .. T'First + NT - 1), H, Chal, NB);
      if H = 0 then
         BQ.Lemma_Inv_Step0
           (Old, T (T'First .. T'First + NT - 1), NB,
            BQ.Bound_Array (T0, Logv, G0, G1, Alpha, Beta), HC0, R, HC1, R);
         BQ.Lemma_Inv_Slice
           (T (T'First .. T'First + NT - 1), T, NB,
            BQ.Bound_Array (T0, Logv, G0, G1, Alpha, Beta),
            HC0, R + 1, HC1, R);
      else
         BQ.Lemma_Inv_Step1
           (Old, T (T'First .. T'First + NT - 1), NB,
            BQ.Bound_Array (T0, Logv, G0, G1, Alpha, Beta),
            HC0, R + 1, HC1, R);
         BQ.Lemma_Inv_Slice
           (T (T'First .. T'First + NT - 1), T, NB,
            BQ.Bound_Array (T0, Logv, G0, G1, Alpha, Beta),
            HC0, R + 1, HC1, R + 1);
      end if;
      NT := NB;
   end Bind_Step;

   procedure Bind_Quad
     (T           : Term_Array;
      Logv        : Natural;
      G0, G1      : Element_Array;
      HC0, HC1    : Element_Array;
      Logw        : Natural;
      Alpha, Beta : Element;
      V           : out Element)
   is
      W  : Terms_Access := new Term_Array'(T);
      E  : Elems_Access :=
        new Element_Array'(0 .. SA.Table_Len (Logv) - 1 => Zero);
      NT : Natural;
      S  : Element := Zero;
   begin
      --  bind_g with the eq2 table, then the runs of equal hands merged.
      SA.Eq2_Table (Logv, G0, G1, Alpha, E.all);
      Bind_G_T (W.all, E.all, Beta);
      BQ.Lemma_T1_Bound (T, W.all, E.all, Logv, G0, G1, Alpha, Beta);
      Free_Elems (E);
      Merge_Terms
        (W.all, NT, True, T, Logv, G0, G1, Alpha, Beta, HC0, HC1);
      --  bind_h of hand 0 then hand 1, Logw rounds.
      for R in 0 .. Logw - 1 loop
         pragma Loop_Invariant (W /= null);
         pragma Loop_Invariant (W'First = T'First and then W'Last = T'Last);
         pragma Loop_Invariant (NT <= W'Length);
         pragma Loop_Invariant
           (Proof_Only =>
              BQ.Inv (W.all, NT,
                      BQ.Bound_Array (T, Logv, G0, G1, Alpha, Beta),
                      HC0, R, HC1, R));
         Bind_Step
           (W.all, NT, 0, R, HC0, HC1, T, Logv, G0, G1, Alpha, Beta);
         Bind_Step
           (W.all, NT, 1, R, HC0, HC1, T, Logv, G0, G1, Alpha, Beta);
      end loop;
      --  The scalar: the coefficients left at hands (0, 0).
      BQ.Lemma_W_Zero (W.all, 0, 0, 0);
      for I in 0 .. NT - 1 loop
         BQ.Lemma_W_Step (W.all, I, 0, 0, 0);
         if W (W'First + I).H0 = 0 and then W (W'First + I).H1 = 0 then
            SA.Lemma_Add_W (S, W (W'First + I).K);
            S := S + W (W'First + I).K;
         end if;
         pragma Loop_Invariant
           (Proof_Only => Same (S, BQ.W_Sum (W.all, I + 1, 0, 0, 0)));
      end loop;
      BQ.Lemma_Inv_At
        (W.all, NT, BQ.Bound_Array (T, Logv, G0, G1, Alpha, Beta),
         HC0, Logw, HC1, Logw, 0, 0);
      BQ.Lemma_V_End_All
        (BQ.Bound_Array (T, Logv, G0, G1, Alpha, Beta), T, T'Length,
         Logv, G0, G1, HC0, HC1, Logw, Alpha, Beta);
      V := S;
      Free_Terms (W);
   end Bind_Quad;

end Sumcheck_HQuad;
