pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;

package body Packed_HQuad is

   --  Heap buffers (ADR 0047): the merged entries and the eq2 table of
   --  Bind_Quad_Packed.
   type Elems_Access is access Element_Array;
   type Terms_Access is access Term_Array;

   procedure Free_Elems is
     new Ada.Unchecked_Deallocation (Element_Array, Elems_Access);
   procedure Free_Terms is
     new Ada.Unchecked_Deallocation (Term_Array, Terms_Access);

   --  The same term: the same hands and output wire, the same
   --  coefficient by Same, as the body of Sumcheck_HQuad states it (the
   --  equality of the field may not be the logical one).
   function Same_Term (A, B : Term) return Boolean is
     (Same (A.K, B.K) and then A.G = B.G
      and then A.H0 = B.H0 and then A.H1 = B.H1)
   with Ghost => Proof_Only, Global => null;

   -------------------------------------------------------------------
   --  The runs. Run_Id and Run_Sum are hidden in Sumcheck_HQuad; the
   --  lemmas below give one step of each, as the body of Sumcheck_HQuad
   --  does for Merge_Runs.
   -------------------------------------------------------------------

   procedure Lemma_Run_Id_Zero (T : Term_Array)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => T'Length >= 1,
     Post   => HQ.Run_Id (T, 0) = 0
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", HQ.Run_Id);
   begin
      null;
   end Lemma_Run_Id_Zero;

   procedure Lemma_Run_Id_Step (T : Term_Array; I : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => I >= 1 and then I < T'Length,
     Post   =>
       HQ.Run_Id (T, I)
       = (if HQ.Same_Hands (T (T'First + I - 1), T (T'First + I))
          then HQ.Run_Id (T, I - 1)
          else HQ.Run_Id (T, I - 1) + 1)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", HQ.Run_Id);
   begin
      null;
   end Lemma_Run_Id_Step;

   --  Run_Id does not decrease along the terms.
   procedure Lemma_Run_Id_Mono (T : Term_Array; I, L : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => I <= L and then L < T'Length,
     Post   => HQ.Run_Id (T, I) <= HQ.Run_Id (T, L),
     Subprogram_Variant => (Decreases => L)
   is
   begin
      if L > I then
         Lemma_Run_Id_Step (T, L);
         Lemma_Run_Id_Mono (T, I, L - 1);
      end if;
   end Lemma_Run_Id_Mono;

   --  Run_Id reads only the hands.
   procedure Lemma_Run_Id_Hands (A, B : Term_Array; I : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => A'First = B'First and then A'Length = B'Length
               and then I < A'Length
               and then
               (for all X in A'Range =>
                  A (X).H0 = B (X).H0 and then A (X).H1 = B (X).H1),
     Post   => HQ.Run_Id (A, I) = HQ.Run_Id (B, I),
     Subprogram_Variant => (Decreases => I)
   is
   begin
      if I = 0 then
         Lemma_Run_Id_Zero (A);
         Lemma_Run_Id_Zero (B);
      else
         Lemma_Run_Id_Step (A, I);
         Lemma_Run_Id_Step (B, I);
         Lemma_Run_Id_Hands (A, B, I - 1);
      end if;
   end Lemma_Run_Id_Hands;

   procedure Lemma_Run_Sum_Step (T : Term_Array; N : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N >= 1 and then N <= T'Length,
     Post   =>
       (for all X in Natural =>
          Same (HQ.Run_Sum (T, X, N),
                (if HQ.Run_Id (T, N - 1) = X
                 then HQ.Run_Sum (T, X, N - 1) + T (T'First + N - 1).K
                 else HQ.Run_Sum (T, X, N - 1))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", HQ.Run_Sum);
   begin
      null;
   end Lemma_Run_Sum_Step;

   --  A run not reached yet has the coefficient zero.
   procedure Lemma_Run_Sum_Zero (T : Term_Array; X : Natural; N : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N <= T'Length
               and then (N = 0 or else X > HQ.Run_Id (T, N - 1)),
     Post   => Same (HQ.Run_Sum (T, X, N), Zero),
     Subprogram_Variant => (Decreases => N)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", HQ.Run_Sum);
   begin
      if N >= 1 then
         if N >= 2 then
            Lemma_Run_Id_Step (T, N - 1);
         end if;
         Lemma_Run_Sum_Zero (T, X, N - 1);
      end if;
   end Lemma_Run_Sum_Zero;

   -------------------------------------------------------------------
   --  Layer_Runs
   -------------------------------------------------------------------

   procedure Layer_Runs (P : PC.Packed_Circuit; J : Natural; N : out Natural)
   is
      T0    : constant Term_Array := Layer_Of (P, J)
      with Ghost => Proof_Only;
      First : constant Positive := P.Layers (J).First;
      Len   : constant Natural := PC.Layer_Len (P, J);
      C     : PC.Cursor;
      Prev  : Term;
      Tm    : Term;
   begin
      if Len = 0 then
         N := 0;
         return;
      end if;
      PC.Lemma_Valid (P);
      pragma Assert (Proof_Only => T0'First = First and then T0'Length = Len);
      C := PC.Start (P, J);
      PC.Lemma_Walked_Start (P, J);
      PC.Lemma_Walked_Step (P, J, 1, C);
      Prev := PC.Term_Of (P, C);
      pragma Assert (Proof_Only => Prev = T0 (First));
      Lemma_Run_Id_Zero (T0);
      C := PC.Step (P, C);
      N := 1;
      for K in 2 .. Len loop
         pragma Loop_Invariant (N <= K - 1);
         pragma Loop_Invariant (Proof_Only => PC.Walked (P, J, K - 1, C));
         pragma Loop_Invariant
           (Proof_Only => N = HQ.Run_Id (T0, K - 2) + 1);
         pragma Loop_Invariant (Proof_Only => Prev = T0 (First + K - 2));
         PC.Lemma_Walked_Step (P, J, K, C);
         Tm := PC.Term_Of (P, C);
         pragma Assert (Proof_Only => Tm = T0 (First + K - 1));
         Lemma_Run_Id_Step (T0, K - 1);
         if not HQ.Same_Hands (Prev, Tm) then
            N := N + 1;
         end if;
         Prev := Tm;
         C := PC.Step (P, C);
      end loop;
   end Layer_Runs;

   -------------------------------------------------------------------
   --  Bind_Merge
   -------------------------------------------------------------------

   --  The coefficient of a term bound with g: with the table as
   --  Bind_G_T, without it as Bind_G.
   function Bound_Coef
     (Tm     : Term;
      E      : Element_Array;
      Logv   : Natural;
      G0, G1 : Element_Array;
      Alpha  : Element;
      Beta   : Element) return Element
   is
     (if Logv <= SA.Max_Bindeq_Log
      then (if Tm.K = Zero then Beta * HQ.Ref (E, E'Length, Tm.G)
            else Tm.K * HQ.Ref (E, E'Length, Tm.G))
      else SA.Bound_K (Tm, Logv, G0, G1, Alpha, Beta))
   with Global => null,
        Pre => G0'First = 0 and then G1'First = 0
               and then Logv <= G0'Length and then Logv <= G1'Length
               and then Logv <= SA.Max_Logw
               and then E'First = 0;

   --  With the table, the coefficient is Bound_KT: Lemma_T1_Bound on a
   --  layer of one term.
   procedure Lemma_Coef
     (Tm     : Term;
      E      : Element_Array;
      Logv   : Natural;
      G0, G1 : Element_Array;
      Alpha  : Element;
      Beta   : Element)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => G0'First = 0 and then G1'First = 0
               and then Logv <= G0'Length and then Logv <= G1'Length
               and then Logv <= SA.Max_Bindeq_Log
               and then E'First = 0
               and then E'Last = SA.Table_Len (Logv) - 1
               and then (for all X in E'Range =>
                           Same (E (X), SA.Beq2 (X, Logv, G0, G1, Alpha))),
     Post   => Same (Bound_Coef (Tm, E, Logv, G0, G1, Alpha, Beta),
                     SA.Bound_KT (Tm, Logv, G0, G1, Alpha, Beta))
   is
      A0 : constant Term_Array (1 .. 1) := [1 => Tm];
      A1 : constant Term_Array (1 .. 1) :=
        [1 => (K  => Bound_Coef (Tm, E, Logv, G0, G1, Alpha, Beta),
               G  => 0,
               H0 => Tm.H0,
               H1 => Tm.H1)];
   begin
      HQ.BQ.Lemma_T1_Bound (A0, A1, E, Logv, G0, G1, Alpha, Beta);
   end Lemma_Coef;

   --  The merge of the first N terms of T1 into W, as Merge_Runs keeps
   --  it: X is the run of term N, its entry has the hands of term N,
   --  every term's run has its hands, and with the tables (Tab) the
   --  entries hold the sums of their runs. Hidden, so that the loop of
   --  Bind_Merge carries it whole; the lemmas below give its steps.
   function Merged
     (W   : Term_Array;
      X   : Natural;
      T1  : Term_Array;
      N   : Natural;
      Tab : Boolean) return Boolean
   is
     (N >= 1 and then N <= T1'Length and then W'First = T1'First
      and then X < W'Length
      and then X = HQ.Run_Id (T1, N - 1)
      and then W (W'First + X).H0 = T1 (T1'First + N - 1).H0
      and then W (W'First + X).H1 = T1 (T1'First + N - 1).H1
      and then
      (if Tab then
         (for all Y in 0 .. X =>
            Same (W (W'First + Y).K, HQ.Run_Sum (T1, Y, N))))
      and then
      (for all I in 0 .. N - 1 =>
         HQ.Run_Id (T1, I) <= X
         and then HQ.Same_Hands (W (W'First + HQ.Run_Id (T1, I)),
                                 T1 (T1'First + I))))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   --  What a step of the loop reads of Merged: the current run, its
   --  entry and its hands.
   procedure Lemma_Merged_At
     (W : Term_Array; X : Natural; T1 : Term_Array; N : Natural;
      Tab : Boolean)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Merged (W, X, T1, N, Tab),
     Post   => N >= 1 and then N <= T1'Length and then W'First = T1'First
               and then X < W'Length
               and then X = HQ.Run_Id (T1, N - 1)
               and then W (W'First + X).H0 = T1 (T1'First + N - 1).H0
               and then W (W'First + X).H1 = T1 (T1'First + N - 1).H1
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Merged);
   begin
      null;
   end Lemma_Merged_At;

   --  The first term opens run 0.
   procedure Lemma_Merged_First
     (W : Term_Array; T1 : Term_Array; Tab : Boolean; V : Element)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => T1'Length >= 1 and then W'First = T1'First
               and then W'Length >= 1
               and then Same (W (W'First).K, Zero + V)
               and then W (W'First).H0 = T1 (T1'First).H0
               and then W (W'First).H1 = T1 (T1'First).H1
               and then (if Tab then Same (V, T1 (T1'First).K)),
     Post   => Merged (W, 0, T1, 1, Tab)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Merged);
   begin
      Lemma_Run_Id_Zero (T1);
      Lemma_Run_Sum_Zero (T1, 0, 0);
      Lemma_Run_Sum_Step (T1, 1);
   end Lemma_Merged_First;

   --  Term N + 1 has the hands of run X: its coefficient is added.
   procedure Lemma_Merged_Add
     (W0, W1 : Term_Array;
      X      : Natural;
      T1     : Term_Array;
      N      : Natural;
      Tab    : Boolean;
      V      : Element)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Merged (W0, X, T1, N, Tab) and then N < T1'Length
               and then W1'First = W0'First and then W1'Last = W0'Last
               and then X < W0'Length
               and then T1 (T1'First + N).H0 = W0 (W0'First + X).H0
               and then T1 (T1'First + N).H1 = W0 (W0'First + X).H1
               and then Same (W1 (W1'First + X).K, W0 (W0'First + X).K + V)
               and then W1 (W1'First + X).H0 = W0 (W0'First + X).H0
               and then W1 (W1'First + X).H1 = W0 (W0'First + X).H1
               and then
               (for all Y in W0'Range =>
                  (if Y /= W0'First + X then Same_Term (W1 (Y), W0 (Y))))
               and then (if Tab then Same (V, T1 (T1'First + N).K)),
     Post   => Merged (W1, X, T1, N + 1, Tab)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Merged);
   begin
      Lemma_Run_Id_Step (T1, N);
      Lemma_Run_Sum_Step (T1, N + 1);
   end Lemma_Merged_Add;

   --  Term N + 1 opens run X + 1.
   procedure Lemma_Merged_New
     (W0, W1 : Term_Array;
      X      : Natural;
      T1     : Term_Array;
      N      : Natural;
      Tab    : Boolean;
      V      : Element)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Merged (W0, X, T1, N, Tab) and then N < T1'Length
               and then W1'First = W0'First and then W1'Last = W0'Last
               and then X + 1 < W0'Length
               and then
               not (T1 (T1'First + N).H0 = W0 (W0'First + X).H0
                    and then T1 (T1'First + N).H1 = W0 (W0'First + X).H1)
               and then Same (W1 (W1'First + X + 1).K, Zero + V)
               and then W1 (W1'First + X + 1).H0 = T1 (T1'First + N).H0
               and then W1 (W1'First + X + 1).H1 = T1 (T1'First + N).H1
               and then
               (for all Y in W0'Range =>
                  (if Y /= W0'First + X + 1
                   then Same_Term (W1 (Y), W0 (Y))))
               and then (if Tab then Same (V, T1 (T1'First + N).K)),
     Post   => Merged (W1, X + 1, T1, N + 1, Tab)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Merged);
   begin
      Lemma_Run_Id_Step (T1, N);
      Lemma_Run_Sum_Step (T1, N + 1);
      Lemma_Run_Sum_Zero (T1, X + 1, N);
   end Lemma_Merged_New;

   --  The merge of the whole layer: the facts Merge_Runs states.
   procedure Lemma_Merged_End
     (W : Term_Array; X : Natural; T1 : Term_Array; Tab : Boolean)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => T1'Length >= 1 and then Merged (W, X, T1, T1'Length, Tab),
     Post   => W'First = T1'First
               and then X + 1 = Runs (T1) and then X < W'Length
               and then
               (if Tab then
                  (for all Y in 0 .. X =>
                     Same (W (W'First + Y).K,
                           HQ.Run_Sum (T1, Y, T1'Length))))
               and then
               (for all I in 0 .. T1'Length - 1 =>
                  HQ.Run_Id (T1, I) <= X
                  and then HQ.Same_Hands (W (W'First + HQ.Run_Id (T1, I)),
                                          T1 (T1'First + I)))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Merged);
   begin
      null;
   end Lemma_Merged_End;

   --  As Merge_Terms: the runs give the invariant of the rounds at round
   --  0, stated on a ghost array of the layer's length that agrees with
   --  W on the runs, then moved to W.
   procedure Lemma_Merged_Inv
     (W      : Term_Array;
      NT     : Natural;
      T1     : Term_Array;
      C0, C1 : Element_Array)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => T1'Length >= 1 and then W'First = T1'First
               and then NT = Runs (T1) and then NT <= W'Length
               and then C0'First = 0 and then C1'First = 0
               and then
               (for all Y in 0 .. NT - 1 =>
                  Same (W (W'First + Y).K, HQ.Run_Sum (T1, Y, T1'Length)))
               and then
               (for all I in 0 .. T1'Length - 1 =>
                  HQ.Run_Id (T1, I) < NT
                  and then HQ.Same_Hands (W (W'First + HQ.Run_Id (T1, I)),
                                          T1 (T1'First + I))),
     Post   => HQ.BQ.Inv (W, NT, T1, C0, 0, C1, 0)
   is
      First : constant Positive := T1'First;
      Full  : constant Term_Array :=
        [for I in T1'Range =>
           (if I - First < NT then W (I) else T1 (I))];
   begin
      pragma Assert (NT <= T1'Length);
      pragma Assert
        (for all Y in 0 .. NT - 1 => Full (First + Y) = W (First + Y));
      pragma Assert
        (for all Y in 0 .. NT - 1 =>
           Same (Full (First + Y).K, HQ.Run_Sum (T1, Y, T1'Length)));
      pragma Assert
        (for all I in 0 .. T1'Length - 1 =>
           HQ.Same_Hands (Full (First + HQ.Run_Id (T1, I)),
                          T1 (First + I)));
      HQ.BQ.Lemma_Run_Sums_W (Full, T1, NT);
      HQ.BQ.Lemma_Inv_Base (Full, T1, NT, C0, C1);
      HQ.BQ.Lemma_Inv_Slice (Full, W, NT, T1, C0, 0, C1, 0);
   end Lemma_Merged_Inv;

   procedure Bind_Merge
     (P      : PC.Packed_Circuit;
      J      : Natural;
      E      : Element_Array;
      Logv   : Natural;
      G0, G1 : Element_Array;
      Alpha  : Element;
      Beta   : Element;
      C0, C1 : Element_Array;
      W      : in out Term_Array;
      NT     : out Natural)
   is
      Tab   : constant Boolean := Logv <= SA.Max_Bindeq_Log;
      T0    : constant Term_Array := Layer_Of (P, J)
      with Ghost => Proof_Only;
      First : constant Positive := P.Layers (J).First;
      Len   : constant Natural := PC.Layer_Len (P, J);
      C     : PC.Cursor;
      Tm    : Term;
      V     : Element;
      X     : Natural := 0;
   begin
      if Len = 0 then
         NT := 0;
         if Tab then
            --  An empty layer: the invariant on an empty slice of W.
            HQ.BQ.Lemma_Inv_Base
              (W (W'First .. W'First - 1),
               Bound_Layer (P, J, Logv, G0, G1, Alpha, Beta), 0, C0, C1);
            HQ.BQ.Lemma_Inv_Slice
              (W (W'First .. W'First - 1), W, 0,
               Bound_Layer (P, J, Logv, G0, G1, Alpha, Beta), C0, 0, C1, 0);
         end if;
         return;
      end if;
      PC.Lemma_Valid (P);
      pragma Assert (Proof_Only => T0'First = First and then T0'Length = Len);
      declare
         --  The layer bound with g when the tables are in use, the layer
         --  itself otherwise: the runs are the same (Lemma_Run_Id_Hands).
         T1 : constant Term_Array :=
           (if Tab then Bound_Layer (P, J, Logv, G0, G1, Alpha, Beta)
            else T0)
         with Ghost => Proof_Only;
      begin
         pragma Assert
           (Proof_Only =>
              T1'First = First and then T1'Length = Len
              and then
              (for all I in T1'Range =>
                 T1 (I).H0 = T0 (I).H0 and then T1 (I).H1 = T0 (I).H1
                 and then
                 (if Tab then
                    Same (T1 (I).K,
                          SA.Bound_KT (T0 (I), Logv, G0, G1, Alpha,
                                       Beta)))));
         Lemma_Run_Id_Hands (T0, T1, Len - 1);
         pragma Assert
           (Proof_Only => HQ.Run_Id (T1, Len - 1) < W'Length);
         --  The first term opens run 0.
         C := PC.Start (P, J);
         PC.Lemma_Walked_Start (P, J);
         PC.Lemma_Walked_Step (P, J, 1, C);
         Tm := PC.Term_Of (P, C);
         pragma Assert (Proof_Only => Same_Term (Tm, T0 (First)));
         V := Bound_Coef (Tm, E, Logv, G0, G1, Alpha, Beta);
         if Tab then
            Lemma_Coef (Tm, E, Logv, G0, G1, Alpha, Beta);
            pragma Assert
              (Proof_Only =>
                 Same (T1 (First).K,
                       SA.Bound_KT (Tm, Logv, G0, G1, Alpha, Beta)));
            pragma Assert (Proof_Only => Same (V, T1 (First).K));
         end if;
         W (First) := (K => Zero + V, G => 0, H0 => Tm.H0, H1 => Tm.H1);
         Lemma_Merged_First (W, T1, Tab, V);
         C := PC.Step (P, C);
         for K in 2 .. Len loop
            --  The walk is at term K - 1: the cut keeps the index.
            pragma Loop_Invariant (X <= K - 2);
            pragma Loop_Invariant
              (Proof_Only => PC.Walked (P, J, K - 1, C));
            pragma Loop_Invariant
              (Proof_Only => Merged (W, X, T1, K - 1, Tab));
            pragma Loop_Invariant
              (Proof_Only => HQ.Run_Id (T1, Len - 1) < W'Length);
            Lemma_Merged_At (W, X, T1, K - 1, Tab);
            PC.Lemma_Walked_Step (P, J, K, C);
            Tm := PC.Term_Of (P, C);
            pragma Assert (Proof_Only => Same_Term (Tm, T0 (First + K - 1)));
            pragma Assert
              (Proof_Only =>
                 Tm.H0 = T1 (First + K - 1).H0
                 and then Tm.H1 = T1 (First + K - 1).H1);
            V := Bound_Coef (Tm, E, Logv, G0, G1, Alpha, Beta);
            if Tab then
               Lemma_Coef (Tm, E, Logv, G0, G1, Alpha, Beta);
               pragma Assert
                 (Proof_Only =>
                    Same (T1 (First + K - 1).K,
                          SA.Bound_KT (Tm, Logv, G0, G1, Alpha, Beta)));
               pragma Assert
                 (Proof_Only => Same (V, T1 (First + K - 1).K));
            end if;
            declare
               W0 : constant Term_Array := W with Ghost => Proof_Only;
            begin
               if Tm.H0 = W (First + X).H0 and then Tm.H1 = W (First + X).H1
               then
                  W (First + X).K := W (First + X).K + V;
                  Lemma_Merged_Add (W0, W, X, T1, K - 1, Tab, V);
               else
                  --  Run X + 1 is the run of term K, at most the last run.
                  Lemma_Run_Id_Step (T1, K - 1);
                  Lemma_Run_Id_Mono (T1, K - 1, Len - 1);
                  pragma Assert
                    (Proof_Only => HQ.Run_Id (T1, K - 1) = X + 1);
                  W (First + X + 1) :=
                    (K => Zero + V, G => 0, H0 => Tm.H0, H1 => Tm.H1);
                  Lemma_Merged_New (W0, W, X, T1, K - 1, Tab, V);
                  X := X + 1;
               end if;
            end;
            C := PC.Step (P, C);
         end loop;
         Lemma_Merged_End (W, X, T1, Tab);
         NT := X + 1;
         pragma Assert (Proof_Only => NT = Runs (T0));
         if Tab then
            Lemma_Merged_Inv (W, NT, T1, C0, C1);
         end if;
      end;
   end Bind_Merge;

   -------------------------------------------------------------------
   --  Bind_Step_Packed: Bind_Step of Sumcheck_HQuad, T0 replaced by
   --  Layer_Of (P, J) (see the header of the spec).
   -------------------------------------------------------------------

   procedure Bind_Step_Packed
     (T        : in out Term_Array;
      NT       : in out Natural;
      H        : HQ.Hand;
      R        : Natural;
      HC0, HC1 : Element_Array;
      P        : PC.Packed_Circuit;
      J        : Natural;
      Logv     : Natural;
      G0, G1   : Element_Array;
      Alpha    : Element;
      Beta     : Element)
   is
      Chal : constant Element := (if H = 0 then HC0 (R) else HC1 (R));
      Old  : constant Term_Array := T (T'First .. T'First + NT - 1)
      with Ghost => Proof_Only;
      T1   : constant Term_Array :=
        Bound_Layer (P, J, Logv, G0, G1, Alpha, Beta)
      with Ghost => Proof_Only;
      NB   : Natural;
   begin
      HQ.BQ.Lemma_Inv_Slice
        (T, Old, NT, T1, HC0, (if H = 0 then R else R + 1), HC1, R);
      HQ.Bind_H (T (T'First .. T'First + NT - 1), H, Chal, NB);
      HQ.BQ.Lemma_Corners_W
        (Old, T (T'First .. T'First + NT - 1), H, Chal, NB);
      if H = 0 then
         HQ.BQ.Lemma_Inv_Step0
           (Old, T (T'First .. T'First + NT - 1), NB, T1, HC0, R, HC1, R);
         HQ.BQ.Lemma_Inv_Slice
           (T (T'First .. T'First + NT - 1), T, NB, T1, HC0, R + 1, HC1, R);
      else
         HQ.BQ.Lemma_Inv_Step1
           (Old, T (T'First .. T'First + NT - 1), NB, T1, HC0, R + 1, HC1,
            R);
         HQ.BQ.Lemma_Inv_Slice
           (T (T'First .. T'First + NT - 1), T, NB, T1, HC0, R + 1, HC1,
            R + 1);
      end if;
      NT := NB;
   end Bind_Step_Packed;

   -------------------------------------------------------------------
   --  Bind_Quad_Packed
   -------------------------------------------------------------------

   procedure Bind_Quad_Packed
     (P           : PC.Packed_Circuit;
      J           : Natural;
      Logv        : Natural;
      G0, G1      : Element_Array;
      HC0, HC1    : Element_Array;
      Logw        : Natural;
      Alpha, Beta : Element;
      V           : out Element)
   is
      T0    : constant Term_Array := Layer_Of (P, J)
      with Ghost => Proof_Only;
      T1    : constant Term_Array :=
        Bound_Layer (P, J, Logv, G0, G1, Alpha, Beta)
      with Ghost => Proof_Only;
      First : constant Positive := P.Layers (J).First;
      NR    : Natural;
      W     : Terms_Access;
      E     : Elems_Access;
      NT    : Natural;
      S     : Element := Zero;
   begin
      PC.Lemma_Valid (P);
      Layer_Runs (P, J, NR);
      W := new Term_Array'
        (First .. First + NR - 1 => (K => Zero, G => 0, H0 => 0, H1 => 0));
      E := new Element_Array'(0 .. SA.Table_Len (Logv) - 1 => Zero);
      --  bind_g with the eq2 table and the runs merged, from the walk.
      SA.Eq2_Table (Logv, G0, G1, Alpha, E.all);
      Bind_Merge
        (P, J, E.all, Logv, G0, G1, Alpha, Beta, HC0, HC1, W.all, NT);
      Free_Elems (E);
      --  bind_h of hand 0 then hand 1, Logw rounds.
      for R in 0 .. Logw - 1 loop
         pragma Loop_Invariant (W /= null);
         pragma Loop_Invariant (W'First = First);
         pragma Loop_Invariant (NT <= W'Length);
         pragma Loop_Invariant
           (Proof_Only => HQ.BQ.Inv (W.all, NT, T1, HC0, R, HC1, R));
         Bind_Step_Packed
           (W.all, NT, 0, R, HC0, HC1, P, J, Logv, G0, G1, Alpha, Beta);
         Bind_Step_Packed
           (W.all, NT, 1, R, HC0, HC1, P, J, Logv, G0, G1, Alpha, Beta);
      end loop;
      --  The scalar: the coefficients left at hands (0, 0).
      HQ.BQ.Lemma_W_Zero (W.all, 0, 0, 0);
      for I in 0 .. NT - 1 loop
         HQ.BQ.Lemma_W_Step (W.all, I, 0, 0, 0);
         if W (W'First + I).H0 = 0 and then W (W'First + I).H1 = 0 then
            SA.Lemma_Add_W (S, W (W'First + I).K);
            S := S + W (W'First + I).K;
         end if;
         pragma Loop_Invariant
           (Proof_Only => Same (S, HQ.BQ.W_Sum (W.all, I + 1, 0, 0, 0)));
      end loop;
      HQ.BQ.Lemma_Inv_At (W.all, NT, T1, HC0, Logw, HC1, Logw, 0, 0);
      pragma Assert
        (Proof_Only =>
           Same (S, HQ.BQ.V_Sum (T1, T1'Length, HC0, Logw, HC1, Logw, 0, 0)));
      HQ.BQ.Lemma_V_End_All
        (T1, T0, T0'Length, Logv, G0, G1, HC0, HC1, Logw, Alpha, Beta);
      pragma Assert (Proof_Only => T1'Length = T0'Length);
      pragma Assert
        (Proof_Only =>
           Same (S, SA.EBQT_Ref (T0, T0'Length, Logv, G0, G1, HC0, HC1, Logw,
                                 Alpha, Beta)));
      V := S;
      Free_Terms (W);
   end Bind_Quad_Packed;

   -------------------------------------------------------------------
   --  Eval_Bound_Quad_Packed
   -------------------------------------------------------------------

   --  One term of EBQ_Ref: the term at N - 1 is Tm.
   procedure Lemma_EBQ_Step
     (T           : Term_Array;
      N           : Natural;
      Tm          : Term;
      Logv        : Natural;
      G0, G1      : Element_Array;
      HC0, HC1    : Element_Array;
      Logw        : Natural;
      Alpha, Beta : Element)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N >= 1 and then N <= T'Length
               and then Same_Term (T (T'First + N - 1), Tm)
               and then G0'First = 0 and then G1'First = 0
               and then Logv <= G0'Length and then Logv <= G1'Length
               and then Logv <= SA.Max_Logw
               and then HC0'First = 0 and then HC1'First = 0
               and then Logw <= HC0'Length and then Logw <= HC1'Length
               and then Logw <= SA.Max_Logw,
     Post   =>
       Same (SA.EBQ_Ref (T, N, Logv, G0, G1, HC0, HC1, Logw, Alpha, Beta),
             SA."+" (SA.EBQ_Ref (T, N - 1, Logv, G0, G1, HC0, HC1, Logw,
                                 Alpha, Beta),
                     SA."*" (SA."*" (SA.Bound_K (Tm, Logv, G0, G1, Alpha,
                                                 Beta),
                                     SA.Eq (HC0, Tm.H0, Logw)),
                             SA.Eq (HC1, Tm.H1, Logw))))
   is
   begin
      null;
   end Lemma_EBQ_Step;

   procedure Eval_Bound_Quad_Packed
     (P           : PC.Packed_Circuit;
      J           : Natural;
      Logv        : Natural;
      G0, G1      : Element_Array;
      HC0, HC1    : Element_Array;
      Logw        : Natural;
      Alpha, Beta : Element;
      V           : out Element)
   is
      T0    : constant Term_Array := Layer_Of (P, J)
      with Ghost => Proof_Only;
      First : constant Positive := P.Layers (J).First;
      Len   : constant Natural := PC.Layer_Len (P, J);
      C     : PC.Cursor;
      Tm    : Term;
      S     : Element := Zero;
   begin
      PC.Lemma_Valid (P);
      pragma Assert (Proof_Only => T0'First = First and then T0'Length = Len);
      C := PC.Start (P, J);
      PC.Lemma_Walked_Start (P, J);
      for K in 1 .. Len loop
         pragma Loop_Invariant (Proof_Only => PC.Walked (P, J, K - 1, C));
         pragma Loop_Invariant
           (Proof_Only =>
              Same (S, SA.EBQ_Ref (T0, K - 1, Logv, G0, G1, HC0, HC1, Logw,
                                   Alpha, Beta)));
         PC.Lemma_Walked_Step (P, J, K, C);
         Tm := PC.Term_Of (P, C);
         pragma Assert (Proof_Only => Same_Term (T0 (First + K - 1), Tm));
         Lemma_EBQ_Step
           (T0, K, Tm, Logv, G0, G1, HC0, HC1, Logw, Alpha, Beta);
         --  The operations of the reference, those of Sumcheck_Algebra.
         S := SA."+" (S, SA."*" (SA."*" (SA.Bound_K (Tm, Logv, G0, G1,
                                                     Alpha, Beta),
                                         SA.Eq (HC0, Tm.H0, Logw)),
                                 SA.Eq (HC1, Tm.H1, Logw)));
         C := PC.Step (P, C);
      end loop;
      V := S;
   end Eval_Bound_Quad_Packed;

end Packed_HQuad;
