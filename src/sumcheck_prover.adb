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
   procedure Update_Terms (T : Terms_Access; H : Hand; X : Element) with
     Global => null,
     Pre    => T /= null;

   procedure Update_Terms (T : Terms_Access; H : Hand; X : Element) is
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
      N0, N1 : Natural;
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
            ST.SA.Bind_G (T.all, Logv, Cur0, Cur1, Alpha, Beta);
            for R in 0 .. Logw - 1 loop
               pragma Loop_Invariant
                 (T /= null and then A0 /= null and then A1 /= null
                  and then B0 /= null and then B1 /= null);
               pragma Loop_Invariant
                 (A0'First = 0 and then A1'First = 0
                  and then B0'First = 0 and then B1'First = 0
                  and then A0'Length = NW and then A1'Length = NW
                  and then B0'Length = NW and then B1'Length = NW);
               pragma Loop_Invariant (N0 <= NW and then N1 <= NW);
               pragma Loop_Invariant (Proof.Last + 1 = ST.SV.Proof_Total (C));
               pragma Loop_Invariant (Ch.Last + 1 = ST.SV.Chal_Total (C));
               --  Hand 0 on A0 against A1, then hand 1 on A1 against the
               --  bound A0, as the reference does.
               Round_Evals (T.all, A0.all, N0, A1.all, N1, 0, P2, Ev0, Ev2);
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
               Update_Terms (T, 0, Chal);
               Round_Evals (T.all, A1.all, N1, A0.all, N0, 1, P2, Ev0, Ev2);
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
               Update_Terms (T, 1, Chal);
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
         end;
      end loop;
      ST.Sample (Ch.Alpha_Input);
   end Prove;

end Sumcheck_Prover;
