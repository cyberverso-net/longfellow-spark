pragma SPARK_Mode (On);

package body Sumcheck_Algebra is

   function "+" (A, B : Element) return Element is
   begin
      return F."+" (A, B);
   end "+";

   function "-" (A, B : Element) return Element is
   begin
      return F."-" (A, B);
   end "-";

   function "*" (A, B : Element) return Element is
   begin
      return F."*" (A, B);
   end "*";

   function Neg (A : Element) return Element is
   begin
      return F.Neg (A);
   end Neg;

   function Bit_Of (X : Natural; B : Natural) return Boolean is
   begin
      return (Shift_Right (Unsigned_64 (X), B) and 1) = 1;
   end Bit_Of;

   ----------------------------------------------------------------------
   --  Eq
   ----------------------------------------------------------------------

   function Eq (R : Element_Array; X : Natural; N : Natural)
                return Element
   is
      P : Element := One;
   begin
      for B in 0 .. N - 1 loop
         if Bit_Of (X, B) then
            P := P * R (B);
         else
            P := P * (One - R (B));
         end if;
         pragma Loop_Invariant (Same (P, Eq_Ref (R, X, B + 1)));
      end loop;
      return P;
   end Eq;

   ----------------------------------------------------------------------
   --  Bindeq: from a_N = [One], expand a_{K+1} (Size elements) into a_K
   --  (2 Size elements) in place, highest index first so that no
   --  element is overwritten before it is read.
   ----------------------------------------------------------------------

   --  Pow2 is non-decreasing.
   procedure Lemma_Pow2_Mono (A, B : Natural) with
     Ghost, Global => null,
     Pre  => A <= B and then B <= Max_Bindeq_Log,
     Post => Pow2 (A) <= Pow2 (B),
     Subprogram_Variant => (Decreases => B);

   procedure Lemma_Pow2_Mono (A, B : Natural) is
   begin
      if B > A then
         Lemma_Pow2_Mono (A, B - 1);
      end if;
   end Lemma_Pow2_Mono;

   procedure Bindeq (C : Element_Array; B : out Element_Array) is
      N    : constant Natural := C'Length;
      Size : Positive := 1;
      T    : Element;
   begin
      B := [others => Zero];
      B (0) := One;
      for K in reverse 0 .. N - 1 loop
         pragma Loop_Invariant (To_Big_Integer (Size) = Pow2 (N - 1 - K));
         pragma Loop_Invariant
           (for all I in 0 .. Size - 1 =>
              Same (B (I), Bindeq_Ref (C, K + 1, I)));
         Lemma_Pow2_Mono (N - K, N);
         pragma Assert (2 * Size <= B'Length);
         for I in reverse 0 .. Size - 1 loop
            T := B (I);
            B (2 * I + 1) := C (K) * T;
            B (2 * I)     := (One - C (K)) * T;
            pragma Loop_Invariant
              (for all J in 0 .. I - 1 =>
                 Same (B (J), Bindeq_Ref (C, K + 1, J)));
            pragma Loop_Invariant
              (for all J in 2 * I .. 2 * Size - 1 =>
                 Same (B (J), Bindeq_Ref (C, K, J)));
         end loop;
         Size := 2 * Size;
      end loop;
   end Bindeq;

   ----------------------------------------------------------------------
   --  Bind
   ----------------------------------------------------------------------

   procedure Bind (A : Element_Array; X : Element; B : out Element_Array)
   is
   begin
      B := [others => Zero];
      for I in B'Range loop
         B (I) := (One - X) * Pad (A, 2 * I) + X * Pad (A, 2 * I + 1);
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              Same (B (J),
                    (One - X) * Pad (A, 2 * J) + X * Pad (A, 2 * J + 1)));
      end loop;
   end Bind;

   ----------------------------------------------------------------------
   --  Eval_Quad
   ----------------------------------------------------------------------

   procedure Eval_Quad (W : Element_Array; Base : Natural; T : Term_Array;
                        V : out Element_Array; OK : out Boolean)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Acc_Ref);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Z_Ref);
   begin
      V  := [others => Zero];
      OK := True;
      for I in T'Range loop
         pragma Loop_Invariant (OK = Z_Ref (W, Base, T, I - T'First));
         pragma Loop_Invariant
           (for all G in V'Range =>
              Same (V (G), Acc_Ref (W, Base, T, I - T'First, G)));
         declare
            Tm : constant Term := T (I);
         begin
            if Tm.K = Zero then
               if W (Base + Tm.H1) * W (Base + Tm.H0) /= Zero then
                  OK := False;
               end if;
            else
               V (Tm.G) := V (Tm.G)
                 + ((Tm.K * W (Base + Tm.H1)) * W (Base + Tm.H0));
            end if;
         end;
      end loop;
   end Eval_Quad;

   ----------------------------------------------------------------------
   --  Lemmas for Eval_Circuit (ghost procedures, bodies proved).
   ----------------------------------------------------------------------

   --  Off is non-decreasing in the segment index.
   procedure Lemma_Off_Mono (C : Circuit; I, J : Natural) with
     Ghost, Global => null,
     Pre  => I <= J and then J <= C.Last_Layer + 2,
     Post => Off (C, I) <= Off (C, J),
     Subprogram_Variant => (Decreases => J);

   procedure Lemma_Off_Mono (C : Circuit; I, J : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Off);
   begin
      if J > I then
         Lemma_Off_Mono (C, I, J - 1);
      end if;
   end Lemma_Off_Mono;

   --  One step of the definition of Off, for the callers that do not see
   --  its body.
   procedure Lemma_Off_Step (C : Circuit; J : Natural) with
     Ghost, Global => null,
     Pre  => J <= C.Last_Layer + 1,
     Post => Off (C, J + 1) = Off (C, J) + Seg_Size (C, J);

   procedure Lemma_Off_Step (C : Circuit; J : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Off);
   begin
      null;
   end Lemma_Off_Step;

   --  Acc_Ref and Z_Ref read the buffer at indices >= Base only: two
   --  buffers of the same length that agree from Base on give the
   --  same values.
   procedure Lemma_Acc_Frame (B1, B2 : Element_Array; Base : Natural;
                              T : Term_Array; N : Natural; G : Natural)
   with
     Ghost, Global => null,
     Pre  => B1'First = 0 and then B2'First = 0
       and then B1'Length = B2'Length
       and then Base <= Natural'Last - Max_Wires
       and then N <= T'Length
       and then (for all K in Base .. B1'Last => Same (B1 (K), B2 (K))),
     Post => Same (Acc_Ref (B1, Base, T, N, G), Acc_Ref (B2, Base, T, N, G))
       and then Z_Ref (B1, Base, T, N) = Z_Ref (B2, Base, T, N),
     Subprogram_Variant => (Decreases => N);

   procedure Lemma_Acc_Frame (B1, B2 : Element_Array; Base : Natural;
                              T : Term_Array; N : Natural; G : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Acc_Ref);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Z_Ref);
   begin
      if N > 0 then
         Lemma_Acc_Frame (B1, B2, Base, T, N - 1, G);
         pragma Assert
           (Same (W_At (B1, Base + T (T'First + N - 1).H1),
                  W_At (B2, Base + T (T'First + N - 1).H1)));
         pragma Assert
           (Same (W_At (B1, Base + T (T'First + N - 1).H0),
                  W_At (B2, Base + T (T'First + N - 1).H0)));
      end if;
   end Lemma_Acc_Frame;

   --  Two buffers of the same length that agree from Off (C, From + 1)
   --  on: a layer J above From that holds in B1 holds in B2, and its Z
   --  status is the same in both.
   procedure Lemma_Layer_Frame (C : Circuit; B1, B2 : Element_Array;
                                J, From : Natural)
   with
     Ghost, Global => null,
     Pre  => B1'First = 0 and then B2'First = 0
       and then B1'Length = B2'Length
       and then From < J and then J <= C.Last_Layer
       and then (for all K in Off (C, From + 1) .. B1'Last =>
                   Same (B1 (K), B2 (K)))
       and then Layer_Holds (C, B1, J),
     Post => Layer_Holds (C, B2, J)
       and then Layer_Z (C, B1, J) = Layer_Z (C, B2, J);

   procedure Lemma_Layer_Frame (C : Circuit; B1, B2 : Element_Array;
                                J, From : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Layer_Holds);
   begin
      Lemma_Off_Mono (C, From + 1, J);
      Lemma_Off_Mono (C, From + 1, J + 1);
      for G in 0 .. Seg_Size (C, J) - 1 loop
         Lemma_Acc_Frame (B1, B2, Off (C, J + 1), Layer_Terms (C, J),
                          Layer_Terms (C, J)'Length, G);
         pragma Loop_Invariant
           (for all G2 in 0 .. G =>
              Same (Acc_Ref (B1, Off (C, J + 1), Layer_Terms (C, J),
                             Layer_Terms (C, J)'Length, G2),
                    Acc_Ref (B2, Off (C, J + 1), Layer_Terms (C, J),
                             Layer_Terms (C, J)'Length, G2)));
      end loop;
      Lemma_Acc_Frame (B1, B2, Off (C, J + 1), Layer_Terms (C, J),
                       Layer_Terms (C, J)'Length, 0);
   end Lemma_Layer_Frame;

   --  Same agreement: the references of layer From (which read segment
   --  From + 1 only) are the same in both buffers.
   procedure Lemma_From_Frame (C : Circuit; B1, B2 : Element_Array;
                               From : Natural)
   with
     Ghost, Global => null,
     Pre  => B1'First = 0 and then B2'First = 0
       and then B1'Length = B2'Length
       and then From <= C.Last_Layer
       and then (for all K in Off (C, From + 1) .. B1'Last =>
                   Same (B1 (K), B2 (K))),
     Post => (for all G in 0 .. Seg_Size (C, From) - 1 =>
                Same (Acc_Ref (B1, Off (C, From + 1),
                               Layer_Terms (C, From),
                               Layer_Terms (C, From)'Length, G),
                      Acc_Ref (B2, Off (C, From + 1),
                               Layer_Terms (C, From),
                               Layer_Terms (C, From)'Length, G)))
       and then Layer_Z (C, B1, From) = Layer_Z (C, B2, From);

   procedure Lemma_From_Frame (C : Circuit; B1, B2 : Element_Array;
                               From : Natural)
   is
   begin
      for G in 0 .. Seg_Size (C, From) - 1 loop
         Lemma_Acc_Frame (B1, B2, Off (C, From + 1), Layer_Terms (C, From),
                          Layer_Terms (C, From)'Length, G);
         pragma Loop_Invariant
           (for all G2 in 0 .. G =>
              Same (Acc_Ref (B1, Off (C, From + 1), Layer_Terms (C, From),
                             Layer_Terms (C, From)'Length, G2),
                    Acc_Ref (B2, Off (C, From + 1), Layer_Terms (C, From),
                             Layer_Terms (C, From)'Length, G2)));
      end loop;
      Lemma_Acc_Frame (B1, B2, Off (C, From + 1), Layer_Terms (C, From),
                       Layer_Terms (C, From)'Length, 0);
   end Lemma_From_Frame;

   --  Segment J of Wires holds V, and V is the quad sum of segment J + 1
   --  of Wires: then layer J holds in Wires.
   procedure Lemma_Layer_Intro (C : Circuit; Wires : Element_Array;
                                J : Natural; V : Element_Array)
   with
     Ghost, Global => null,
     Pre  => Wires'First = 0 and then J <= C.Last_Layer
       and then V'First = 0 and then V'Length = Seg_Size (C, J)
       and then Off (C, J) + Seg_Size (C, J) <= Wires'Length
       and then (for all G in V'Range =>
                   Same (Wires (Off (C, J) + G), V (G)))
       and then (for all G in V'Range =>
                   Same (V (G),
                         Acc_Ref (Wires, Off (C, J + 1), Layer_Terms (C, J),
                                  Layer_Terms (C, J)'Length, G))),
     Post => Layer_Holds (C, Wires, J);

   procedure Lemma_Layer_Intro (C : Circuit; Wires : Element_Array;
                                J : Natural; V : Element_Array)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Layer_Holds);
   begin
      null;
   end Lemma_Layer_Intro;

   ----------------------------------------------------------------------
   --  Eval_Circuit
   ----------------------------------------------------------------------

   procedure Eval_Circuit (C : Circuit; W : Element_Array;
                           Wires : in out Element_Array; OK : out Boolean)
   is
      In_Base : constant Natural := Off (C, C.Last_Layer + 1);
   begin
      --  Segment NL is the input.
      Lemma_Off_Step (C, C.Last_Layer + 1);
      for I in 0 .. C.Ninput - 1 loop
         Wires (In_Base + I) := W (I);
         pragma Loop_Invariant
           (for all K in 0 .. I => Same (Wires (In_Base + K), W (K)));
      end loop;

      OK := True;
      for J in reverse 0 .. C.Last_Layer loop
         pragma Loop_Invariant
           (for all I in 0 .. C.Ninput - 1 =>
              Same (Wires (In_Base + I), W (I)));
         pragma Loop_Invariant
           (for all J2 in J + 1 .. C.Last_Layer => Layer_Holds (C, Wires, J2));
         pragma Loop_Invariant
           (OK = (for all J2 in J + 1 .. C.Last_Layer =>
                    Layer_Z (C, Wires, J2)));
         Lemma_Off_Step (C, J);
         Lemma_Off_Step (C, J + 1);
         Lemma_Off_Mono (C, J + 2, C.Last_Layer + 2);
         Lemma_Off_Mono (C, J + 1, C.Last_Layer + 1);
         declare
            Size     : constant Wire_Count := Seg_Size (C, J);
            Base_In  : constant Natural := Off (C, J + 1);
            Base_Out : constant Natural := Off (C, J);
            V        : Element_Array (0 .. Size - 1);
            Layer_OK : Boolean;
            Before   : constant Element_Array := Wires with Ghost;
         begin
            Eval_Quad (Wires, Base_In, Layer_Terms (C, J), V, Layer_OK);
            OK := OK and Layer_OK;
            for G in 0 .. Size - 1 loop
               Wires (Base_Out + G) := V (G);
               pragma Loop_Invariant
                 (for all K in 0 .. G => Same (Wires (Base_Out + K), V (K)));
               pragma Loop_Invariant
                 (for all K in Wires'Range =>
                    (if K < Base_Out or else K > Base_Out + G
                     then Same (Wires (K), Before (K))));
            end loop;
            for J2 in J + 1 .. C.Last_Layer loop
               pragma Loop_Invariant
                 (for all J3 in J + 1 .. J2 - 1 =>
                    Layer_Holds (C, Wires, J3)
                    and then Layer_Z (C, Before, J3) = Layer_Z (C, Wires, J3));
               Lemma_Layer_Frame (C, Before, Wires, J2, J);
            end loop;
            Lemma_From_Frame (C, Before, Wires, J);
            Lemma_Layer_Intro (C, Wires, J, V);
         end;
      end loop;

      pragma Assert
        (OK = (for all J in 0 .. C.Last_Layer => Layer_Z (C, Wires, J)));
      for G in 0 .. C.Noutput - 1 loop
         if Wires (G) /= Zero then
            OK := False;
         end if;
         pragma Loop_Invariant
           (OK = ((for all J in 0 .. C.Last_Layer => Layer_Z (C, Wires, J))
                  and then (for all K in 0 .. G => Wires (K) = Zero)));
      end loop;
   end Eval_Circuit;

   ----------------------------------------------------------------------
   --  Bind_G
   ----------------------------------------------------------------------

   procedure Bind_G (T : in out Term_Array; Logv : Natural;
                     G0, G1 : Element_Array; Alpha, Beta : Element)
   is
      Before : constant Term_Array := T with Ghost;
   begin
      for I in T'Range loop
         T (I).K := Bound_K (T (I), Logv, G0, G1, Alpha, Beta);
         T (I).G := 0;
         pragma Loop_Invariant
           (for all J in T'First .. I =>
              Same (T (J).K, Bound_K (Before (J), Logv, G0, G1, Alpha, Beta))
              and then T (J).G = 0
              and then T (J).H0 = Before (J).H0
              and then T (J).H1 = Before (J).H1);
         pragma Loop_Invariant
           (for all J in I + 1 .. T'Last =>
              Same (T (J).K, Before (J).K)
              and then T (J).G = Before (J).G
              and then T (J).H0 = Before (J).H0
              and then T (J).H1 = Before (J).H1);
      end loop;
   end Bind_G;

   ----------------------------------------------------------------------
   --  Eval_Bound_Quad
   ----------------------------------------------------------------------

   function Eval_Bound_Quad (T : Term_Array; Logv : Natural;
                             G0, G1 : Element_Array;
                             HC0, HC1 : Element_Array; Logw : Natural;
                             Alpha, Beta : Element) return Element
   is
      S : Element := Zero;
   begin
      for I in T'Range loop
         S := S + ((Bound_K (T (I), Logv, G0, G1, Alpha, Beta)
                      * Eq (HC0, T (I).H0, Logw))
                   * Eq (HC1, T (I).H1, Logw));
         pragma Loop_Invariant
           (Same (S, EBQ_Ref (T, I - T'First + 1, Logv, G0, G1, HC0, HC1,
                              Logw, Alpha, Beta)));
      end loop;
      return S;
   end Eval_Bound_Quad;

end Sumcheck_Algebra;
