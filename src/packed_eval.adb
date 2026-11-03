pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;

package body Packed_Eval is

   use SA.F;
   use type SA.Term;
   use type SA.Term_Array;
   use type SA.Layer;

   --  The sums and products of this body are the wrappers of
   --  Sumcheck_Algebra, the operations the references Acc_Ref and Z_Ref
   --  are written with, so that the proof is a matter of congruence;
   --  they compute the field's operations.
   function "+" (A, B : Element) return Element renames SA."+";
   function "*" (A, B : Element) return Element renames SA."*";

   -------------------------------------------------------------------
   --  One step of the two references of Eval_Quad, whose bodies are
   --  hidden: the value after N terms from the value after N - 1 and
   --  term N. Each lemma unhides the body in its own context only.
   -------------------------------------------------------------------

   procedure Lemma_Acc_Step
     (W : Element_Array; Base : Natural; T : Term_Array; N : Positive;
      G : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => W'First = 0 and then N <= T'Length
               and then Base <= Natural'Last - SA.Max_Wires,
     Post   =>
       (if T (T'First + N - 1).G = G and then T (T'First + N - 1).K /= Zero
        then Same (SA.Acc_Ref (W, Base, T, N, G),
                   SA.Acc_Ref (W, Base, T, N - 1, G)
                   + ((T (T'First + N - 1).K
                       * SA.W_At (W, Base + T (T'First + N - 1).H1))
                      * SA.W_At (W, Base + T (T'First + N - 1).H0)))
        else Same (SA.Acc_Ref (W, Base, T, N, G),
                   SA.Acc_Ref (W, Base, T, N - 1, G)));

   procedure Lemma_Acc_Step
     (W : Element_Array; Base : Natural; T : Term_Array; N : Positive;
      G : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", SA.Acc_Ref);
   begin
      null;
   end Lemma_Acc_Step;

   procedure Lemma_Z_Step
     (W : Element_Array; Base : Natural; T : Term_Array; N : Positive)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => W'First = 0 and then N <= T'Length
               and then Base <= Natural'Last - SA.Max_Wires,
     Post   =>
       SA.Z_Ref (W, Base, T, N)
       = (SA.Z_Ref (W, Base, T, N - 1)
          and then (T (T'First + N - 1).K /= Zero
                    or else SA.W_At (W, Base + T (T'First + N - 1).H1)
                            * SA.W_At (W, Base + T (T'First + N - 1).H0)
                            = Zero));

   procedure Lemma_Z_Step
     (W : Element_Array; Base : Natural; T : Term_Array; N : Positive)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", SA.Z_Ref);
   begin
      null;
   end Lemma_Z_Step;

   --  The two references before any term: Zero and True.
   procedure Lemma_Acc_Zero
     (W : Element_Array; Base : Natural; T : Term_Array; G : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => W'First = 0 and then Base <= Natural'Last - SA.Max_Wires,
     Post   => Same (SA.Acc_Ref (W, Base, T, 0, G), Zero)
               and then SA.Z_Ref (W, Base, T, 0);

   procedure Lemma_Acc_Zero
     (W : Element_Array; Base : Natural; T : Term_Array; G : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", SA.Acc_Ref);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", SA.Z_Ref);
   begin
      null;
   end Lemma_Acc_Zero;

   type Elems_Access is access Element_Array;

   procedure Free_Elems is
     new Ada.Unchecked_Deallocation (Element_Array, Elems_Access);

   -------------------------------------------------------------------
   --  Off of two equal shapes: the equality of Ada, field by field and
   --  layer by layer, carried through the hidden recursion of Off one
   --  step at a time (Lemma_Chal_Off_Eq of Sumcheck_Verifier does the
   --  same for Chal_Off). Seg_Size shows its body and reads the same
   --  count in both shapes.
   -------------------------------------------------------------------

   procedure Lemma_Off_Eq (S1, S2 : Shape; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => S1 = S2 and then J <= S1.Last_Layer + 2,
     Post   => SA.Off (S1, J) = SA.Off (S2, J);

   procedure Lemma_Off_Eq (S1, S2 : Shape; J : Natural) is
   begin
      for K in 0 .. J - 1 loop
         pragma Loop_Invariant (SA.Off (S1, K) = SA.Off (S2, K));
         SA.Lemma_Off_Step (S1, K);
         SA.Lemma_Off_Step (S2, K);
      end loop;
   end Lemma_Off_Eq;

   -------------------------------------------------------------------
   --  Eval_Layer
   -------------------------------------------------------------------

   procedure Eval_Layer
     (P    : Packed_Circuit;
      J    : Natural;
      W    : Element_Array;
      Base : Natural;
      V    : out Element_Array;
      OK   : out Boolean)
   is
      T0    : constant Term_Array := Layer_Of (P, J) with Ghost => Proof_Only;
      E     : constant SA.Circuit := PC.Expand (P) with Ghost => Proof_Only;
      First : constant Positive := P.Layers (J).First;
      Len   : constant Natural := PC.Layer_Len (P, J);
      NW    : constant SA.Wire_Count := P.Layers (J).NW_In;
      C     : PC.Cursor := PC.Start (P, J);
      Tm    : SA.Term;
   begin
      V  := [others => Zero];
      OK := True;
      PC.Lemma_Valid (P);
      pragma Assert (Proof_Only => T0'First = First and then T0'Length = Len);
      --  The terms of the layer name wires in range: the conjunct of
      --  Well_Formed on layer J of the expansion, whose layer table is
      --  the one of P, and whose layer J is T0.
      pragma Assert (Proof_Only => E.Layers (J) = P.Layers (J));
      pragma Assert
        (Proof_Only =>
           SA.Fits (E.Terms (E.Layers (J).First .. E.Layers (J).Last),
                    (if J = 0 then E.Noutput else E.Layers (J - 1).NW_In),
                    E.Layers (J).NW_In));
      pragma Assert
        (Proof_Only => SA.Fits (T0, Out_Count (P, J), NW));
      --  Before the first term: every output Zero, every assertion met.
      for G in V'Range loop
         Lemma_Acc_Zero (W, Base, T0, G);
         pragma Loop_Invariant
           (Proof_Only =>
              (for all G2 in 0 .. G =>
                 Same (V (G2), SA.Acc_Ref (W, Base, T0, 0, G2))));
      end loop;
      Lemma_Acc_Zero (W, Base, T0, 0);
      pragma Assert (Proof_Only => OK = SA.Z_Ref (W, Base, T0, 0));
      PC.Lemma_Walked_Start (P, J);
      for K in 1 .. Len loop
         pragma Loop_Invariant (Proof_Only => PC.Walked (P, J, K - 1, C));
         pragma Loop_Invariant
           (Proof_Only => OK = SA.Z_Ref (W, Base, T0, K - 1));
         pragma Loop_Invariant
           (Proof_Only =>
              (for all G in V'Range =>
                 Same (V (G), SA.Acc_Ref (W, Base, T0, K - 1, G))));
         PC.Lemma_Walked_Step (P, J, K, C);
         Tm := PC.Term_Of (P, C);
         pragma Assert
           (Proof_Only =>
              Tm = T0 (First + K - 1)
              and then Same (Tm.K, T0 (First + K - 1).K));
         pragma Assert
           (Proof_Only =>
              Tm.G < V'Length and then Tm.H0 < NW and then Tm.H1 < NW);
         --  One step of the references, then the two cases of the term,
         --  each a small proof: the reference reads the buffer through
         --  W_At, which is the element here since the index is inside.
         Lemma_Z_Step (W, Base, T0, K);
         pragma Assert
           (Proof_Only =>
              Same (SA.W_At (W, Base + Tm.H1), W (Base + Tm.H1))
              and then Same (SA.W_At (W, Base + Tm.H0), W (Base + Tm.H0)));
         if Tm.K = Zero then
            if W (Base + Tm.H1) * W (Base + Tm.H0) /= Zero then
               OK := False;
            end if;
            pragma Assert (Proof_Only => OK = SA.Z_Ref (W, Base, T0, K));
            for G in V'Range loop
               Lemma_Acc_Step (W, Base, T0, K, G);
               pragma Loop_Invariant
                 (Proof_Only =>
                    (for all G2 in 0 .. G =>
                       Same (V (G2), SA.Acc_Ref (W, Base, T0, K, G2))));
            end loop;
         else
            pragma Assert (Proof_Only => OK = SA.Z_Ref (W, Base, T0, K));
            declare
               V0 : constant Element_Array := V with Ghost => Proof_Only;
            begin
               V (Tm.G) := V (Tm.G)
                 + ((Tm.K * W (Base + Tm.H1)) * W (Base + Tm.H0));
               for G in V'Range loop
                  Lemma_Acc_Step (W, Base, T0, K, G);
                  pragma Loop_Invariant
                    (Proof_Only =>
                       (for all G2 in 0 .. G =>
                          Same (V (G2), SA.Acc_Ref (W, Base, T0, K, G2))));
                  pragma Loop_Invariant
                    (Proof_Only =>
                       (for all G2 in V'Range =>
                          (if G2 /= Tm.G then Same (V (G2), V0 (G2)))));
               end loop;
            end;
         end if;
         C := PC.Step (P, C);
      end loop;
      pragma Assert (Proof_Only => OK = SA.Z_Ref (W, Base, T0, Len));
      pragma Assert
        (Proof_Only =>
           (for all G in V'Range =>
              Same (V (G), SA.Acc_Ref (W, Base, T0, Len, G))));
   end Eval_Layer;

   -------------------------------------------------------------------
   --  Layer J is done: segment J of Wires holds V, the quad sum of
   --  segment J + 1 computed on Before, and Wires agrees with Before
   --  from segment J + 1 on. Then layer J holds in Wires, the layers
   --  above it still hold, and the Z status of every layer from J on is
   --  the same in both buffers. The three lemmas of Sumcheck_Algebra,
   --  ghost at the default level, cannot take the expansion, a value of
   --  level Proof_Only, from executable code: this lemma, at that level,
   --  calls them.
   -------------------------------------------------------------------

   procedure Lemma_Layer_Done
     (C      : SA.Circuit;
      Before : Element_Array;
      Wires  : Element_Array;
      J      : Natural;
      V      : Element_Array)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       Before'First = 0 and then Wires'First = 0
       and then Before'Length = Wires'Length
       and then J <= C.Last_Layer
       and then V'First = 0
       and then V'Length = SA.Seg_Size (SA.Shape_Of (C), J)
       and then SA.Off (SA.Shape_Of (C), J) + SA.Seg_Size (SA.Shape_Of (C), J)
                <= Wires'Length
       and then (for all K in SA.Off (SA.Shape_Of (C), J + 1) .. Wires'Last =>
                   Same (Before (K), Wires (K)))
       and then (for all G in V'Range =>
                   Same (Wires (SA.Off (SA.Shape_Of (C), J) + G), V (G)))
       and then (for all G in V'Range =>
                   Same (V (G),
                         SA.Acc_Ref (Before, SA.Off (SA.Shape_Of (C), J + 1),
                                     SA.Layer_Terms (C, J),
                                     SA.Layer_Terms (C, J)'Length, G)))
       and then (for all J2 in J + 1 .. C.Last_Layer =>
                   SA.Layer_Holds (C, Before, J2)),
     Post   =>
       (for all J2 in J .. C.Last_Layer => SA.Layer_Holds (C, Wires, J2))
       and then (for all J2 in J + 1 .. C.Last_Layer =>
                   SA.Layer_Z (C, Before, J2) = SA.Layer_Z (C, Wires, J2))
       and then SA.Layer_Z (C, Before, J) = SA.Layer_Z (C, Wires, J);

   procedure Lemma_Layer_Done
     (C      : SA.Circuit;
      Before : Element_Array;
      Wires  : Element_Array;
      J      : Natural;
      V      : Element_Array)
   is
   begin
      for J2 in J + 1 .. C.Last_Layer loop
         pragma Loop_Invariant
           (for all J3 in J + 1 .. J2 - 1 =>
              SA.Layer_Holds (C, Wires, J3)
              and then SA.Layer_Z (C, Before, J3) = SA.Layer_Z (C, Wires, J3));
         SA.Lemma_Layer_Frame (C, Before, Wires, J2, J);
      end loop;
      SA.Lemma_From_Frame (C, Before, Wires, J);
      SA.Lemma_Layer_Intro (C, Wires, J, V);
   end Lemma_Layer_Done;

   -------------------------------------------------------------------
   --  Eval_Circuit: the body of Sumcheck_Algebra.Eval_Circuit with
   --  Eval_Layer in place of Eval_Quad on Layer_Terms (C, J). S is the
   --  shape of P, read by the executable statements; SC the shape of
   --  the expansion C, which the references name.
   -------------------------------------------------------------------

   procedure Eval_Circuit
     (P     : Packed_Circuit;
      W     : Element_Array;
      Wires : in out Element_Array;
      OK    : out Boolean)
   is
      C       : constant SA.Circuit := PC.Expand (P) with Ghost => Proof_Only;
      S       : constant Shape := Shape_Of (P);
      In_Base : constant Natural := SA.Off (S, P.Last_Layer + 1);
   begin
      PC.Lemma_Valid (P);
      SA.Lemma_Shape_Of (C);
      pragma Assert (Proof_Only => SA.Shape_Of (C) = S);
      declare
         SC : constant Shape := SA.Shape_Of (C) with Ghost => Proof_Only;
      begin
         --  Segment NL is the input.
         SA.Lemma_Off_Step (S, P.Last_Layer + 1);
         SA.Lemma_Off_Step (S, P.Last_Layer);
         SA.Lemma_Off_Mono (S, P.Last_Layer + 1, P.Last_Layer + 2);
         Lemma_Off_Eq (S, SC, P.Last_Layer + 1);
         for I in 0 .. P.Ninput - 1 loop
            Wires (In_Base + I) := W (I);
            pragma Loop_Invariant
              (for all K in 0 .. I => Same (Wires (In_Base + K), W (K)));
         end loop;

         OK := True;
         for J in reverse 0 .. P.Last_Layer loop
            pragma Loop_Invariant
              (for all I in 0 .. P.Ninput - 1 =>
                 Same (Wires (In_Base + I), W (I)));
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all J2 in J + 1 .. P.Last_Layer =>
                    SA.Layer_Holds (C, Wires, J2)));
            pragma Loop_Invariant
              (Proof_Only =>
                 OK = (for all J2 in J + 1 .. P.Last_Layer =>
                         SA.Layer_Z (C, Wires, J2)));
            SA.Lemma_Off_Step (S, J);
            SA.Lemma_Off_Step (S, J + 1);
            SA.Lemma_Off_Mono (S, J + 2, P.Last_Layer + 2);
            SA.Lemma_Off_Mono (S, J + 1, P.Last_Layer + 1);
            Lemma_Off_Eq (S, SC, J);
            Lemma_Off_Eq (S, SC, J + 1);
            declare
               Size     : constant SA.Wire_Count := SA.Seg_Size (S, J);
               Base_In  : constant Natural := SA.Off (S, J + 1);
               Base_Out : constant Natural := SA.Off (S, J);
               V        : Elems_Access :=
                 new Element_Array'(0 .. Size - 1 => Zero);
               Layer_OK : Boolean;
               Before   : constant Element_Array := Wires
               with Ghost => Proof_Only;
            begin
               Eval_Layer (P, J, Wires, Base_In, V.all, Layer_OK);
               OK := OK and Layer_OK;
               for G in 0 .. Size - 1 loop
                  Wires (Base_Out + G) := V (G);
                  pragma Loop_Invariant
                    (for all K in 0 .. G =>
                       Same (Wires (Base_Out + K), V (K)));
                  pragma Loop_Invariant
                    (Proof_Only =>
                       (for all K in Wires'Range =>
                          (if K < Base_Out or else K > Base_Out + G
                           then Same (Wires (K), Before (K)))));
               end loop;
               --  The offsets and the layer under their two names: the
               --  shape of P and the shape of C, the walk and the slice.
               pragma Assert
                 (Proof_Only =>
                    Base_In = SA.Off (SC, J + 1)
                    and then Base_Out = SA.Off (SC, J)
                    and then Size = SA.Seg_Size (SC, J));
               pragma Assert
                 (Proof_Only =>
                    Layer_Of (P, J) = SA.Layer_Terms (C, J)
                    and then PC.Layer_Len (P, J)
                             = SA.Layer_Terms (C, J)'Length);
               Lemma_Layer_Done (C, Before, Wires, J, V.all);
               Free_Elems (V);
            end;
         end loop;

         pragma Assert
           (Proof_Only =>
              OK = (for all J in 0 .. P.Last_Layer =>
                      SA.Layer_Z (C, Wires, J)));
         --  The outputs are segment 0, inside the buffer.
         SA.Lemma_Off_Step (S, 0);
         SA.Lemma_Off_Mono (S, 1, P.Last_Layer + 2);
         for G in 0 .. P.Noutput - 1 loop
            if Wires (G) /= Zero then
               OK := False;
            end if;
            pragma Loop_Invariant
              (Proof_Only =>
                 OK = ((for all J in 0 .. P.Last_Layer =>
                          SA.Layer_Z (C, Wires, J))
                       and then (for all K in 0 .. G => Wires (K) = Zero)));
         end loop;
         --  The postcondition, conjunct by conjunct, on the expansion.
         pragma Assert
           (Proof_Only =>
              (for all I in 0 .. P.Ninput - 1 =>
                 Same (SA.W_At (Wires, SA.Off (SC, P.Last_Layer + 1) + I),
                       W (I))));
         pragma Assert
           (Proof_Only =>
              (for all J in 0 .. P.Last_Layer =>
                 SA.Layer_Holds (C, Wires, J)));
         pragma Assert
           (Proof_Only =>
              (for all G in 0 .. P.Noutput - 1 =>
                 SA.W_At (Wires, G) = Wires (G)));
         pragma Assert
           (Proof_Only =>
              OK = ((for all J in 0 .. P.Last_Layer =>
                       SA.Layer_Z (C, Wires, J))
                    and then (for all G in 0 .. P.Noutput - 1 =>
                                SA.W_At (Wires, G) = Zero)));
      end;
   end Eval_Circuit;

end Packed_Eval;
