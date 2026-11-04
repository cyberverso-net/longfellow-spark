pragma SPARK_Mode (On);


package body Packed_Eval is

   use SA.F;
   use type SA.Term;
   use type SA.Term_Array;
   use type SA.Layer;
   use type SA.Seg_Access;

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
   --  Lemma_Layer_Seg_Intro of Sumcheck_Algebra at level Proof_Only: the
   --  expansion C is a Proof_Only constant, and a lemma at the default
   --  ghost level cannot take it from executable code; this wrapper, at
   --  that level, calls it.
   -------------------------------------------------------------------

   procedure Lemma_Seg_Done
     (C : SA.Circuit; Out_Seg, In_Seg : Element_Array; J : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       Out_Seg'First = 0 and then In_Seg'First = 0
       and then J <= C.Last_Layer
       and then Out_Seg'Length = SA.Seg_Size (SA.Shape_Of (C), J)
       and then (for all G in Out_Seg'Range =>
                   Same (Out_Seg (G),
                         SA.Acc_Ref (In_Seg, 0, SA.Layer_Terms (C, J),
                                     SA.Layer_Terms (C, J)'Length, G))),
     Post   => SA.Layer_Holds_Seg (C, Out_Seg, In_Seg, J);

   procedure Lemma_Seg_Done
     (C : SA.Circuit; Out_Seg, In_Seg : Element_Array; J : Natural)
   is
   begin
      SA.Lemma_Layer_Seg_Intro (C, Out_Seg, In_Seg, J);
   end Lemma_Seg_Done;

   --  Lemma_Layer_Z_Seg_Eq at level Proof_Only, for the same reason.
   procedure Lemma_Z_Seg_Eq
     (C : SA.Circuit; In_Seg : Element_Array; J : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => In_Seg'First = 0 and then J <= C.Last_Layer,
     Post   => SA.Layer_Z_Seg (C, In_Seg, J)
               = SA.Z_Ref (In_Seg, 0, SA.Layer_Terms (C, J),
                           SA.Layer_Terms (C, J)'Length);

   procedure Lemma_Z_Seg_Eq
     (C : SA.Circuit; In_Seg : Element_Array; J : Natural)
   is
   begin
      SA.Lemma_Layer_Z_Seg_Eq (C, In_Seg, J);
   end Lemma_Z_Seg_Eq;

   --  One step of the Z status over the layers: the status of the
   --  layers above J and the status of J give the status from J on.
   --  Stated on the array of segments as it is before segment J is
   --  filled (the segments above J only are read).
   procedure Lemma_Z_Step
     (C : SA.Circuit; Wr : SA.Seg_Array; J : Natural;
      Above, At_J : Boolean)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       Wr'First = 0 and then J <= C.Last_Layer
       and then Wr'Last = C.Last_Layer + 1
       and then (for all K in J + 1 .. Wr'Last =>
                   Wr (K) /= null and then Wr (K)'First = 0)
       and then Above = (for all J2 in J + 1 .. C.Last_Layer =>
                           SA.Layer_Z_Seg (C, Wr (J2 + 1).all, J2))
       and then At_J = SA.Layer_Z_Seg (C, Wr (J + 1).all, J),
     Post   =>
       (Above and At_J)
       = (for all J2 in J .. C.Last_Layer =>
            SA.Layer_Z_Seg (C, Wr (J2 + 1).all, J2));

   procedure Lemma_Z_Step
     (C : SA.Circuit; Wr : SA.Seg_Array; J : Natural;
      Above, At_J : Boolean)
   is
   begin
      null;
   end Lemma_Z_Step;

   -------------------------------------------------------------------
   --  Eval_Circuit: the body of Sumcheck_Algebra.Eval_Circuit with
   --  Eval_Layer in place of Eval_Quad on Layer_Terms (C, J), and a heap
   --  segment per layer in place of the single buffer (block 4). S is
   --  the shape of P, read by the executable statements; the references
   --  name the shape of the expansion C, equal to it field by field.
   -------------------------------------------------------------------

   procedure Eval_Circuit
     (P  : Packed_Circuit;
      W  : Element_Array;
      Wr : in out SA.Seg_Array;
      OK : out Boolean)
   is
      C  : constant SA.Circuit := PC.Expand (P) with Ghost => Proof_Only;
      S  : constant Shape := Shape_Of (P);
      NL : constant Natural := P.Last_Layer + 1;
   begin
      PC.Lemma_Valid (P);
      SA.Lemma_Shape_Of (C);
      pragma Assert (Proof_Only => SA.Shape_Of (C) = S);
      --  Segment NL is the input: Shape_Ok makes the last layer read
      --  Ninput wires, so the segment has the size of W.
      Wr (NL) := new Element_Array'(W);
      pragma Assert (Wr (NL)'Length = SA.Seg_Size (S, NL));

      OK := True;
      for J in reverse 0 .. P.Last_Layer loop
         pragma Loop_Invariant (for all K in 0 .. J => Wr (K) = null);
         pragma Loop_Invariant
           (for all K in J + 1 .. NL =>
              Wr (K) /= null and then Wr (K)'First = 0
              and then Wr (K)'Length = SA.Seg_Size (S, K));
         pragma Loop_Invariant
           (for all I in 0 .. P.Ninput - 1 => Same (Wr (NL) (I), W (I)));
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J2 in J + 1 .. P.Last_Layer =>
                 SA.Layer_Holds_Seg (C, Wr (J2).all, Wr (J2 + 1).all, J2)));
         pragma Loop_Invariant
           (Proof_Only =>
              OK = (for all J2 in J + 1 .. P.Last_Layer =>
                      SA.Layer_Z_Seg (C, Wr (J2 + 1).all, J2)));
         declare
            Size     : constant SA.Wire_Count := SA.Seg_Size (S, J);
            V        : SA.Seg_Access :=
              new Element_Array'(0 .. Size - 1 => Zero);
            Layer_OK : Boolean;
         begin
            Eval_Layer (P, J, Wr (J + 1).all, 0, V.all, Layer_OK);
            --  The layer under its two names: the walk and the slice of
            --  the expansion; the segment's size in the two shapes; the
            --  Z status of the layer in the reference's terms.
            pragma Assert
              (Proof_Only =>
                 Layer_Of (P, J) = SA.Layer_Terms (C, J)
                 and then PC.Layer_Len (P, J)
                          = SA.Layer_Terms (C, J)'Length);
            pragma Assert
              (Proof_Only => Size = SA.Seg_Size (SA.Shape_Of (C), J));
            Lemma_Z_Seg_Eq (C, Wr (J + 1).all, J);
            pragma Assert
              (Proof_Only =>
                 Layer_OK = SA.Layer_Z_Seg (C, Wr (J + 1).all, J));
            Lemma_Z_Step (C, Wr, J, OK, Layer_OK);
            OK := OK and Layer_OK;
            pragma Assert
              (Proof_Only =>
                 OK = (for all J2 in J .. P.Last_Layer =>
                         SA.Layer_Z_Seg (C, Wr (J2 + 1).all, J2)));
            Lemma_Seg_Done (C, V.all, Wr (J + 1).all, J);
            --  The segment moves into the array; V is not read after.
            Wr (J) := V;
         end;
      end loop;

      pragma Assert
        (Proof_Only =>
           OK = (for all J in 0 .. P.Last_Layer =>
                   SA.Layer_Z_Seg (C, Wr (J + 1).all, J)));
      --  The outputs are segment 0.
      for G in 0 .. P.Noutput - 1 loop
         if Wr (0) (G) /= Zero then
            OK := False;
         end if;
         pragma Loop_Invariant
           (Proof_Only =>
              OK = ((for all J in 0 .. P.Last_Layer =>
                       SA.Layer_Z_Seg (C, Wr (J + 1).all, J))
                    and then (for all K in 0 .. G => Wr (0) (K) = Zero)));
      end loop;
   end Eval_Circuit;

end Packed_Eval;
