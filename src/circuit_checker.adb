pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;

package body Circuit_Checker is

   use type SA.Layer;
   use type SA.Term;
   use type CC.Layer_Span;

   -------------------------------------------------------------------
   --  The layers as the walk reaches them
   -------------------------------------------------------------------

   function First_Var
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural) return Natural
   is (if J = P.Last_Layer then Integer'Min (P.Ninput, Max_Vars)
       elsif First_Var (P, K, J + 1) <= Max_Vars
       then Integer'Min
              (Max_Vars,
               First_Var (P, K, J + 1)
               + Declared_Before (P, K, J + 1, Reads (P, K, J + 1),
                                  Out_Count (P, J + 1)))
       else Max_Vars);

   function Reads
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural)
      return Shape_Array
   is (if J = P.Last_Layer then Input_Shapes (P)
       elsif First_Var (P, K, J + 1) <= Max_Vars
       then Out_Shapes (P, K, J + 1, Reads (P, K, J + 1),
                        First_Var (P, K, J + 1))
       else Input_Shapes (P));

   function Read_Coefs
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural)
      return Coef_Array
   is (if J = P.Last_Layer
       then [for I in 0 .. P.Ninput - 1 =>
               Coef_List'[1 => SA.One, others => Zero]]
       else Out_Coefs (P, K, J + 1, Reads (P, K, J + 1),
                       Read_Coefs (P, K, J + 1)));

   -------------------------------------------------------------------
   --  One step of each hidden function of the model
   -------------------------------------------------------------------

   procedure Lemma_Hint_Pos_Step
     (P : PC.Packed_Circuit; J : Natural; M : Shape_Array; N : Positive)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms,
        Post => Hint_Pos (P, J, M, N)
                = Hint_Pos (P, J, M, N - 1)
                  + Long_Long_Integer (Pairs (P, J, M, N))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Hint_Pos);
   begin
      null;
   end Lemma_Hint_Pos_Step;

   procedure Lemma_Hint_Pos_Zero
     (P : PC.Packed_Circuit; J : Natural; M : Shape_Array)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer,
        Post => Hint_Pos (P, J, M, 0) = 0
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Hint_Pos);
   begin
      null;
   end Lemma_Hint_Pos_Zero;

   procedure Lemma_Used_Def
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; N : Positive; Q : Natural; G : Natural)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms + 1,
        Post => Used (P, K, J, M, N, Q, G)
                = (if Q = 0 then
                     (if N = 1 then 0
                      else Used (P, K, J, M, N - 1, Pairs (P, J, M, N - 1),
                                 G))
                   else Used (P, K, J, M, N, Q - 1, G)
                        + (if G = TT (P, J, N).G
                              and then H (P, K, J, M, N, Q)
                                       = Used (P, K, J, M, N, Q - 1, G)
                           then 1 else 0))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Used);
   begin
      null;
   end Lemma_Used_Def;

   procedure Lemma_Slot_Mono_Def
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; N : Positive; Q : Natural; G, S : Natural)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms + 1,
        Post => Slot_Mono (P, K, J, M, N, Q, G, S)
                = (if Q = 0 then
                     (if N = 1 then (A => 0, B => 0)
                      else Slot_Mono (P, K, J, M, N - 1,
                                      Pairs (P, J, M, N - 1), G, S))
                   elsif G = TT (P, J, N).G
                     and then H (P, K, J, M, N, Q)
                              = Used (P, K, J, M, N, Q - 1, G)
                     and then S = H (P, K, J, M, N, Q)
                   then Pair_Mono (M, TT (P, J, N), Q)
                   else Slot_Mono (P, K, J, M, N, Q - 1, G, S))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Mono);
   begin
      null;
   end Lemma_Slot_Mono_Def;

   procedure Lemma_Pairs_Ok_Def
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; N : Positive; Q : Natural)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms + 1,
        Post => Pairs_Ok (P, K, J, M, N, Q)
                = (if Q = 0 then
                     (N = 1
                      or else Pairs_Ok (P, K, J, M, N - 1,
                                        Pairs (P, J, M, N - 1)))
                   else Pairs_Ok (P, K, J, M, N, Q - 1)
                        and then Pair_Ok (P, K, J, M, N, Q))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Pairs_Ok);
   begin
      null;
   end Lemma_Pairs_Ok_Def;

   procedure Lemma_Wire_Terms_Def
     (P : PC.Packed_Circuit; J : Natural; N : Natural; G : Natural)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms,
        Post => Wire_Terms (P, J, N, G)
                = (if N = 0 then 0
                   else Wire_Terms (P, J, N - 1, G)
                        + (if TT (P, J, N).G = G
                              and then TT (P, J, N).K /= Zero
                           then 1 else 0))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Wire_Terms);
   begin
      null;
   end Lemma_Wire_Terms_Def;

   procedure Lemma_Slot_Base_Def
     (P : PC.Packed_Circuit; K : CC.Certificate; J, G : Natural)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer and then G <= SA.Max_Wires,
        Post => Slot_Base (P, K, J, G)
                = (if G = 0 then 0
                   else Slot_Base (P, K, J, G - 1)
                        + Long_Long_Integer (Count_Of (P, K, J, G - 1)))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Base);
   begin
      null;
   end Lemma_Slot_Base_Def;

   procedure Lemma_Declared_Def
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; G : Natural)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms,
        Post => Declared_Before (P, K, J, M, G)
                = (if G = 0 then 0
                   else Declared_Before (P, K, J, M, G - 1)
                        + (if Linear (P, K, J, M, G - 1) then 0 else 1))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         Declared_Before);
   begin
      null;
   end Lemma_Declared_Def;

   --  The same steps for every wire (and slot) at once: the walk changes
   --  one wire per pair, and its invariants speak of all of them.
   procedure Lemma_Used_All
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; N : Positive; Q : Natural; NO : Natural)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms + 1,
        Post => (for all G in 0 .. NO - 1 =>
                   Used (P, K, J, M, N, Q, G)
                   = (if Q = 0 then
                        (if N = 1 then 0
                         else Used (P, K, J, M, N - 1,
                                    Pairs (P, J, M, N - 1), G))
                      else Used (P, K, J, M, N, Q - 1, G)
                           + (if G = TT (P, J, N).G
                                 and then H (P, K, J, M, N, Q)
                                          = Used (P, K, J, M, N, Q - 1, G)
                              then 1 else 0)))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Used);
   begin
      null;
   end Lemma_Used_All;

   procedure Lemma_Slot_Mono_All
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; N : Positive; Q : Natural; NO : Natural)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms + 1,
        Post => (for all G in 0 .. NO - 1 =>
                   (for all S in 0 .. CC.Max_Count =>
                      Slot_Mono (P, K, J, M, N, Q, G, S)
                      = (if Q = 0 then
                           (if N = 1 then (A => 0, B => 0)
                            else Slot_Mono (P, K, J, M, N - 1,
                                            Pairs (P, J, M, N - 1), G, S))
                         elsif G = TT (P, J, N).G
                           and then H (P, K, J, M, N, Q)
                                    = Used (P, K, J, M, N, Q - 1, G)
                           and then S = H (P, K, J, M, N, Q)
                         then Pair_Mono (M, TT (P, J, N), Q)
                         else Slot_Mono (P, K, J, M, N, Q - 1, G, S))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Slot_Mono);
   begin
      null;
   end Lemma_Slot_Mono_All;

   procedure Lemma_Wire_Terms_All
     (P : PC.Packed_Circuit; J : Natural; N : Positive; NO : Natural)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms,
        Post => (for all G in 0 .. NO - 1 =>
                   Wire_Terms (P, J, N, G)
                   = Wire_Terms (P, J, N - 1, G)
                     + (if TT (P, J, N).G = G and then TT (P, J, N).K /= Zero
                        then 1 else 0))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Wire_Terms);
   begin
      null;
   end Lemma_Wire_Terms_All;

   procedure Lemma_Count_Of
     (P : PC.Packed_Circuit; K : CC.Certificate; J, G : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Count_Of);
   begin
      null;
   end Lemma_Count_Of;

   procedure Lemma_Hint_At
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      X : Long_Long_Integer)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Hint_At);
   begin
      null;
   end Lemma_Hint_At;

   procedure Lemma_Accepts_Def (P : PC.Packed_Circuit; K : CC.Certificate)
   with Ghost => Proof_Only, Global => null,
        Post => Accepts (P, K)
                = (K.NL = P.Last_Layer + 1
                   and then CC.Spans_Ok (K)
                   and then P.Ninput <= Max_Vars
                   and then (for all J in 0 .. P.Last_Layer =>
                               Layer_Accepted (P, K, J)))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Accepts);
   begin
      null;
   end Lemma_Accepts_Def;

   procedure Lemma_Layer_Ok_Def
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer and then Len (P, J) <= SA.Max_Terms
                and then Out_Count (P, J) <= SA.Max_Wires,
        Post => Layer_Ok (P, K, J, M)
                = (Span (P, K, J).Wires = Out_Count (P, J)
                   and then Hint_Pos (P, J, M, Len (P, J))
                            = Long_Long_Integer (Span (P, K, J).Hints)
                   and then Slot_Base (P, K, J, Out_Count (P, J))
                            <= Long_Long_Integer (Max_Layer_Slots)
                   and then (Len (P, J) = 0
                             or else Pairs_Ok (P, K, J, M, Len (P, J),
                                               Pairs (P, J, M, Len (P, J))))
                   and then (for all G in 0 .. Out_Count (P, J) - 1 =>
                               Count_Of (P, K, J, G) <= Max_Slots
                               and then Wire_Terms (P, J, Len (P, J), G)
                                        <= Max_Terms_Per_Wire
                               and then Used_End (P, K, J, M, G)
                                        = Count_Of (P, K, J, G)))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Layer_Ok);
   begin
      null;
   end Lemma_Layer_Ok_Def;

   procedure Lemma_Layer_Accepted_Def
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer,
        Post => Layer_Accepted (P, K, J)
                = (Layer_Ok (P, K, J, Reads (P, K, J))
                   and then First_Var (P, K, J)
                            + Declared_Before (P, K, J, Reads (P, K, J),
                                               Out_Count (P, J))
                            <= Max_Vars)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         Layer_Accepted);
   begin
      null;
   end Lemma_Layer_Accepted_Def;

   procedure Lemma_Layer_Facts_Def
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      V : SA.Element_Array)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer,
        Post => Layer_Facts (P, K, J, V)
                = (Asserts_Hold (P, K, J, V) and then Declared_Hold (P, K, J, V)
                   and then Outputs_Zero (P, K, J, V))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Layer_Facts);
   begin
      null;
   end Lemma_Layer_Facts_Def;

   --  One step of Reads and First_Var from layer J to layer J - 1.
   procedure Lemma_Reads_Def
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer,
        Post => (if J = P.Last_Layer then
                   Reads (P, K, J) = Input_Shapes (P)
                   and then First_Var (P, K, J)
                            = Integer'Min (P.Ninput, Max_Vars))
                and then
                (if J > 0 then
                   Reads (P, K, J - 1)
                   = Out_Shapes (P, K, J, Reads (P, K, J), First_Var (P, K, J))
                   and then First_Var (P, K, J - 1)
                            = Integer'Min
                                (Max_Vars,
                                 First_Var (P, K, J)
                                 + Declared_Before (P, K, J, Reads (P, K, J),
                                                    Out_Count (P, J))))
   is
   begin
      null;
   end Lemma_Reads_Def;

   -------------------------------------------------------------------
   --  The storage of the walk
   -------------------------------------------------------------------

   type Shape_Access is access Shape_Array;
   type Nat_Array is array (Natural range <>) of Natural;
   type Nat_Access is access Nat_Array;
   --  The slot bases of a layer, bounded by the pool's capacity so that a
   --  base plus a count does not overflow.
   subtype Slot_Pos is Natural range 0 .. CC.Capacity'Last;
   type Base_Array is array (Natural range <>) of Slot_Pos;
   type Base_Access is access Base_Array;
   type Mono_Array is array (Positive range <>) of Monomial;
   type Mono_Access is access Mono_Array;

   procedure Free_Shapes is new Ada.Unchecked_Deallocation
     (Shape_Array, Shape_Access);
   procedure Free_Nats is new Ada.Unchecked_Deallocation
     (Nat_Array, Nat_Access);
   procedure Free_Bases is new Ada.Unchecked_Deallocation
     (Base_Array, Base_Access);
   procedure Free_Monos is new Ada.Unchecked_Deallocation
     (Mono_Array, Mono_Access);

   -------------------------------------------------------------------
   --  One layer
   -------------------------------------------------------------------

   --  The wires of layer J, reading the shapes M, numbered from Vb: St is
   --  Accepted exactly when the layer passes and the variables fit; then
   --  Next holds the shapes of its wires and Vb_Next the next variable.
   procedure Check_Layer
     (P       : PC.Packed_Circuit;
      K       : CC.Certificate;
      J       : Natural;
      M       : Shape_Array;
      Vb      : Natural;
      Pool    : in out Mono_Array;
      Next    : out Shape_Access;
      Vb_Next : out Natural;
      St      : out Status)
   with
     Global => null,
     Pre    =>
       (Runtime    =>
          J <= P.Last_Layer and then M'First = 0
          and then M'Last = P.Layers (J).NW_In - 1
          and then Vb <= Max_Vars
          and then Pool'First = 1 and then Pool'Last = Max_Layer_Slots
          and then CC.Spans_Ok (K) and then K.NL = P.Last_Layer + 1,
        Proof_Only =>
          PC.Valid (P) and then SA.Well_Formed (PC.Expand (P))
          and then Same_Shapes (M, Reads (P, K, J))),
     Post   =>
       (Runtime    =>
          (if St = Accepted then
             Next /= null and then Next'First = 0
             and then Next'Last = Out_Count (P, J) - 1
             and then Vb_Next <= Max_Vars
           else Next = null),
        Proof_Only =>
          (St = Accepted)
          = (Layer_Ok (P, K, J, Reads (P, K, J))
             and then Vb + Declared_Before (P, K, J, Reads (P, K, J),
                                            Out_Count (P, J))
                      <= Max_Vars)
          and then
          (if St = Accepted then
             Same_Shapes (Next.all, Out_Shapes (P, K, J, Reads (P, K, J), Vb))
             and then Vb_Next
                      = Vb + Declared_Before (P, K, J, Reads (P, K, J),
                                              Out_Count (P, J))));

   procedure Check_Layer
     (P       : PC.Packed_Circuit;
      K       : CC.Certificate;
      J       : Natural;
      M       : Shape_Array;
      Vb      : Natural;
      Pool    : in out Mono_Array;
      Next    : out Shape_Access;
      Vb_Next : out Natural;
      St      : out Status)
   is separate;

   -------------------------------------------------------------------
   --  The walk
   -------------------------------------------------------------------

   procedure Walk
     (P  : PC.Packed_Circuit;
      K  : CC.Certificate;
      St : out Status)
   is
      Pool : Mono_Access := null;
      Prev : Shape_Access := null;
      Next : Shape_Access := null;
      Vb   : Natural;
      Vb2  : Natural;
   begin
      if K.NL /= P.Last_Layer + 1 or else not CC.Spans_Ok (K)
        or else P.Ninput > Max_Vars
      then
         Lemma_Accepts_Def (P, K);
         St := (if P.Ninput > Max_Vars then Too_Many_Vars else Cert_Mismatch);
         return;
      end if;
      Pool := new Mono_Array'(1 .. Max_Layer_Slots => (A => 0, B => 0));
      Prev := new Shape_Array'(Input_Shapes (P));
      PC.Lemma_Valid (P);
      --  The last layer reads the inputs (Well_Formed of the expansion,
      --  whose layer table is P's).
      pragma Assert
        (Proof_Only =>
           PC.Expand (P).Layers (P.Last_Layer) = P.Layers (P.Last_Layer));
      pragma Assert (P.Layers (P.Last_Layer).NW_In = P.Ninput);
      Lemma_Accepts_Def (P, K);
      Lemma_Reads_Def (P, K, P.Last_Layer);
      pragma Assert
        (Proof_Only => Same_Shapes (Prev.all, Reads (P, K, P.Last_Layer)));
      Vb := P.Ninput;
      St := Accepted;
      for J in reverse 0 .. P.Last_Layer loop
         pragma Loop_Invariant (Pool /= null and then Prev /= null);
         pragma Loop_Invariant
           (Pool'First = 1 and then Pool'Last = Max_Layer_Slots);
         pragma Loop_Invariant
           (Prev'First = 0 and then Prev'Last = P.Layers (J).NW_In - 1
            and then Vb <= Max_Vars);
         pragma Loop_Invariant (Next = null);
         pragma Loop_Invariant (St = Accepted);
         pragma Loop_Invariant
           (Proof_Only =>
              Same_Shapes (Prev.all, Reads (P, K, J))
              and then Vb = First_Var (P, K, J)
              and then (for all J2 in J + 1 .. P.Last_Layer =>
                          Layer_Accepted (P, K, J2)));
         Check_Layer (P, K, J, Prev.all, Vb, Pool.all, Next, Vb2, St);
         Lemma_Layer_Accepted_Def (P, K, J);
         pragma Assert
           (Proof_Only => (St = Accepted) = Layer_Accepted (P, K, J));
         Free_Shapes (Prev);
         if St /= Accepted then
            Free_Monos (Pool);
            return;
         end if;
         Lemma_Reads_Def (P, K, J);
         Prev := Next;
         Next := null;
         Vb := Vb2;
      end loop;
      Free_Shapes (Prev);
      Free_Monos (Pool);
   end Walk;

   procedure Lemma_Accepts
     (P  : PC.Packed_Circuit;
      K  : CC.Certificate;
      W  : SA.Element_Array;
      Wr : SA.Seg_Array;
      V  : out SA.Element_Array)
   is separate;

end Circuit_Checker;
