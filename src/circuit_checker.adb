pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;

package body Circuit_Checker is

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
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms,
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
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms,
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
        Pre  => J <= P.Last_Layer and then N <= SA.Max_Terms,
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

   procedure Lemma_Walk_From_Def
     (P : PC.Packed_Circuit; K : CC.Certificate; J : Natural;
      M : Shape_Array; Vb : Natural)
   with Ghost => Proof_Only, Global => null,
        Pre  => J <= P.Last_Layer and then Vb <= Max_Vars,
        Post => Walk_From (P, K, J, M, Vb)
                = (Layer_Ok (P, K, J, M)
                   and then Vb + Declared_Before (P, K, J, M, Out_Count (P, J))
                            <= Max_Vars
                   and then
                   (J = 0
                    or else Walk_From
                              (P, K, J - 1, Out_Shapes (P, K, J, M, Vb),
                               Vb + Declared_Before (P, K, J, M,
                                                     Out_Count (P, J)))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Walk_From);
   begin
      null;
   end Lemma_Walk_From_Def;

   -------------------------------------------------------------------
   --  The storage of the walk
   -------------------------------------------------------------------

   type Shape_Access is access Shape_Array;
   type Nat_Array is array (Natural range <>) of Natural;
   type Nat_Access is access Nat_Array;
   type Mono_Array is array (Positive range <>) of Monomial;
   type Mono_Access is access Mono_Array;

   procedure Free_Shapes is new Ada.Unchecked_Deallocation
     (Shape_Array, Shape_Access);
   procedure Free_Nats is new Ada.Unchecked_Deallocation
     (Nat_Array, Nat_Access);
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
          and then M'Length = P.Layers (J).NW_In
          and then Vb <= Max_Vars
          and then Pool'First = 1 and then Pool'Last = Max_Layer_Slots
          and then CC.Spans_Ok (K) and then K.NL = P.Last_Layer + 1,
        Proof_Only =>
          PC.Valid (P) and then SA.Well_Formed (PC.Expand (P))),
     Post   =>
       (Runtime    =>
          (if St = Accepted then
             Next /= null and then Next'First = 0
             and then Next'Length = Out_Count (P, J)
             and then Vb_Next <= Max_Vars
           else Next = null),
        Proof_Only =>
          (St = Accepted)
          = (Layer_Ok (P, K, J, M)
             and then Vb + Declared_Before (P, K, J, M, Out_Count (P, J))
                      <= Max_Vars)
          and then
          (if St = Accepted then
             Next.all = Out_Shapes (P, K, J, M, Vb)
             and then Vb_Next
                      = Vb + Declared_Before (P, K, J, M, Out_Count (P, J))));

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
      Pool : Mono_Access;
      Prev : Shape_Access;
      Next : Shape_Access;
      Vb   : Natural;
      Vb2  : Natural;
   begin
      if K.NL /= P.Last_Layer + 1 or else not CC.Spans_Ok (K)
        or else P.Ninput > Max_Vars
      then
         St := Cert_Mismatch;
         return;
      end if;
      Pool := new Mono_Array'(1 .. Max_Layer_Slots => (A => 0, B => 0));
      Prev := new Shape_Array'
        ([for I in 0 .. P.Ninput - 1 => (N => 1, V => [1 => I, others => 0])]);
      pragma Assert (Proof_Only => Prev.all = Input_Shapes (P));
      Vb := P.Ninput;
      St := Accepted;
      for J in reverse 0 .. P.Last_Layer loop
         pragma Loop_Invariant (Pool /= null and then Prev /= null);
         pragma Loop_Invariant
           (Pool'First = 1 and then Pool'Last = Max_Layer_Slots);
         pragma Loop_Invariant
           (Prev'First = 0 and then Prev'Length = P.Layers (J).NW_In
            and then Vb <= Max_Vars);
         pragma Loop_Invariant
           (Proof_Only =>
              Accepts (P, K) = Walk_From (P, K, J, Prev.all, Vb));
         Check_Layer (P, K, J, Prev.all, Vb, Pool.all, Next, Vb2, St);
         Lemma_Walk_From_Def (P, K, J, Prev.all, Vb);
         Free_Shapes (Prev);
         if St /= Accepted then
            Free_Monos (Pool);
            return;
         end if;
         Prev := Next;
         Next := null;
         Vb := Vb2;
      end loop;
      Free_Shapes (Prev);
      Free_Monos (Pool);
   end Walk;

end Circuit_Checker;
