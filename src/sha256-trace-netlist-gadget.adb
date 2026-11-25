pragma SPARK_Mode (On);

package body Sha256.Trace.Netlist.Gadget is

   ----------------------------------------------------------------------
   --  Bits as field elements
   ----------------------------------------------------------------------

   function Bit_E (B : Boolean) return Element is
     (if B then One else Zero)
   with Ghost => Proof_Only;

   function Bit (V : Unsigned_32; J : Bit_Index) return Boolean is
     ((Shift_Right (V, J) and 1) = 1)
   with Ghost => Proof_Only;

   procedure Lemma_Bits_Of (V : Unsigned_32; J : Bit_Index) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Bits_Of (V) (J) = Bit_E (Bit (V, J));

   procedure Lemma_Bits_Of (V : Unsigned_32; J : Bit_Index) is
   begin
      null;
   end Lemma_Bits_Of;

   --  The sum of two bits is their xor.
   procedure Lemma_Add (P, Q : Boolean) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Add (Bit_E (P), Bit_E (Q)) = Bit_E (P /= Q);

   procedure Lemma_Add (P, Q : Boolean) is
   begin
      null;
   end Lemma_Add;

   --  The product of two bits is their and.
   procedure Lemma_Mul (P, Q : Boolean) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul (Bit_E (P), Bit_E (Q)) = Bit_E (P and then Q);

   procedure Lemma_Mul (P, Q : Boolean) is
      A : constant Element := Bit_E (P);
   begin
      GF2_128.Lemma_Mul_One (A);
      Lemma_Mul_Zero (A);
      if Q then
         pragma Assert (Mul (A, Bit_E (Q)) = A);
      else
         pragma Assert (Mul (A, Bit_E (Q)) = Zero);
      end if;
   end Lemma_Mul;

   procedure Lemma_Xor3 (P, Q, R : Boolean) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Xor3 (Bit_E (P), Bit_E (Q), Bit_E (R)) = Bit_E (P xor Q xor R)
   is
   begin
      Lemma_Add (P, Q);
      Lemma_Add (P /= Q, R);
   end Lemma_Xor3;

   procedure Lemma_Ch (P, Q, R : Boolean) with
     Ghost  => Proof_Only,
     Global => null,
     Post   =>
       Ch_Bit (Bit_E (P), Bit_E (Q), Bit_E (R))
       = Bit_E ((P and then Q) /= ((not P) and then R))
   is
      NP : constant Element := Not_Bit (Bit_E (P));
   begin
      Lemma_Add (True, P);
      pragma Assert (Bit_E (True) = One);
      pragma Assert (NP = Bit_E (not P));
      Lemma_Mul (P, Q);
      Lemma_Mul (not P, R);
      Lemma_Mul_Cong (NP, Bit_E (not P), Bit_E (R), Bit_E (R));
      pragma Assert (Mul (NP, Bit_E (R)) = Bit_E ((not P) and then R));
      Lemma_Add (P and then Q, (not P) and then R);
      pragma Assert
        (Ch_Bit (Bit_E (P), Bit_E (Q), Bit_E (R))
         = Add (Mul (Bit_E (P), Bit_E (Q)), Mul (NP, Bit_E (R))));
   end Lemma_Ch;

   procedure Lemma_Maj (P, Q, R : Boolean) with
     Ghost  => Proof_Only,
     Global => null,
     Post   =>
       Maj_Bit (Bit_E (P), Bit_E (Q), Bit_E (R))
       = Bit_E ((P and then Q) /= ((P /= Q) and then R))
   is
      PQ : constant Element := Add (Bit_E (P), Bit_E (Q));
   begin
      Lemma_Add (P, Q);
      pragma Assert (PQ = Bit_E (P /= Q));
      Lemma_Mul (P, Q);
      Lemma_Mul (P /= Q, R);
      Lemma_Mul_Cong (PQ, Bit_E (P /= Q), Bit_E (R), Bit_E (R));
      pragma Assert (Mul (PQ, Bit_E (R)) = Bit_E ((P /= Q) and then R));
      Lemma_Add (P and then Q, (P /= Q) and then R);
      pragma Assert
        (Maj_Bit (Bit_E (P), Bit_E (Q), Bit_E (R))
         = Add (Mul (Bit_E (P), Bit_E (Q)), Mul (PQ, Bit_E (R))));
   end Lemma_Maj;

   ----------------------------------------------------------------------
   --  The bit forms of the round functions
   ----------------------------------------------------------------------

   procedure Lemma_Sigma_0_Bits (V : Unsigned_32) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Sigma_0_Form (Bits_Of (V)) = Bits_Of (Sigma_0 (V))
   is
   begin
      for I in Bit_Index loop
         Lemma_Bits_Of (V, (I + 2) mod 32);
         Lemma_Bits_Of (V, (I + 13) mod 32);
         Lemma_Bits_Of (V, (I + 22) mod 32);
         Lemma_Bits_Of (Sigma_0 (V), I);
         Lemma_Xor3 (Bit (V, (I + 2) mod 32), Bit (V, (I + 13) mod 32),
                     Bit (V, (I + 22) mod 32));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              Sigma_0_Form (Bits_Of (V)) (J) = Bits_Of (Sigma_0 (V)) (J));
      end loop;
   end Lemma_Sigma_0_Bits;

   procedure Lemma_Sigma_1_Bits (V : Unsigned_32) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Sigma_1_Form (Bits_Of (V)) = Bits_Of (Sigma_1 (V))
   is
   begin
      for I in Bit_Index loop
         Lemma_Bits_Of (V, (I + 6) mod 32);
         Lemma_Bits_Of (V, (I + 11) mod 32);
         Lemma_Bits_Of (V, (I + 25) mod 32);
         Lemma_Bits_Of (Sigma_1 (V), I);
         Lemma_Xor3 (Bit (V, (I + 6) mod 32), Bit (V, (I + 11) mod 32),
                     Bit (V, (I + 25) mod 32));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              Sigma_1_Form (Bits_Of (V)) (J) = Bits_Of (Sigma_1 (V)) (J));
      end loop;
   end Lemma_Sigma_1_Bits;

   procedure Lemma_Small_0_Bits (V : Unsigned_32) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Small_0_Form (Bits_Of (V)) = Bits_Of (Small_0 (V))
   is
   begin
      for I in Bit_Index loop
         Lemma_Bits_Of (V, (I + 7) mod 32);
         Lemma_Bits_Of (V, (I + 18) mod 32);
         if I + 3 < 32 then
            Lemma_Bits_Of (V, I + 3);
         end if;
         Lemma_Bits_Of (Small_0 (V), I);
         Lemma_Xor3 (Bit (V, (I + 7) mod 32), Bit (V, (I + 18) mod 32),
                     I + 3 < 32 and then Bit (V, I + 3));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              Small_0_Form (Bits_Of (V)) (J) = Bits_Of (Small_0 (V)) (J));
      end loop;
   end Lemma_Small_0_Bits;

   procedure Lemma_Small_1_Bits (V : Unsigned_32) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Small_1_Form (Bits_Of (V)) = Bits_Of (Small_1 (V))
   is
   begin
      for I in Bit_Index loop
         Lemma_Bits_Of (V, (I + 17) mod 32);
         Lemma_Bits_Of (V, (I + 19) mod 32);
         if I + 10 < 32 then
            Lemma_Bits_Of (V, I + 10);
         end if;
         Lemma_Bits_Of (Small_1 (V), I);
         Lemma_Xor3 (Bit (V, (I + 17) mod 32), Bit (V, (I + 19) mod 32),
                     I + 10 < 32 and then Bit (V, I + 10));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              Small_1_Form (Bits_Of (V)) (J) = Bits_Of (Small_1 (V)) (J));
      end loop;
   end Lemma_Small_1_Bits;

   procedure Lemma_Ch_Bits (A, B, C : Unsigned_32) with
     Ghost  => Proof_Only,
     Global => null,
     Post   =>
       Ch_Form (Bits_Of (A), Bits_Of (B), Bits_Of (C))
       = Bits_Of (Ch (A, B, C))
   is
   begin
      for I in Bit_Index loop
         Lemma_Bits_Of (A, I);
         Lemma_Bits_Of (B, I);
         Lemma_Bits_Of (C, I);
         Lemma_Bits_Of (Ch (A, B, C), I);
         Lemma_Ch (Bit (A, I), Bit (B, I), Bit (C, I));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              Ch_Form (Bits_Of (A), Bits_Of (B), Bits_Of (C)) (J)
              = Bits_Of (Ch (A, B, C)) (J));
      end loop;
   end Lemma_Ch_Bits;

   procedure Lemma_Maj_Bits (A, B, C : Unsigned_32) with
     Ghost  => Proof_Only,
     Global => null,
     Post   =>
       Maj_Form (Bits_Of (A), Bits_Of (B), Bits_Of (C))
       = Bits_Of (Maj (A, B, C))
   is
   begin
      for I in Bit_Index loop
         Lemma_Bits_Of (A, I);
         Lemma_Bits_Of (B, I);
         Lemma_Bits_Of (C, I);
         Lemma_Bits_Of (Maj (A, B, C), I);
         Lemma_Maj (Bit (A, I), Bit (B, I), Bit (C, I));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              Maj_Form (Bits_Of (A), Bits_Of (B), Bits_Of (C)) (J)
              = Bits_Of (Maj (A, B, C)) (J));
      end loop;
   end Lemma_Maj_Bits;

   --  A form over words of bits is the word of the round function: its
   --  bits, and its value.
   procedure Lemma_Forms (A, B, C : Word_Bits) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => All_Bits (A) and then All_Bits (B) and then All_Bits (C),
     Post   =>
       All_Bits (Sigma_0_Form (A)) and then All_Bits (Sigma_1_Form (A))
       and then All_Bits (Small_0_Form (A))
       and then All_Bits (Small_1_Form (A))
       and then All_Bits (Ch_Form (A, B, C))
       and then All_Bits (Maj_Form (A, B, C))
       and then Word_Value (Sigma_0_Form (A)) = Sigma_0 (Word_Value (A))
       and then Word_Value (Sigma_1_Form (A)) = Sigma_1 (Word_Value (A))
       and then Word_Value (Small_0_Form (A)) = Small_0 (Word_Value (A))
       and then Word_Value (Small_1_Form (A)) = Small_1 (Word_Value (A))
       and then Word_Value (Ch_Form (A, B, C))
                = Ch (Word_Value (A), Word_Value (B), Word_Value (C))
       and then Word_Value (Maj_Form (A, B, C))
                = Maj (Word_Value (A), Word_Value (B), Word_Value (C))
   is
      VA : constant Unsigned_32 := Word_Value (A);
      VB : constant Unsigned_32 := Word_Value (B);
      VC : constant Unsigned_32 := Word_Value (C);
   begin
      Lemma_Bits_Of_Value (A);
      Lemma_Bits_Of_Value (B);
      Lemma_Bits_Of_Value (C);
      pragma Assert (A = Bits_Of (VA));
      pragma Assert (B = Bits_Of (VB));
      pragma Assert (C = Bits_Of (VC));
      Lemma_Sigma_0_Bits (VA);
      Lemma_Sigma_1_Bits (VA);
      Lemma_Small_0_Bits (VA);
      Lemma_Small_1_Bits (VA);
      Lemma_Ch_Bits (VA, VB, VC);
      Lemma_Maj_Bits (VA, VB, VC);
      pragma Assert (Sigma_0_Form (A) = Bits_Of (Sigma_0 (VA)));
      pragma Assert (Sigma_1_Form (A) = Bits_Of (Sigma_1 (VA)));
      pragma Assert (Small_0_Form (A) = Bits_Of (Small_0 (VA)));
      pragma Assert (Small_1_Form (A) = Bits_Of (Small_1 (VA)));
      for I in Bit_Index loop
         Lemma_Mul_Cong (A (I), Bits_Of (VA) (I), B (I), Bits_Of (VB) (I));
         Lemma_Mul_Cong (Not_Bit (A (I)), Not_Bit (Bits_Of (VA) (I)),
                         C (I), Bits_Of (VC) (I));
         Lemma_Mul_Cong (Add (A (I), B (I)),
                         Add (Bits_Of (VA) (I), Bits_Of (VB) (I)),
                         C (I), Bits_Of (VC) (I));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              Ch_Form (A, B, C) (J) = Bits_Of (Ch (VA, VB, VC)) (J)
              and then Maj_Form (A, B, C) (J) = Bits_Of (Maj (VA, VB, VC)) (J));
      end loop;
      Lemma_Value_Ext (Sigma_0_Form (A), Bits_Of (Sigma_0 (VA)));
      Lemma_Value_Ext (Sigma_1_Form (A), Bits_Of (Sigma_1 (VA)));
      Lemma_Value_Ext (Small_0_Form (A), Bits_Of (Small_0 (VA)));
      Lemma_Value_Ext (Small_1_Form (A), Bits_Of (Small_1 (VA)));
      Lemma_Value_Ext (Ch_Form (A, B, C), Bits_Of (Ch (VA, VB, VC)));
      Lemma_Value_Ext (Maj_Form (A, B, C), Bits_Of (Maj (VA, VB, VC)));
      Lemma_Value_Ext (A, Bits_Of (VA));
      Lemma_Value_Ext (B, Bits_Of (VB));
      Lemma_Value_Ext (C, Bits_Of (VC));
      Lemma_Value_Bits_Of (Sigma_0 (VA));
      Lemma_Value_Bits_Of (Sigma_1 (VA));
      Lemma_Value_Bits_Of (Small_0 (VA));
      Lemma_Value_Bits_Of (Small_1 (VA));
      Lemma_Value_Bits_Of (Ch (VA, VB, VC));
      Lemma_Value_Bits_Of (Maj (VA, VB, VC));
   end Lemma_Forms;

   ----------------------------------------------------------------------
   --  The words of the netlist's values
   ----------------------------------------------------------------------

   function Inputs_Hold
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64) return Boolean
   is
     ((for all J in Sha256.Word_Index => H0 (J) = Bits_Of (S (J)))
      and then (for all I in 0 .. 15 =>
                  M (I) = Bits_Of (Message_Word (Block, I)))
      and then Witness_Bits (X))
   with Ghost => Proof_Only;

   procedure Lemma_Input_Bits
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Inputs_Hold (M, H0, X, S, Block),
     Post   =>
       (for all J in Sha256.Word_Index => All_Bits (H0 (J)))
       and then (for all I in Round => All_Bits (W_Bits (M, X, I)))
       and then (for all T in Round_Or_End =>
                   (for all P in Sha256.Word_Index =>
                      All_Bits (Var_Bits (H0, X, T, P))))
   is
   begin
      for J in Sha256.Word_Index loop
         Lemma_Value_Bits_Of (S (J));
         pragma Loop_Invariant
           (for all P in Sha256.Word_Index range 0 .. J => All_Bits (H0 (P)));
      end loop;
      for I in 0 .. 15 loop
         Lemma_Value_Bits_Of (Message_Word (Block, I));
         pragma Loop_Invariant
           (for all P in 0 .. I => All_Bits (M (P)));
      end loop;
   end Lemma_Input_Bits;

   --  Value I of the netlist and its bits.
   procedure Lemma_Bits_At_Var
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      T : Round_Or_End; P : Sha256.Word_Index)
   with
     Ghost  => Proof_Only,
     Global => null,
     Post   =>
       Bits_At (M, H0, X, Var (T, P)) = Var_Bits (H0, X, T, P)
       and then Word_Value (Bits_At (M, H0, X, Var (T, P)))
                = Word_Value (Var_Bits (H0, X, T, P))
   is
   begin
      if P <= 3 and then T > Natural (P) then
         pragma Assert
           ((A_Ix (T - 1 - Natural (P)) - First_Round) / 6
            = T - 1 - Natural (P));
         pragma Assert
           ((A_Ix (T - 1 - Natural (P)) - First_Round) mod 6 = 5);
      elsif P >= 4 and then T > Natural (P) - 4 then
         pragma Assert
           ((E_Ix (T - 1 - (Natural (P) - 4)) - First_Round) / 6
            = T - 1 - (Natural (P) - 4));
         pragma Assert
           ((E_Ix (T - 1 - (Natural (P) - 4)) - First_Round) mod 6 = 4);
      end if;
   end Lemma_Bits_At_Var;

   procedure Lemma_Bits_At_W
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness; I : Round)
   with
     Ghost  => Proof_Only,
     Global => null,
     Post   =>
       Bits_At (M, H0, X, W_Ix (I)) = W_Bits (M, X, I)
       and then Word_Value (Bits_At (M, H0, X, W_Ix (I)))
                = Word_Value (W_Bits (M, X, I))
   is
   begin
      if I >= 16 then
         pragma Assert ((W_Ix (I) - First_Schedule) / 3 = I - 16);
         pragma Assert ((W_Ix (I) - First_Schedule) mod 3 = 2);
      end if;
   end Lemma_Bits_At_W;

   --  The bridge of G3 on one assertion, with the bits it needs.
   procedure Lemma_Sum
     (L : Gadgets.Words.Word_List; K : Gadgets.Words.Term_Count;
      A : Word_Bits)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       Gadgets.Words.All_Bits (L, K) and then All_Bits (A)
       and then Gadgets.Words.Assertion (L, K, A) = Zero,
     Post   =>
       Word_Value (A) = Unsigned_32 (Gadgets.Words.Sum_Upto (L, K) mod 2 ** 32)
   is
   begin
      Gadgets.Words.Lemma_Assert_Eqmod (L, K, A);
   end Lemma_Sum;

   ----------------------------------------------------------------------
   --  One value
   ----------------------------------------------------------------------

   --  Value I satisfies its definition over the decoded values.
   function Value_Holds
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64; I : Value_Index) return Boolean
   is
     (Decoded (M, H0, X) (I)
      = Eval (Def (I), Decoded (M, H0, X), S, Block, I))
   with Ghost => Proof_Only;

   --  The bits at the values a round reads.
   procedure Lemma_Bits_At_Round
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness; T : Round)
   with
     Ghost  => Proof_Only,
     Global => null,
     Post   =>
       (for all P in Sha256.Word_Index =>
          Word_Value (Bits_At (M, H0, X, Var (T, P)))
          = Word_Value (Var_Bits (H0, X, T, P)))
       and then Word_Value (Bits_At (M, H0, X, W_Ix (T)))
                = Word_Value (W_Bits (M, X, T))
       and then Word_Value (Bits_At (M, H0, X, Sg1_Ix (T)))
                = Word_Value (Sigma_1_Form (Var_Bits (H0, X, T, 4)))
       and then Word_Value (Bits_At (M, H0, X, Ch_Ix (T)))
                = Word_Value (Ch_Form (Var_Bits (H0, X, T, 4),
                                       Var_Bits (H0, X, T, 5),
                                       Var_Bits (H0, X, T, 6)))
       and then Word_Value (Bits_At (M, H0, X, Sg0_Ix (T)))
                = Word_Value (Sigma_0_Form (Var_Bits (H0, X, T, 0)))
       and then Word_Value (Bits_At (M, H0, X, Mj_Ix (T)))
                = Word_Value (Maj_Form (Var_Bits (H0, X, T, 0),
                                        Var_Bits (H0, X, T, 1),
                                        Var_Bits (H0, X, T, 2)))
       and then Word_Value (Bits_At (M, H0, X, E_Ix (T)))
                = Word_Value (X.E (T))
       and then Word_Value (Bits_At (M, H0, X, A_Ix (T)))
                = Word_Value (X.A (T))
   is
   begin
      for P in Sha256.Word_Index loop
         Lemma_Bits_At_Var (M, H0, X, T, P);
         pragma Loop_Invariant
           (for all Q in Sha256.Word_Index range 0 .. P =>
              Word_Value (Bits_At (M, H0, X, Var (T, Q)))
              = Word_Value (Var_Bits (H0, X, T, Q)));
      end loop;
      Lemma_Bits_At_W (M, H0, X, T);
      for O in 0 .. 5 loop
         pragma Assert ((First_Round + 6 * T + O - First_Round) / 6 = T);
         pragma Assert ((First_Round + 6 * T + O - First_Round) mod 6 = O);
      end loop;
   end Lemma_Bits_At_Round;

   procedure Lemma_Value_Input
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64; I : Value_Index)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       I < First_Schedule
       and then Inputs_Hold (M, H0, X, S, Block) and then Assertions_Hold (M, H0, X),
     Post   => Value_Holds (M, H0, X, S, Block, I)
   is
      V : constant Values := Decoded (M, H0, X);
   begin
      Lemma_Input_Bits (M, H0, X, S, Block);
      if I < First_Message then
         Lemma_Value_Bits_Of (S (Sha256.Word_Index (I)));
         Lemma_Value_Ext
           (H0 (Sha256.Word_Index (I)), Bits_Of (S (Sha256.Word_Index (I))));
         pragma Assert (Def (I).Op = Op_State);
         pragma Assert (V (I) = Word_Value (H0 (Sha256.Word_Index (I))));
      else
         Lemma_Value_Bits_Of (Message_Word (Block, I - First_Message));
         Lemma_Value_Ext
           (M (I - First_Message),
            Bits_Of (Message_Word (Block, I - First_Message)));
         pragma Assert (Def (I).Op = Op_Message);
         pragma Assert (V (I) = Word_Value (M (I - First_Message)));
      end if;
   end Lemma_Value_Input;

   procedure Lemma_Value_Small
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64; St : Schedule_Step; Zero_One : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       Zero_One <= 1
       and then Inputs_Hold (M, H0, X, S, Block) and then Assertions_Hold (M, H0, X),
     Post   => Value_Holds (M, H0, X, S, Block, First_Schedule + 3 * (St - 16) + Zero_One)
   is
      V : constant Values := Decoded (M, H0, X);
   begin
      Lemma_Input_Bits (M, H0, X, S, Block);
      pragma Assert ((3 * (St - 16) + Zero_One) / 3 = St - 16);
      pragma Assert ((3 * (St - 16) + Zero_One) mod 3 = Zero_One);
      if Zero_One = 0 then
         Lemma_Bits_At_W (M, H0, X, St - 15);
         Lemma_Forms (W_Bits (M, X, St - 15), H0 (0), H0 (0));
         pragma Assert
           (Def (S0_Ix (St)) = (Op_Small_0, 1, [W_Ix (St - 15), others => 0], 0));
         pragma Assert
           (V (S0_Ix (St)) = Small_0 (Word_Value (W_Bits (M, X, St - 15))));
         pragma Assert (V (W_Ix (St - 15)) = Word_Value (W_Bits (M, X, St - 15)));
      else
         Lemma_Bits_At_W (M, H0, X, St - 2);
         Lemma_Forms (W_Bits (M, X, St - 2), H0 (0), H0 (0));
         pragma Assert
           (Def (S1_Ix (St)) = (Op_Small_1, 1, [W_Ix (St - 2), others => 0], 0));
         pragma Assert
           (V (S1_Ix (St)) = Small_1 (Word_Value (W_Bits (M, X, St - 2))));
         pragma Assert (V (W_Ix (St - 2)) = Word_Value (W_Bits (M, X, St - 2)));
      end if;
   end Lemma_Value_Small;

   procedure Lemma_Value_Schedule
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64; St : Schedule_Step)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       Inputs_Hold (M, H0, X, S, Block) and then Assertions_Hold (M, H0, X),
     Post   => Value_Holds (M, H0, X, S, Block, W_Ix (St))
   is
      V : constant Values := Decoded (M, H0, X);
      L : constant Gadgets.Words.Word_List := Schedule_Words (M, X, St);
   begin
      Lemma_Input_Bits (M, H0, X, S, Block);
      Lemma_Bits_At_W (M, H0, X, St);
      Lemma_Bits_At_W (M, H0, X, St - 7);
      Lemma_Bits_At_W (M, H0, X, St - 16);
      Lemma_Forms (W_Bits (M, X, St - 15), H0 (0), H0 (0));
      Lemma_Forms (W_Bits (M, X, St - 2), H0 (0), H0 (0));
      pragma Assert ((3 * (St - 16) + 1) / 3 = St - 16);
      pragma Assert ((3 * (St - 16) + 1) mod 3 = 1);
      pragma Assert ((3 * (St - 16)) / 3 = St - 16);
      pragma Assert ((3 * (St - 16)) mod 3 = 0);
      pragma Assert ((3 * (St - 16) + 2) / 3 = St - 16);
      pragma Assert ((3 * (St - 16) + 2) mod 3 = 2);
      pragma Assert
        (Bits_At (M, H0, X, S1_Ix (St)) = Small_1_Form (W_Bits (M, X, St - 2)));
      pragma Assert
        (Bits_At (M, H0, X, S0_Ix (St)) = Small_0_Form (W_Bits (M, X, St - 15)));
      pragma Assert (Gadgets.Words.All_Bits (L, 4));
      pragma Assert (Gadgets.Words.Assertion (L, 4, X.W (St)) = Zero);
      Lemma_Sum (L, 4, X.W (St));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 4)
         = Value (L (0)) + Value (L (1)) + Value (L (2)) + Value (L (3)));
      pragma Assert
        (Def (W_Ix (St))
         = (Op_Add, 4,
            [S1_Ix (St), W_Ix (St - 7), S0_Ix (St), W_Ix (St - 16),
             others => 0], 0));
      pragma Assert (V (S1_Ix (St)) = Word_Value (L (0)));
      pragma Assert (V (W_Ix (St - 7)) = Word_Value (L (1)));
      pragma Assert (V (S0_Ix (St)) = Word_Value (L (2)));
      pragma Assert (V (W_Ix (St - 16)) = Word_Value (L (3)));
      pragma Assert (V (W_Ix (St)) = Word_Value (X.W (St)));
      pragma Assert
        (Word_Value (X.W (St))
         = Word_Value (L (0)) + Word_Value (L (1)) + Word_Value (L (2))
           + Word_Value (L (3)));
   end Lemma_Value_Schedule;

   procedure Lemma_Value_Function
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64; T : Round; O : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       O <= 3
       and then Inputs_Hold (M, H0, X, S, Block) and then Assertions_Hold (M, H0, X),
     Post   => Value_Holds (M, H0, X, S, Block, First_Round + 6 * T + O)
   is
      V : constant Values := Decoded (M, H0, X);
   begin
      Lemma_Input_Bits (M, H0, X, S, Block);
      Lemma_Bits_At_Round (M, H0, X, T);
      Lemma_Forms (Var_Bits (H0, X, T, 4), Var_Bits (H0, X, T, 5),
                   Var_Bits (H0, X, T, 6));
      Lemma_Forms (Var_Bits (H0, X, T, 0), Var_Bits (H0, X, T, 1),
                   Var_Bits (H0, X, T, 2));
      pragma Assert ((6 * T + O) / 6 = T);
      pragma Assert ((6 * T + O) mod 6 = O);
      for P in Sha256.Word_Index loop
         pragma Assert (V (Var (T, P)) = Word_Value (Var_Bits (H0, X, T, P)));
         pragma Loop_Invariant
           (for all Q in Sha256.Word_Index range 0 .. P =>
              V (Var (T, Q)) = Word_Value (Var_Bits (H0, X, T, Q)));
      end loop;
      case O is
         when 0 =>
            pragma Assert
              (Def (Sg1_Ix (T)) = (Op_Sigma_1, 1, [Var (T, 4), others => 0], 0));
         when 1 =>
            pragma Assert
              (Def (Ch_Ix (T))
               = (Op_Ch, 3, [Var (T, 4), Var (T, 5), Var (T, 6), others => 0],
                  0));
         when 2 =>
            pragma Assert
              (Def (Sg0_Ix (T)) = (Op_Sigma_0, 1, [Var (T, 0), others => 0], 0));
         when others =>
            pragma Assert
              (Def (Mj_Ix (T))
               = (Op_Maj, 3, [Var (T, 0), Var (T, 1), Var (T, 2), others => 0],
                  0));
      end case;
   end Lemma_Value_Function;

   procedure Lemma_Value_E
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64; T : Round)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       Inputs_Hold (M, H0, X, S, Block) and then Assertions_Hold (M, H0, X),
     Post   => Value_Holds (M, H0, X, S, Block, E_Ix (T))
   is
      V : constant Values := Decoded (M, H0, X);
      L : constant Gadgets.Words.Word_List := E_Words (M, H0, X, T);
   begin
      Lemma_Input_Bits (M, H0, X, S, Block);
      Lemma_Bits_At_Round (M, H0, X, T);
      Lemma_Value_Bits_Of (K (Round_Index (T)));
      Lemma_Forms (Var_Bits (H0, X, T, 4), Var_Bits (H0, X, T, 5),
                   Var_Bits (H0, X, T, 6));
      Lemma_Forms (Var_Bits (H0, X, T, 0), Var_Bits (H0, X, T, 1),
                   Var_Bits (H0, X, T, 2));
      for P in Sha256.Word_Index loop
         pragma Assert (V (Var (T, P)) = Word_Value (Var_Bits (H0, X, T, P)));
         pragma Loop_Invariant
           (for all Q in Sha256.Word_Index range 0 .. P =>
              V (Var (T, Q)) = Word_Value (Var_Bits (H0, X, T, Q)));
      end loop;
      pragma Assert (V (W_Ix (T)) = Word_Value (W_Bits (M, X, T)));
      pragma Assert (V (Sg1_Ix (T)) = Word_Value (L (1)));
      pragma Assert (V (Ch_Ix (T)) = Word_Value (L (2)));
      pragma Assert (Word_Value (L (3)) = K (Round_Index (T)));
      pragma Assert ((6 * T + 4) / 6 = T);
      pragma Assert ((6 * T + 4) mod 6 = 4);
      pragma Assert (Gadgets.Words.All_Bits (L, 6));
      pragma Assert (Gadgets.Words.Assertion (L, 6, X.E (T)) = Zero);
      Lemma_Sum (L, 6, X.E (T));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 1)
         = Gadgets.Words.Sum_Upto (L, 0) + Value (L (0)));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 2)
         = Gadgets.Words.Sum_Upto (L, 1) + Value (L (1)));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 3)
         = Gadgets.Words.Sum_Upto (L, 2) + Value (L (2)));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 4)
         = Gadgets.Words.Sum_Upto (L, 3) + Value (L (3)));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 5)
         = Gadgets.Words.Sum_Upto (L, 4) + Value (L (4)));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 6)
         = Gadgets.Words.Sum_Upto (L, 5) + Value (L (5)));
      pragma Assert
        (Def (E_Ix (T))
         = (Op_Add, 5,
            [Var (T, 3), Var (T, 7), Sg1_Ix (T), Ch_Ix (T), W_Ix (T),
             others => 0], K (Round_Index (T))));
      pragma Assert (V (E_Ix (T)) = Word_Value (X.E (T)));
      pragma Assert
        (Word_Value (X.E (T))
         = Word_Value (L (0)) + Word_Value (L (1)) + Word_Value (L (2))
           + Word_Value (L (3)) + Word_Value (L (4)) + Word_Value (L (5)));
   end Lemma_Value_E;

   procedure Lemma_Value_A
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64; T : Round)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       Inputs_Hold (M, H0, X, S, Block) and then Assertions_Hold (M, H0, X),
     Post   => Value_Holds (M, H0, X, S, Block, A_Ix (T))
   is
      V : constant Values := Decoded (M, H0, X);
      L : constant Gadgets.Words.Word_List := A_Words (M, H0, X, T);
   begin
      Lemma_Input_Bits (M, H0, X, S, Block);
      Lemma_Bits_At_Round (M, H0, X, T);
      Lemma_Value_Bits_Of (K (Round_Index (T)));
      Lemma_Forms (Var_Bits (H0, X, T, 4), Var_Bits (H0, X, T, 5),
                   Var_Bits (H0, X, T, 6));
      Lemma_Forms (Var_Bits (H0, X, T, 0), Var_Bits (H0, X, T, 1),
                   Var_Bits (H0, X, T, 2));
      for P in Sha256.Word_Index loop
         pragma Assert (V (Var (T, P)) = Word_Value (Var_Bits (H0, X, T, P)));
         pragma Loop_Invariant
           (for all Q in Sha256.Word_Index range 0 .. P =>
              V (Var (T, Q)) = Word_Value (Var_Bits (H0, X, T, Q)));
      end loop;
      pragma Assert (V (W_Ix (T)) = Word_Value (W_Bits (M, X, T)));
      pragma Assert (V (Sg1_Ix (T)) = Word_Value (L (1)));
      pragma Assert (V (Ch_Ix (T)) = Word_Value (L (2)));
      pragma Assert (Word_Value (L (3)) = K (Round_Index (T)));
      pragma Assert (V (Sg0_Ix (T)) = Word_Value (L (5)));
      pragma Assert (V (Mj_Ix (T)) = Word_Value (L (6)));
      pragma Assert ((6 * T + 5) / 6 = T);
      pragma Assert ((6 * T + 5) mod 6 = 5);
      pragma Assert (Gadgets.Words.All_Bits (L, 7));
      pragma Assert (Gadgets.Words.Assertion (L, 7, X.A (T)) = Zero);
      Lemma_Sum (L, 7, X.A (T));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 1)
         = Gadgets.Words.Sum_Upto (L, 0) + Value (L (0)));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 2)
         = Gadgets.Words.Sum_Upto (L, 1) + Value (L (1)));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 3)
         = Gadgets.Words.Sum_Upto (L, 2) + Value (L (2)));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 4)
         = Gadgets.Words.Sum_Upto (L, 3) + Value (L (3)));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 5)
         = Gadgets.Words.Sum_Upto (L, 4) + Value (L (4)));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 6)
         = Gadgets.Words.Sum_Upto (L, 5) + Value (L (5)));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 7)
         = Gadgets.Words.Sum_Upto (L, 6) + Value (L (6)));
      pragma Assert
        (Def (A_Ix (T))
         = (Op_Add, 6,
            [Var (T, 7), Sg1_Ix (T), Ch_Ix (T), W_Ix (T), Sg0_Ix (T),
             Mj_Ix (T)], K (Round_Index (T))));
      pragma Assert (V (A_Ix (T)) = Word_Value (X.A (T)));
      pragma Assert
        (Word_Value (X.A (T))
         = Word_Value (L (0)) + Word_Value (L (1)) + Word_Value (L (2))
           + Word_Value (L (3)) + Word_Value (L (4)) + Word_Value (L (5))
           + Word_Value (L (6)));
   end Lemma_Value_A;

   procedure Lemma_Value_Out
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64; J : Sha256.Word_Index)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       Inputs_Hold (M, H0, X, S, Block) and then Assertions_Hold (M, H0, X),
     Post   => Value_Holds (M, H0, X, S, Block, First_Output + Natural (J))
   is
      V : constant Values := Decoded (M, H0, X);
      L : constant Gadgets.Words.Word_List := H_Words (H0, X, J);
   begin
      Lemma_Input_Bits (M, H0, X, S, Block);
      Lemma_Bits_At_Var (M, H0, X, 64, J);
      pragma Assert (V (Natural (J)) = Word_Value (H0 (J)));
      pragma Assert (V (Var (64, J)) = Word_Value (Var_Bits (H0, X, 64, J)));
      pragma Assert (Gadgets.Words.All_Bits (L, 2));
      pragma Assert (Gadgets.Words.Assertion (L, 2, X.H1 (J)) = Zero);
      Lemma_Sum (L, 2, X.H1 (J));
      pragma Assert
        (Gadgets.Words.Sum_Upto (L, 2) = Value (L (0)) + Value (L (1)));
      pragma Assert
        (Def (First_Output + Natural (J))
         = (Op_Add, 2, [Natural (J), Var (64, J), others => 0], 0));
      pragma Assert
        (V (First_Output + Natural (J)) = Word_Value (X.H1 (J)));
      pragma Assert
        (Word_Value (X.H1 (J)) = Word_Value (L (0)) + Word_Value (L (1)));
   end Lemma_Value_Out;

   procedure Lemma_Value
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64; I : Value_Index)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       Inputs_Hold (M, H0, X, S, Block) and then Assertions_Hold (M, H0, X),
     Post   => Value_Holds (M, H0, X, S, Block, I)
   is
   begin
      if I < First_Schedule then
         Lemma_Value_Input (M, H0, X, S, Block, I);
      elsif I < First_Round then
         declare
            St : constant Schedule_Step := 16 + (I - First_Schedule) / 3;
            O  : constant Natural := (I - First_Schedule) mod 3;
         begin
            pragma Assert (I = First_Schedule + 3 * (St - 16) + O);
            if O <= 1 then
               Lemma_Value_Small (M, H0, X, S, Block, St, O);
            else
               Lemma_Value_Schedule (M, H0, X, S, Block, St);
            end if;
         end;
      elsif I < First_Output then
         declare
            T : constant Round := (I - First_Round) / 6;
            O : constant Natural := (I - First_Round) mod 6;
         begin
            pragma Assert (I = First_Round + 6 * T + O);
            if O <= 3 then
               Lemma_Value_Function (M, H0, X, S, Block, T, O);
            elsif O = 4 then
               Lemma_Value_E (M, H0, X, S, Block, T);
            else
               Lemma_Value_A (M, H0, X, S, Block, T);
            end if;
         end;
      else
         Lemma_Value_Out
           (M, H0, X, S, Block, Sha256.Word_Index (I - First_Output));
      end if;
   end Lemma_Value;

   procedure Lemma_Block
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64)
   is
      V : constant Values := Decoded (M, H0, X);
   begin
      for I in Value_Index loop
         Lemma_Value (M, H0, X, S, Block, I);
         pragma Loop_Invariant
           (for all J in 0 .. I => V (J) = Eval (Def (J), V, S, Block, J));
      end loop;
      pragma Assert (Holds (V, S, Block));
      Lemma_Holds_Unique (V, S, Block);
      pragma Assert (V = Interpret (S, Block));
   end Lemma_Block;

end Sha256.Trace.Netlist.Gadget;
