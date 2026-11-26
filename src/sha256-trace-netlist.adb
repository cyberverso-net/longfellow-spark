pragma SPARK_Mode (On);

package body Sha256.Trace.Netlist is

   --  Every argument of a definition is an earlier value.
   procedure Lemma_Def_Earlier (I : Value_Index) with
     Ghost,
     Global => null,
     Post   => Args_Earlier (Def (I), I)
   is
   begin
      if I >= First_Round and then I < First_Output then
         pragma Assert
           (for all P in Sha256.Word_Index =>
              Var ((I - First_Round) / 6, P)
              < First_Round + 6 * ((I - First_Round) / 6));
      end if;
   end Lemma_Def_Earlier;

   function Generate return Netlist is
      N : Netlist := [others => (Op_State, 0, [others => 0], 0)];
   begin
      for I in Value_Index loop
         N (I) := Def (I);
         Lemma_Def_Earlier (I);
         pragma Loop_Invariant (for all J in 0 .. I => N (J) = Def (J));
         pragma Loop_Invariant
           (for all J in 0 .. I => Args_Earlier (Def (J), J));
      end loop;
      return N;
   end Generate;

   ----------------------------------------------------------------------
   --  The lemmas of the proof
   ----------------------------------------------------------------------

   --  One round moves b, c, d and f, g, h down by one (Round_Step).
   procedure Lemma_Shift
     (H0 : Sha256.State; Block : Bytes_64; T : Round; P : Sha256.Word_Index)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => P /= 0 and then P /= 4,
     Post   => Rounds (H0, Block, T + 1) (P) = Rounds (H0, Block, T) (P - 1)
   is
   begin
      pragma Assert
        (Rounds (H0, Block, T + 1)
         = Round_Step (Rounds (H0, Block, T), Block, T));
   end Lemma_Shift;

   --  Working variable P before round T is the a (or the e) of an
   --  earlier round, or a word of H0: what Var names.
   procedure Lemma_Var
     (H0 : Sha256.State; Block : Bytes_64; T : Round_Or_End;
      P : Sha256.Word_Index)
   with
     Ghost              => Proof_Only,
     Global             => null,
     Subprogram_Variant => (Decreases => T),
     Post               =>
       Rounds (H0, Block, T) (P)
       = (if P <= 3 then
            (if T > Natural (P) then Rounds (H0, Block, T - Natural (P)) (0)
             else H0 (P - Sha256.Word_Index (T)))
          else
            (if T > Natural (P) - 4
             then Rounds (H0, Block, T - (Natural (P) - 4)) (4)
             else H0 (P - Sha256.Word_Index (T))))
   is
   begin
      if T = 0 then
         pragma Assert (Rounds (H0, Block, 0) = H0);
      elsif P = 0 or else P = 4 then
         null;
      else
         Lemma_Shift (H0, Block, T - 1, P);
         Lemma_Var (H0, Block, T - 1, P - 1);
      end if;
   end Lemma_Var;

   --  The value Var names holds that working variable.
   procedure Lemma_Expected_Var
     (H0 : Sha256.State; Block : Bytes_64; T : Round_Or_End;
      P : Sha256.Word_Index)
   with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Expected (H0, Block, Var (T, P)) = Rounds (H0, Block, T) (P)
   is
   begin
      Lemma_Var (H0, Block, T, P);
      if P <= 3 then
         if T > Natural (P) then
            pragma Assert
              (Expected (H0, Block, A_Ix (T - 1 - Natural (P)))
               = Rounds (H0, Block, T - Natural (P)) (0));
         end if;
      else
         if T > Natural (P) - 4 then
            pragma Assert
              (Expected (H0, Block, E_Ix (T - 1 - (Natural (P) - 4)))
               = Rounds (H0, Block, T - (Natural (P) - 4)) (4));
         end if;
      end if;
   end Lemma_Expected_Var;

   --  The value W_Ix names holds the schedule word.
   procedure Lemma_Expected_W
     (H0 : Sha256.State; Block : Bytes_64; I : Round)
   with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Expected (H0, Block, W_Ix (I)) = Schedule_Word (Block, I)
   is
   begin
      if I < 16 then
         pragma Assert (Schedule_Word (Block, I) = Block_Word (Block, I));
      else
         pragma Assert ((W_Ix (I) - First_Schedule) mod 3 = 2);
         pragma Assert (16 + (W_Ix (I) - First_Schedule) / 3 = I);
      end if;
   end Lemma_Expected_W;

   --  One step of the interpretation: the definition of I over values
   --  that hold their words gives the word of I.
   procedure Lemma_Step
     (V : Values; H0 : Sha256.State; Block : Bytes_64; I : Value_Index)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => (for all J in 0 .. I - 1 => V (J) = Expected (H0, Block, J)),
     Post   => Eval (Def (I), V, H0, Block, I) = Expected (H0, Block, I)
   is
   begin
      if I < First_Message then
         null;
      elsif I < First_Schedule then
         pragma Assert
           (Message_Word (Block, I - First_Message)
            = Block_Word (Block, I - First_Message));
         pragma Assert
           (Expected (H0, Block, I) = Block_Word (Block, I - First_Message));
      elsif I < First_Round then
         declare
            S : constant Schedule_Step := 16 + (I - First_Schedule) / 3;
         begin
            case (I - First_Schedule) mod 3 is
               when 0 =>
                  Lemma_Expected_W (H0, Block, S - 15);
                  pragma Assert (W_Ix (S - 15) < I);
                  pragma Assert
                    (Expected (H0, Block, I)
                     = Small_0 (Schedule_Word (Block, S - 15)));
                  pragma Assert
                    (Eval (Def (I), V, H0, Block, I)
                     = Expected (H0, Block, I));
               when 1 =>
                  Lemma_Expected_W (H0, Block, S - 2);
                  pragma Assert (W_Ix (S - 2) < I);
                  pragma Assert
                    (Expected (H0, Block, I)
                     = Small_1 (Schedule_Word (Block, S - 2)));
                  pragma Assert
                    (Eval (Def (I), V, H0, Block, I)
                     = Expected (H0, Block, I));
               when others =>
                  Lemma_Expected_W (H0, Block, S - 7);
                  Lemma_Expected_W (H0, Block, S - 16);
                  pragma Assert
                    (V (S1_Ix (S)) = Small_1 (Schedule_Word (Block, S - 2)));
                  pragma Assert
                    (V (S0_Ix (S)) = Small_0 (Schedule_Word (Block, S - 15)));
                  pragma Assert
                    (Expected (H0, Block, I) = Schedule_Word (Block, S));
                  pragma Assert
                    (Schedule_Word (Block, S)
                     = Small_1 (Schedule_Word (Block, S - 2))
                       + Schedule_Word (Block, S - 7)
                       + Small_0 (Schedule_Word (Block, S - 15))
                       + Schedule_Word (Block, S - 16));
                  pragma Assert
                    (Eval (Def (I), V, H0, Block, I)
                     = Expected (H0, Block, I));
            end case;
         end;
      elsif I < First_Output then
         declare
            T : constant Round := (I - First_Round) / 6;
            R : constant Sha256.State := Rounds (H0, Block, T);
         begin
            for P in Sha256.Word_Index loop
               Lemma_Expected_Var (H0, Block, T, P);
               pragma Loop_Invariant
                 (for all Q in 0 .. P => V (Var (T, Q)) = R (Q));
            end loop;
            pragma Assert
              (Rounds (H0, Block, T + 1) = Round_Step (R, Block, T));
            Lemma_Expected_W (H0, Block, T);
            pragma Assert (V (W_Ix (T)) = Schedule_Word (Block, T));
            pragma Assert (I = First_Round + 6 * T + (I - First_Round) mod 6);
            case (I - First_Round) mod 6 is
               when 0 =>
                  pragma Assert
                    (Def (I)
                     = (Op_Sigma_1, 1, [Var (T, 4), others => 0], 0));
                  pragma Assert (Expected (H0, Block, I) = Sigma_1 (R (4)));
               when 1 =>
                  pragma Assert
                    (Expected (H0, Block, I)
                     = Ch (R (4), R (5), R (6)));
               when 2 =>
                  pragma Assert (Expected (H0, Block, I) = Sigma_0 (R (0)));
               when 3 =>
                  pragma Assert
                    (Expected (H0, Block, I) = Maj (R (0), R (1), R (2)));
               when 4 =>
                  pragma Assert (Sg1_Ix (T) < I and then Ch_Ix (T) < I);
                  pragma Assert
                    (Expected (H0, Block, Sg1_Ix (T))
                     = Sigma_1 (R (4)));
                  pragma Assert
                    (Expected (H0, Block, Ch_Ix (T))
                     = Ch (R (4), R (5), R (6)));
                  pragma Assert
                    (Eval (Def (I), V, H0, Block, I)
                     = R (3) + R (7) + Sigma_1 (R (4))
                       + Ch (R (4), R (5), R (6))
                       + Schedule_Word (Block, T) + K (Round_Index (T)));
                  pragma Assert
                    (Expected (H0, Block, I) = Round_Step (R, Block, T) (4));
               when others =>
                  pragma Assert (Sg1_Ix (T) < I and then Ch_Ix (T) < I
                                 and then Sg0_Ix (T) < I
                                 and then Mj_Ix (T) < I);
                  pragma Assert
                    (Expected (H0, Block, Sg1_Ix (T))
                     = Sigma_1 (R (4)));
                  pragma Assert
                    (Expected (H0, Block, Ch_Ix (T))
                     = Ch (R (4), R (5), R (6)));
                  pragma Assert
                    (Expected (H0, Block, Sg0_Ix (T))
                     = Sigma_0 (R (0)));
                  pragma Assert
                    (Expected (H0, Block, Mj_Ix (T))
                     = Maj (R (0), R (1), R (2)));
                  pragma Assert
                    (Eval (Def (I), V, H0, Block, I)
                     = R (7) + Sigma_1 (R (4)) + Ch (R (4), R (5), R (6))
                       + Schedule_Word (Block, T) + Sigma_0 (R (0))
                       + Maj (R (0), R (1), R (2)) + K (Round_Index (T)));
                  pragma Assert
                    (Expected (H0, Block, I) = Round_Step (R, Block, T) (0));
            end case;
         end;
      else
         declare
            J : constant Sha256.Word_Index :=
              Sha256.Word_Index (I - First_Output);
         begin
            Lemma_Expected_Var (H0, Block, 64, J);
            pragma Assert (V (Natural (J)) = H0 (J));
            pragma Assert (V (Var (64, J)) = Rounds (H0, Block, 64) (J));
            pragma Assert
              (Expected (H0, Block, I)
               = H0 (J) + Rounds (H0, Block, 64) (J));
            pragma Assert
              (Eval (Def (I), V, H0, Block, I) = Expected (H0, Block, I));
         end;
      end if;
   end Lemma_Step;

   ----------------------------------------------------------------------
   --  The interpretation
   ----------------------------------------------------------------------

   --  Values that hold their words satisfy every definition.
   procedure Lemma_Holds (V : Values; H0 : Sha256.State; Block : Bytes_64)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => (for all J in Value_Index => V (J) = Expected (H0, Block, J)),
     Post   => Holds (V, H0, Block)
   is
   begin
      for I in Value_Index loop
         Lemma_Step (V, H0, Block, I);
         pragma Loop_Invariant
           (for all J in 0 .. I => V (J) = Eval (Def (J), V, H0, Block, J));
      end loop;
   end Lemma_Holds;

   function Interpret (H0 : Sha256.State; Block : Bytes_64) return Values is
      V : Values := [others => 0];
   begin
      for I in Value_Index loop
         pragma Assert (Proof_Only => (for all J in 0 .. I - 1 =>
                          V (J) = Expected (H0, Block, J)));
         Lemma_Step (V, H0, Block, I);
         V (I) := Eval (Def (I), V, H0, Block, I);
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J in 0 .. I => V (J) = Expected (H0, Block, J)));
      end loop;
      Lemma_Holds (V, H0, Block);
      return V;
   end Interpret;

   procedure Lemma_Holds_Unique
     (V : Values; H0 : Sha256.State; Block : Bytes_64)
   is
      R : constant Values := Interpret (H0, Block);
   begin
      for I in Value_Index loop
         Lemma_Def_Earlier (I);
         pragma Assert
           (Eval (Def (I), V, H0, Block, I) = Eval (Def (I), R, H0, Block, I));
         pragma Loop_Invariant (for all J in 0 .. I => V (J) = R (J));
      end loop;
   end Lemma_Holds_Unique;

end Sha256.Trace.Netlist;
