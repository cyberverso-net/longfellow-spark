pragma SPARK_Mode (On);

package body Fisher_Yates is

   --  Exchange two entries; the others stay.
   procedure Swap (A : in out Index_Array; I, J : Natural) with
     Global => null,
     Pre    => I in A'Range and then J in A'Range,
     Post   =>
       A (I) = A'Old (J) and then A (J) = A'Old (I)
       and then (for all X in A'Range =>
                   (if X /= I and then X /= J then A (X) = A'Old (X)))
   is
      T : constant Natural := A (I);
   begin
      A (I) := A (J);
      A (J) := T;
   end Swap;

   procedure Lemma_Draws_Below_Empty (V : Index_Array; N : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Draws_Below);
   begin
      null;
   end Lemma_Draws_Below_Empty;

   procedure Record_Draw
     (V : in out Index_Array; N : Natural; I : Natural; X : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Draws_Below);
   begin
      V (I) := X;
      --  N appears in the contracts only; the assertion restates the
      --  precondition so that the body refers to it (no warning).
      pragma Assert (V (I) < N - I);
   end Record_Draw;

   procedure Choose (N : Natural; V : Index_Array; R : out Index_Array) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Draws_Below);
      A   : Index_Array (0 .. N - 1) := [others => 0];
      --  The inverse of A: Pos (A (X)) = X for every X. It makes "no two
      --  entries equal" a linear check instead of the quadratic
      --  quantifier over pairs, which the assertion-enabled test build
      --  would execute at every iteration (65535 squared on Appendix
      --  B.2.5): if A (X) = A (Y) then X = Pos (A (X)) = Pos (A (Y)) = Y.
      Pos : Index_Array (0 .. N - 1) := [others => 0] with Ghost;
   begin
      for I in A'Range loop
         A (I)   := I;
         Pos (I) := I;
         pragma Loop_Invariant
           (for all X in 0 .. I => A (X) = X and then Pos (X) = X);
      end loop;
      for I in R'Range loop
         R (I) := 0;
      end loop;
      for I in V'Range loop
         Pos (A (I))         := I + V (I);
         Pos (A (I + V (I))) := I;
         Swap (A, I, I + V (I));
         R (I) := A (I);
         pragma Loop_Invariant
           (for all X in A'Range => A (X) < N and then Pos (A (X)) = X);
         pragma Loop_Invariant (for all P in 0 .. I => R (P) = A (P));
      end loop;
   end Choose;

end Fisher_Yates;
