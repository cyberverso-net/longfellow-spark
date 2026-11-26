pragma SPARK_Mode (On);

with Field_GF2_128.Laws;

package body Local_Check_GF2_128_Laws is

   procedure Lemma_Product_Checked
     (T : LC.Term_Array; NT : LC.Term_Count;
      A : LC.Form_Array; NA : LC.Form_Count;
      B : LC.Form_Array; NB : LC.Form_Count;
      M : LC.Pair_Map; V : LC.Values)
   is
   begin
      --  Each coefficient comparison of the check, to Same.
      for K in 1 .. NT loop
         Field_GF2_128.Laws.Lemma_Same
           (T (K).K, LC.Collected (A, NA, B, NB, M, K, NA, NB));
         pragma Loop_Invariant
           (for all L in 1 .. K =>
              LC.Same (T (L).K, LC.Collected (A, NA, B, NB, M, L, NA, NB)));
      end loop;
      pragma Assert (LC.Check_Product_Same (T, NT, A, NA, B, NB, M));
      LC.Lemma_Product (T, NT, A, NA, B, NB, M, V);
   end Lemma_Product_Checked;

end Local_Check_GF2_128_Laws;
