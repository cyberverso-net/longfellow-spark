--  Local_Check_GF2_128_Laws: the lemma of Local_Check over GF(2^128)
--  from its executable check. Check_Product compares the coefficients
--  with the predefined equality of GF2_128.Element; Field_GF2_128.Laws
--  turns each comparison into Same, which Lemma_Product takes. ADR 0093.
--
--  Proof status: Gold. Trusted: Same as the equality of the field
--  (register row T6); the contracts at Proof_Only (T8).

pragma SPARK_Mode (On);

with Proof_Levels;
with Local_Check_GF2_128;

package Local_Check_GF2_128_Laws is

   package LC renames Local_Check_GF2_128;

   --  The lemma of the executable check: if Check_Product passes, then
   --  for every assignment V the terms' value is the product of the forms.
   procedure Lemma_Product_Checked
     (T : LC.Term_Array; NT : LC.Term_Count;
      A : LC.Form_Array; NA : LC.Form_Count;
      B : LC.Form_Array; NB : LC.Form_Count;
      M : LC.Pair_Map; V : LC.Values)
   with Ghost => Proof_Only, Global => null,
        Pre  => LC.Wires_In (T, NT, V)
                and then LC.Form_In (A, NA, V) and then LC.Form_In (B, NB, V)
                and then LC.Check_Product (T, NT, A, NA, B, NB, M),
        Post => LC.Same (LC.Sum_Terms (T, NT, V),
                         LC."*" (LC.Sum_Form (A, NA, V),
                                 LC.Sum_Form (B, NB, V)));

end Local_Check_GF2_128_Laws;
