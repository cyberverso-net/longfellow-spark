pragma SPARK_Mode (On);

package body Gadgets.Words is

   --  The bridge of G3: the statement is the contract, proved in Lean
   --  (LongfellowSpark.Model.assert_eqmod); register row L4.
   procedure Lemma_Assert_Eqmod (L : Word_List; K : Term_Count; A : Word_Bits)
   with SPARK_Mode => Off
   is
   begin
      null;
   end Lemma_Assert_Eqmod;

end Gadgets.Words;
