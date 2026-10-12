--  Body outside SPARK on purpose: Same implements the predefined "="
--  for execution in the assertion-enabled test build; the provers see
--  only the declaration and its Logical_Equal annotation.

pragma SPARK_Mode (Off);

package body Field_GF2_128 is

   use type GF2_128.Element;

   function Same (A, B : GF2_128.Element) return Boolean is
   begin
      return A = B;
   end Same;

end Field_GF2_128;
