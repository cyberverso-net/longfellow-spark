--  Body outside SPARK on purpose: Same implements the predefined "="
--  for execution in the assertion-enabled test build; the provers see
--  only the declaration and its Logical_Equal annotation.

pragma SPARK_Mode (Off);

package body Field_P256 is

   use type P256_Field.Element;

   function Same (A, B : P256_Field.Element) return Boolean is
   begin
      return A = B;
   end Same;

end Field_P256;
