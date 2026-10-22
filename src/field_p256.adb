--  Same implements the predefined "=" for execution in the assertion-
--  enabled test build and is outside SPARK on purpose: the provers see
--  only its declaration and its Logical_Equal annotation. The rest of
--  the body is SPARK.

pragma SPARK_Mode (On);

with Field_P256.Laws;

package body Field_P256 is

   use type P256_Field.Element;

   function Same (A, B : P256_Field.Element) return Boolean with
     SPARK_Mode => Off
   is
   begin
      return A = B;
   end Same;

   procedure Checked_Inv
     (D : P256_Field.Element; R : out P256_Field.Element; Ok : out Boolean)
   is
   begin
      R  := P256_Field.Inv (D);
      Ok := D /= P256_Field.Zero
            and then P256_Field.Mul (R, D) = P256_Field.One;
   end Checked_Inv;

   procedure From_Subfield_Bytes
     (B : Bytes.Byte_Array; E : out P256_Field.Element; Ok : out Boolean)
   is
   begin
      P256_Field.From_Bytes (B, E, Ok);
   end From_Subfield_Bytes;

   procedure Lemma_Mul_Assoc (A, B, C : P256_Field.Element) is
   begin
      P256_Field.Lemma_Mul_Assoc (A, B, C);
      Laws.Lemma_Same (P256_Field.Mul (P256_Field.Mul (A, B), C),
                  P256_Field.Mul (A, P256_Field.Mul (B, C)));
   end Lemma_Mul_Assoc;

end Field_P256;
