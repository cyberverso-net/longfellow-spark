--  Same implements the predefined "=" for execution in the assertion-
--  enabled test build and is outside SPARK on purpose: the provers see
--  only its declaration and its Logical_Equal annotation. The rest of
--  the body is SPARK.

pragma SPARK_Mode (On);

with Field_P256.Laws;

package body Field_P256 is

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

   procedure Lemma_Mul_Comm (X, Y : P256_Field.Element) is
   begin
      P256_Field.Lemma_Mul_Comm (X, Y);
      Laws.Lemma_Same (P256_Field.Mul (X, Y),
                       P256_Field.Mul (Y, X));
   end Lemma_Mul_Comm;

   procedure Lemma_Mul_One (A : P256_Field.Element) is
   begin
      P256_Field.Lemma_Mul_One (A);
      Laws.Lemma_Same (P256_Field.Mul (A, P256_Field.One),
                       A);
   end Lemma_Mul_One;

   procedure Lemma_Mul_Distrib (A, B, C : P256_Field.Element) is
   begin
      P256_Field.Lemma_Mul_Distrib (A, B, C);
      Laws.Lemma_Same (P256_Field.Mul (A, P256_Field.Add (B, C)),
                       P256_Field.Add (P256_Field.Mul (A, B),
                                     P256_Field.Mul (A, C)));
   end Lemma_Mul_Distrib;

   procedure Lemma_Mul_Distrib_Sub (A, B, C : P256_Field.Element) is
   begin
      P256_Field.Lemma_Mul_Distrib_Sub (A, B, C);
      Laws.Lemma_Same (P256_Field.Mul (A, P256_Field.Sub (B, C)),
                       P256_Field.Sub (P256_Field.Mul (A, B),
                                     P256_Field.Mul (A, C)));
   end Lemma_Mul_Distrib_Sub;

   procedure Lemma_Add_Assoc (A, B, C : P256_Field.Element) is
   begin
      P256_Field.Lemma_Add_Assoc (A, B, C);
      Laws.Lemma_Same (P256_Field.Add (P256_Field.Add (A, B), C),
                       P256_Field.Add (A, P256_Field.Add (B, C)));
   end Lemma_Add_Assoc;

   procedure Lemma_Add_Comm (X, Y : P256_Field.Element) is
   begin
      P256_Field.Lemma_Add_Comm (X, Y);
      Laws.Lemma_Same (P256_Field.Add (X, Y),
                       P256_Field.Add (Y, X));
   end Lemma_Add_Comm;

   procedure Lemma_Add_Zero (A : P256_Field.Element) is
   begin
      P256_Field.Lemma_Add_Zero (A);
      Laws.Lemma_Same (P256_Field.Add (A, P256_Field.Zero),
                       A);
   end Lemma_Add_Zero;

   procedure Lemma_Add_Neg (A : P256_Field.Element) is
   begin
      P256_Field.Lemma_Add_Neg (A);
      Laws.Lemma_Same (P256_Field.Add (A, P256_Field.Neg (A)),
                       P256_Field.Zero);
   end Lemma_Add_Neg;

   procedure Lemma_Sub_Def (A, B : P256_Field.Element) is
   begin
      P256_Field.Lemma_Sub_Def (A, B);
      Laws.Lemma_Same (P256_Field.Sub (A, B),
                       P256_Field.Add (A, P256_Field.Neg (B)));
   end Lemma_Sub_Def;

end Field_P256;
