--  Same implements the predefined "=" for execution in the assertion-
--  enabled test build and is outside SPARK on purpose: the provers see
--  only its declaration and its Logical_Equal annotation. The rest of
--  the body is SPARK.

pragma SPARK_Mode (On);

with Field_GF2_128.Laws;

package body Field_GF2_128 is

   use type GF2_128.Element;

   function Same (A, B : GF2_128.Element) return Boolean with
     SPARK_Mode => Off
   is
   begin
      return A = B;
   end Same;

   procedure Checked_Inv
     (D : GF2_128.Element; R : out GF2_128.Element; Ok : out Boolean)
   is
   begin
      R  := GF2_128.Inv (D);
      Ok := D /= GF2_128.Zero and then GF2_128.Mul (R, D) = GF2_128.One;
   end Checked_Inv;

   procedure From_Subfield_Bytes
     (B : Bytes.Byte_Array; E : out GF2_128.Element; Ok : out Boolean)
   is
      V : constant Natural :=
        Natural (B (B'First)) + 256 * Natural (B (B'First + 1));
   begin
      E  := GF2_128.Inject (V);
      Ok := True;
   end From_Subfield_Bytes;

   function To_Subfield_Bytes (E : GF2_128.Element) return Bytes.Byte_Array
   is
      V : constant GF2_128.Subfield_Value := GF2_128.Subfield_Coords (E);
   begin
      return [0 => Unsigned_8 (V mod 256), 1 => Unsigned_8 (V / 256)];
   end To_Subfield_Bytes;

   procedure Lemma_Mul_Assoc (A, B, C : GF2_128.Element) is
   begin
      GF2_128.Lemma_Mul_Assoc (A, B, C);
      Laws.Lemma_Same (GF2_128.Mul (GF2_128.Mul (A, B), C),
                  GF2_128.Mul (A, GF2_128.Mul (B, C)));
   end Lemma_Mul_Assoc;

   procedure Lemma_Mul_Comm (A, B : GF2_128.Element) is
   begin
      GF2_128.Lemma_Mul_Comm (A, B);
      Laws.Lemma_Same (GF2_128.Mul (A, B),
                       GF2_128.Mul (B, A));
   end Lemma_Mul_Comm;

   procedure Lemma_Mul_One (A : GF2_128.Element) is
   begin
      GF2_128.Lemma_Mul_One (A);
      Laws.Lemma_Same (GF2_128.Mul (A, GF2_128.One),
                       A);
   end Lemma_Mul_One;

   procedure Lemma_Mul_Distrib (A, B, C : GF2_128.Element) is
   begin
      GF2_128.Lemma_Mul_Distrib (A, B, C);
      Laws.Lemma_Same (GF2_128.Mul (A, GF2_128.Add (B, C)),
                       GF2_128.Add (GF2_128.Mul (A, B), GF2_128.Mul (A, C)));
   end Lemma_Mul_Distrib;

   procedure Lemma_Mul_Distrib_Sub (A, B, C : GF2_128.Element) is
   begin
      GF2_128.Lemma_Mul_Distrib_Sub (A, B, C);
      Laws.Lemma_Same (GF2_128.Mul (A, GF2_128.Sub (B, C)),
                       GF2_128.Sub (GF2_128.Mul (A, B), GF2_128.Mul (A, C)));
   end Lemma_Mul_Distrib_Sub;

   procedure Lemma_Add_Assoc (A, B, C : GF2_128.Element) is
      L : constant GF2_128.Element := GF2_128.Add (GF2_128.Add (A, B), C);
      R : constant GF2_128.Element := GF2_128.Add (A, GF2_128.Add (B, C));
   begin
      pragma Assert (L.Limbs (0) = R.Limbs (0));
      pragma Assert (L.Limbs (1) = R.Limbs (1));
      Laws.Lemma_Same (L, R);
   end Lemma_Add_Assoc;

   procedure Lemma_Add_Comm (A, B : GF2_128.Element) is
      L : constant GF2_128.Element := GF2_128.Add (A, B);
      R : constant GF2_128.Element := GF2_128.Add (B, A);
   begin
      pragma Assert (L.Limbs (0) = R.Limbs (0));
      pragma Assert (L.Limbs (1) = R.Limbs (1));
      Laws.Lemma_Same (L, R);
   end Lemma_Add_Comm;

   procedure Lemma_Add_Zero (A : GF2_128.Element) is
      L : constant GF2_128.Element := GF2_128.Add (A, GF2_128.Zero);
   begin
      pragma Assert (L.Limbs (0) = A.Limbs (0));
      pragma Assert (L.Limbs (1) = A.Limbs (1));
      Laws.Lemma_Same (L, A);
   end Lemma_Add_Zero;

   procedure Lemma_Add_Neg (A : GF2_128.Element) is
      L : constant GF2_128.Element := GF2_128.Add (A, GF2_128.Neg (A));
   begin
      pragma Assert (L.Limbs (0) = 0);
      pragma Assert (L.Limbs (1) = 0);
      Laws.Lemma_Same (L, GF2_128.Zero);
   end Lemma_Add_Neg;

   procedure Lemma_Sub_Def (A, B : GF2_128.Element) is
   begin
      Laws.Lemma_Same (GF2_128.Sub (A, B),
                       GF2_128.Add (A, GF2_128.Neg (B)));
   end Lemma_Sub_Def;

end Field_GF2_128;
