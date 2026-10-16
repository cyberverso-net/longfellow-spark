--  Same implements the predefined "=" for execution in the assertion-
--  enabled test build and is outside SPARK on purpose: the provers see
--  only its declaration and its Logical_Equal annotation. The rest of
--  the body is SPARK.

pragma SPARK_Mode (On);

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

end Field_GF2_128;
