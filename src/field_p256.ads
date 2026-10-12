--  Field_P256: the P-256 base field as a Field_Signature instance
--  (ADR 0024, ADR 0025).
--
--  P2 = 2, the third sumcheck evaluation point for fields of odd
--  characteristic (draft-03 Section 6.4). The Lagrange denominators
--  are d0 = (0 - 1) (0 - 2) = 2, d1 = (1 - 0) (1 - 2) = -1 and
--  d2 = (2 - 0) (2 - 1) = 2, so the inverses are (p + 1) / 2, p - 1
--  and (p + 1) / 2. They are computed by
--  tests/vectors/gen_sumcheck_vectors.py (checked by d * inv (d) = 1)
--  and re-checked by the harness sumcheck_kat with Mul at every run.
--  Limbs are little-endian, as in P256_Field.

pragma SPARK_Mode (On);

with P256_Field;
with Field_Signature;

package Field_P256 is

   P2 : constant P256_Field.Element := (Limbs => [2, 0, 0, 0]);

   --  (p + 1) / 2 = 1 / 2
   Half : constant P256_Field.Element :=
     (Limbs => [16#0000000000000000#, 16#0000000080000000#,
                16#8000000000000000#, 16#7FFFFFFF80000000#]);

   --  p - 1 = -1 = 1 / (-1)
   Minus_One : constant P256_Field.Element :=
     (Limbs => [16#FFFFFFFFFFFFFFFE#, 16#00000000FFFFFFFF#,
                16#0000000000000000#, 16#FFFFFFFF00000001#]);

   package Sig is new Field_Signature
     (Element    => P256_Field.Element,
      Zero       => P256_Field.Zero,
      One        => P256_Field.One,
      P2         => P2,
      "+"        => P256_Field.Add,
      "-"        => P256_Field.Sub,
      "*"        => P256_Field.Mul,
      Neg        => P256_Field.Neg,
      L0_Den_Inv => Half,
      L1_Den_Inv => Minus_One,
      L2_Den_Inv => Half);

end Field_P256;
