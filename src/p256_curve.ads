--  P256_Curve: the group of NIST P-256 in projective coordinates, for
--  the ECDSA witness of upstream's signature circuit (chapter 9, block
--  6; ADR 0086). The witness holds the projective points of every
--  round of the circuit's scalar multiplication, so the formulas and
--  the representation are upstream's, not merely the group law:
--  core/algebra/src/ec.rs at d5e6be7, the complete addition and
--  doubling of Renes, Costello and Batina (2016, algorithms 1 and 3)
--  for a short Weierstrass curve with a general coefficient a, the
--  point at infinity (0, 1, 0), and a double-and-add scalar
--  multiplication from the least significant bit.
--
--  Constant time (ADR 0006, ADR 0086): the points are secrets of the
--  credential (the public key of the holder's device, the point R of
--  a signature). Add, Double and Affine are fixed sequences of field
--  operations; Affine inverts a secret Z with the fixed chain of
--  P256_Field.Inv, allowed by ADR 0086. Scalar_Mul is double-and-add-
--  always: the sum is computed at every bit and kept or dropped by a
--  masked selection (Select_Point), where upstream's scalar_mul
--  branches on the bit; the values are the same, since the dropped
--  sum is never used. Select_8 chooses one of eight points by masks
--  built from the index without a branch, where upstream indexes its
--  table with the secret bits. The guarantee is scoped to builds with
--  assertions disabled (header of gf2_128.ads).
--
--  Proof status: Silver (absence of run-time errors) on the
--  arithmetic; Gold on the selections (Select_Point and Select_8
--  return the point the mask or the index names). Nothing here is
--  proved against the group law: that the formulas compute the sum of
--  the points is an algebraic fact out of SMT reach, anchored by the
--  vectors of tests/vectors/p256_curve.txt (RFC 5903 key pairs for
--  Scalar_Mul, random points against the Python transcription) and by
--  the byte identity of the ECDSA witness with upstream's files.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with P256_Field;

package P256_Curve is

   use type P256_Field.Element;

   subtype Element is P256_Field.Element;
   subtype Limb_Array is P256_Field.Limb_Array;

   --  A projective point (X : Y : Z); the point at infinity is
   --  (0 : 1 : 0), as upstream's zero.
   type Point is record
      X, Y, Z : Element;
   end record;

   type Affine_Point is record
      X, Y : Element;
   end record;

   Infinity : constant Point :=
     (X => P256_Field.Zero, Y => P256_Field.One, Z => P256_Field.Zero);

   --  The curve y^2 = x^3 + a x + b over F_p with a = p - 3 and the base
   --  point G (RFC 5903 Section 3.1; SEC 2 v2.0 Section 2.4.2), as
   --  canonical integers.
   A_Limbs : constant Limb_Array :=
     [16#FFFF_FFFF_FFFF_FFFC#, 16#0000_0000_FFFF_FFFF#,
      16#0000_0000_0000_0000#, 16#FFFF_FFFF_0000_0001#];
   B_Limbs : constant Limb_Array :=
     [16#3BCE_3C3E_27D2_604B#, 16#651D_06B0_CC53_B0F6#,
      16#B3EB_BD55_7698_86BC#, 16#5AC6_35D8_AA3A_93E7#];
   GX_Limbs : constant Limb_Array :=
     [16#F4A1_3945_D898_C296#, 16#7703_7D81_2DEB_33A0#,
      16#F8BC_E6E5_63A4_40F2#, 16#6B17_D1F2_E12C_4247#];
   GY_Limbs : constant Limb_Array :=
     [16#CBB6_4068_37BF_51F5#, 16#2BCE_3357_6B31_5ECE#,
      16#8EE7_EB4A_7C0F_9E16#, 16#4FE3_42E2_FE1A_7F9B#];

   function Coef_A return Element is (P256_Field.From_Canonical (A_Limbs))
   with Global => null;
   function Coef_B return Element is (P256_Field.From_Canonical (B_Limbs))
   with Global => null;
   function Base_Point return Point is
     (X => P256_Field.From_Canonical (GX_Limbs),
      Y => P256_Field.From_Canonical (GY_Limbs),
      Z => P256_Field.One)
   with Global => null;

   --  The projective point of an affine one: (x : y : 1).
   function To_Point (P : Affine_Point) return Point is
     (X => P.X, Y => P.Y, Z => P256_Field.One)
   with Global => null;

   --  (X / Z, Y / Z); with Z = 0 both coordinates are zero, since the
   --  inverse is total (upstream asserts on a zero Z).
   function Affine (P : Point) return Affine_Point with Global => null;

   --  The complete formulas of upstream's ec.rs: add (algorithm 1 of
   --  Renes, Costello and Batina with 3 b precomputed) and double
   --  (algorithm 3). Total on all pairs of points, the point at
   --  infinity included.
   function Add (P1, P2 : Point) return Point with Global => null;
   function Double (P : Point) return Point with Global => null;

   --  A mask from a word: all ones when D = 0, zero otherwise, without
   --  a branch.
   function Mask_Of_Zero (D : Unsigned_64) return Unsigned_64 with
     Global => null,
     Post   => Mask_Of_Zero'Result = (if D = 0 then Unsigned_64'Last else 0);

   --  B where Mask is all ones, A where it is zero, limb by limb.
   function Select_Element (A, B : Element; Mask : Unsigned_64)
     return Element
   with Global => null,
        Pre  => Mask = 0 or else Mask = Unsigned_64'Last,
        Post => Select_Element'Result = (if Mask = 0 then A else B);

   function Select_Point (A, B : Point; Mask : Unsigned_64) return Point
   with Global => null,
        Pre  => Mask = 0 or else Mask = Unsigned_64'Last,
        Post => Select_Point'Result = (if Mask = 0 then A else B);

   --  The eight points a round of the ECDSA circuit's scalar
   --  multiplication chooses from (ecdsa2/concrete.rs, opts).
   subtype Table_Index is Natural range 0 .. 7;
   type Point_Table is array (Table_Index) of Point;

   --  T (I) by masks, no branch and no secret index.
   function Select_8 (T : Point_Table; I : Table_Index) return Point with
     Global => null,
     Post   => Select_8'Result = T (I);

   --  K P for a 256-bit scalar K given as four little-endian words,
   --  double-and-add-always from the least significant bit: the same
   --  projective result as upstream's scalar_mul over 256 bits.
   function Scalar_Mul (K : Limb_Array; P : Point) return Point with
     Global => null;

end P256_Curve;
