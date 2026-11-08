--  Ecdsa_Witness: the private inputs of one ECDSA verification in
--  upstream's signature circuit, in the legacy form of versions 5 to 7
--  (chapter 9, block 6; ADR 0086). From a public key (x, y), a digest
--  e and a signature (r, s), the 1,034 elements that
--  push_legacy_verify_witness_3 of runtime/src/concrete/legacy/
--  private.rs pushes at d5e6be7, computed as circuits/ecdsa2/src/
--  concrete.rs computes them (given and derived):
--
--    rx, ry        the point R = e s^-1 G + r s^-1 Pk, rx taken from r
--                  and ry from the point;
--    rx^-1, nms^-1, pkx^-1
--                  three inverses in the base field; nms is -s mod q,
--                  a scalar-field value reduced into the base field and
--                  inverted there, as the circuit wants it;
--    G + Pk, G + R, Pk + R, G + Pk + R
--                  four affine sums, eight elements;
--    then, for i from 255 down to 0: the digit b_i = e_i + 2 r_i + 4
--    nms_i (the i-th bits of e, r and nms, e and r as the 256-bit
--    integers given, not reduced) as the element 2 b_i - 7, and for
--    i > 0 the projective point P_i of the circuit's scalar
--    multiplication, P <- 2 P + T (4 e_i + 2 r_i + nms_i) from the
--    point at infinity over the table T = (O, R, Pk, Pk + R, G, G + R,
--    G + Pk, G + Pk + R). The two encodings of the same three bits
--    are upstream's: the digit weighs e least (private.rs), the table
--    index weighs it most (concrete.rs).
--
--  13 + 256 + 255 * 3 = 1,034 elements (Count). The signature value s
--  must be below q: upstream's builder converts it with
--  words64_to_element and stops on a value at or above q, where e and
--  r are reduced; the precondition of Push_Legacy states it, and the
--  caller refuses such a signature with a status (block 6c).
--
--  Proof status: Silver, with one Gold fact, the frame: Push_Legacy
--  changes nothing outside W (First .. First + Count - 1). That it
--  fills that interval, in this order, with these values, rests on
--  P256_Field (Gold), Q256_Field (Gold but Inv) and P256_Curve (Silver)
--  and is tested: the vectors of tests/vectors/ecdsa_witness.txt and
--  the byte identity with the signature witness files of upstream's
--  two archives (ecdsa_kat).
--
--  Constant time (ADR 0086): the key, the digest and the signature
--  are secrets of the credential. Every step is a fixed sequence of
--  field and curve operations; the digit selects the table entry by
--  masks (P256_Curve.Select_8); the bits are read at positions that
--  depend on the loop counter only; the inverses are the fixed chains
--  of the two fields. The guarantee is scoped to builds with
--  assertions disabled.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with P256_Field;
with Q256_Field;
with P256_Curve;
with Sumcheck_Algebra_P256;

package Ecdsa_Witness is

   use type P256_Field.Element;

   package SAP renames Sumcheck_Algebra_P256;

   --  A 256-bit integer as four little-endian words: the digests, the
   --  coordinates and the signature values as upstream's Nat.
   subtype Nat_256 is P256_Field.Limb_Array;

   --  The same four words as the scalar field's word array.
   function To_Q (N : Nat_256) return Q256_Field.Limb_Array is
     ([N (0), N (1), N (2), N (3)])
   with Global => null;

   Count : constant := 13 + 256 + 255 * 3;

   --  The bit I of N, 0 or 1, read at a position fixed by I.
   function Bit (N : Nat_256; I : Natural) return Unsigned_64 is
     (Shift_Right (N (I / 64), I mod 64) and 1)
   with Global => null, Pre => I <= 255, Post => Bit'Result <= 1;

   --  The digit of round I: e_I + 2 r_I + 4 nms_I.
   function Digit (E, R, Nms : Nat_256; I : Natural) return Natural is
     (Natural (Bit (E, I) + 2 * Bit (R, I) + 4 * Bit (Nms, I)))
   with Global => null, Pre => I <= 255, Post => Digit'Result <= 7;

   --  The table index of round I: 4 e_I + 2 r_I + nms_I.
   function Table_Index_Of (E, R, Nms : Nat_256; I : Natural) return Natural
   is (Natural (4 * Bit (E, I) + 2 * Bit (R, I) + Bit (Nms, I)))
   with Global => null, Pre => I <= 255, Post => Table_Index_Of'Result <= 7;

   --  The element 2 b - 7 of a digit b.
   function Digit_Element (B : Natural) return P256_Field.Element is
     (P256_Field.Sub (P256_Field.Of_Natural (2 * B),
                      P256_Field.Of_Natural (7)))
   with Global => null, Pre => B <= 7;

   --  The witness of the signature (R, S) on the digest E under the
   --  key Pk, S below q, written at W (First .. First + Count - 1); the
   --  rest of W is unchanged.
   procedure Push_Legacy
     (Pk    : P256_Curve.Affine_Point;
      E, R, S : Nat_256;
      W     : in out SAP.Element_Array;
      First : Natural)
   with
     Global => null,
     Pre    => Q256_Field.Is_Canonical (To_Q (S))
       and then First >= W'First
       and then First <= Natural'Last - Count
       and then First + Count - 1 <= W'Last,
     Post   => (for all J in W'Range =>
                  (if J < First or else J > First + Count - 1
                   then W (J) = W'Old (J)));

end Ecdsa_Witness;
