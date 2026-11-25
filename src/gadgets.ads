pragma SPARK_Mode (On);

--  Gadgets: the model of the gadgets of upstream's SHA-256 circuit over
--  GF(2^128) (ADR 0091, piece 2; chapter 10, Section 2). The children
--  state what each gadget asserts and what follows when the assertions
--  hold:
--
--    Gadgets.Bits   : G1, the plucker that unpacks a field element into
--                     four bits (lib/circuits/logic/bit_plucker.h);
--    Gadgets.Words  : G3, words of 32 bits as powers of x and the
--                     assertion assert_eqmod (lib/circuits/logic/
--                     bit_adder.h);
--    Gadgets.Sha256 : G4, the assertions of one block of the compression
--                     (lib/circuits/sha/flatsha256_circuit.h).
--
--  This unit holds the vocabulary they share: a word as the 32 field
--  elements of its bits, bit 0 the least significant, and its value.
--  A bit of the circuit is a field element that is 0 or 1 (Is_Bit);
--  nothing in the types forces it, since the circuit's wires are field
--  elements and the gadgets' assertions are what make them bits.
--
--  Proved (Gold): Lemma_Value_Bits_Of and Lemma_Bits_Of_Value, the value
--  of a word and its bits are inverse; Lemma_Value_Ext, Lemma_Mul_Cong
--  and Lemma_Mul_Zero, the laws of the equality of elements and of the
--  product that the proofs of the gadgets use. Trusted: nothing beyond the proof
--  tools.
--
--  Linked into the library archive with every unit of src/, and named
--  by no unit of the library. The gadgets are public data: nothing here
--  follows the constant-time discipline, and the library never calls it
--  on secrets.

with Interfaces; use Interfaces;
with GF2_128;
with Proof_Levels;

package Gadgets is

   subtype Element is GF2_128.Element;

   use type GF2_128.Element;

   --  The element x, the polynomial of degree 1 (the number 2 in the
   --  coordinates of GF2_128: bit I is the coefficient of x^I).
   X : constant Element := (Limbs => [0 => 2, 1 => 0]);

   --  A bit of the circuit: the field element 0 or 1.
   function Is_Bit (V : Element) return Boolean is
     (V = GF2_128.Zero or else V = GF2_128.One);

   subtype Bit_Index is Natural range 0 .. 31;
   subtype Bit_Count is Natural range 0 .. 32;

   --  A word of 32 bits, bit 0 the least significant.
   type Word_Bits is array (Bit_Index) of Element;

   function All_Bits (W : Word_Bits) return Boolean is
     (for all I in Bit_Index => Is_Bit (W (I)));

   --  2^N, for N up to 32.
   function Pow2 (N : Bit_Count) return Unsigned_64 is (Shift_Left (1, N));

   --  The value of the first N bits: the sum of 2^I over the bits I that
   --  are 1. A bit that is not 1 counts as 0.
   function Value_Upto (W : Word_Bits; N : Bit_Count) return Unsigned_64 is
     (if N = 0 then 0
      else Value_Upto (W, N - 1)
           + (if W (N - 1) = GF2_128.One then Pow2 (N - 1) else 0))
   with
     Post               => Value_Upto'Result < Pow2 (N),
     Subprogram_Variant => (Decreases => N);

   --  The value of a word.
   function Value (W : Word_Bits) return Unsigned_64 is (Value_Upto (W, 32))
   with Post => Value'Result < 2 ** 32;

   function Word_Value (W : Word_Bits) return Unsigned_32 is
     (Unsigned_32 (Value (W)));

   --  The bits of a word as field elements.
   function Bits_Of (V : Unsigned_32) return Word_Bits is
     [for I in Bit_Index =>
        (if (Shift_Right (V, I) and 1) = 1 then GF2_128.One
         else GF2_128.Zero)];

   procedure Lemma_Value_Bits_Of (V : Unsigned_32) with
     Ghost,
     Global => null,
     Post   => Word_Value (Bits_Of (V)) = V and then All_Bits (Bits_Of (V));

   procedure Lemma_Bits_Of_Value (W : Word_Bits) with
     Ghost,
     Global => null,
     Pre    => All_Bits (W),
     Post   => Bits_Of (Word_Value (W)) = W;

   --  The equality of elements is that of their limbs, not the identity
   --  of the solvers' logic: these lemmas carry it through the value of
   --  a word and through the product.
   procedure Lemma_Value_Ext (A, B : Word_Bits) with
     Ghost,
     Global => null,
     Pre    => (for all I in Bit_Index => A (I) = B (I)),
     Post   =>
       Word_Value (A) = Word_Value (B) and then All_Bits (A) = All_Bits (B);

   procedure Lemma_Mul_Cong (A1, A2, B1, B2 : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => A1 = A2 and then B1 = B2,
     Post   => GF2_128.Mul (A1, B1) = GF2_128.Mul (A2, B2);

   procedure Lemma_Mul_Zero (A : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => GF2_128.Mul (A, GF2_128.Zero) = GF2_128.Zero;

end Gadgets;
