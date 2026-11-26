pragma SPARK_Mode (On);

--  Gadgets.Words: G3, words of 32 bits in the multiplicative group of
--  GF(2^128) (ADR 0091, piece 2; chapter 10, Section 2), the model of
--  upstream's BitAdderAux for a field of characteristic 2
--  (lib/circuits/logic/bit_adder.h at 0d92f80c, lines 83 to 147).
--
--  A word of 32 bits b_0 .. b_31 is the element
--    Encode (W) = the product over I of (1 + b_I (x^(2^I) + 1)),
--  which for bits is x raised to the value of the word. A sum of words
--  is a product of their elements. assert_eqmod (a, b, k), with b the
--  product of the elements of k words, asserts that the product over
--  I < k of (b - x^(I 2^32) Encode (a)) is zero (Assertion). The
--  constants are built as the generator builds them: Alpha_2 (I) is x
--  squared I times, Shift (I) is Alpha_2 (32) multiplied in I times;
--  every product is taken one factor at a time.
--
--  Proved (Gold over Lean lemmas): Lemma_Assert_Eqmod, for 1 to 7 words
--  whose bits are 0 or 1 and a word a whose bits are 0 or 1, the
--  assertion holds exactly when the sum of the words modulo 2^32 is the
--  value of a. GNATprove takes it from its contract: its body is null
--  and outside SPARK. It is the Lean theorem
--  LongfellowSpark.Model.assert_eqmod (lean/LongfellowSpark/Model.lean),
--  with every hypothesis of the theorem a precondition here, and it
--  rests on the order of x in the field, 2^128 - 1
--  (LongfellowSpark.GF128.alpha_order), proved in Lean by computation
--  in the kernel. That the definitions here and those of the Lean model
--  are the same is checked by reading (the correspondence page of the
--  guide, register row L4) and by the vectors of tests/vectors/
--  lean_gf2_128.txt. Tested (gadgets_kat): the statement itself, both
--  ways, on random and adversarial words.
--
--  Linked into the library archive with every unit of src/, and named
--  by no unit of the library. Public data only, as for Gadgets.

package Gadgets.Words is

   use GF2_128;

   --  x squared I times: x^(2^I).
   function Alpha_2 (I : Bit_Count) return Element is
     (if I = 0 then X
      else (declare
              P : constant Element := Alpha_2 (I - 1);
            begin
              Mul (P, P)))
   with Subprogram_Variant => (Decreases => I);

   Max_Terms : constant := 7;
   subtype Term_Count is Positive range 1 .. Max_Terms;
   subtype Term_Index is Natural range 0 .. Max_Terms - 1;
   subtype Term_Upto is Natural range 0 .. Max_Terms;

   --  Alpha_2 (32) multiplied in I times: x^(I 2^32).
   function Shift (I : Term_Index) return Element is
     (if I = 0 then One else Mul (Alpha_2 (32), Shift (I - 1)))
   with Subprogram_Variant => (Decreases => I);

   --  The factor of bit I: the gadget's mux (B, x^(2^I), 1).
   function Factor (I : Bit_Index; B : Element) return Element is
     (Add (One, Mul (B, Add (Alpha_2 (I), One))));

   --  The element of the first N bits of a word, and of the word.
   function Encode_Upto (W : Word_Bits; N : Bit_Count) return Element is
     (if N = 0 then One
      else Mul (Encode_Upto (W, N - 1), Factor (N - 1, W (N - 1))))
   with Subprogram_Variant => (Decreases => N);

   function Encode (W : Word_Bits) return Element is (Encode_Upto (W, 32));

   --  The words of one assertion; only the first K count.
   type Word_List is array (Term_Index) of Word_Bits;

   function All_Bits (L : Word_List; K : Term_Count) return Boolean is
     (for all J in 0 .. K - 1 => All_Bits (L (J)));

   --  The product of the elements of the first N words: their sum.
   function Product_Upto (L : Word_List; N : Term_Upto) return Element is
     (if N = 0 then One else Mul (Product_Upto (L, N - 1), Encode (L (N - 1))))
   with Subprogram_Variant => (Decreases => N);

   --  The factor I of assert_eqmod (A, the sum of the K words, K).
   function Difference
     (L : Word_List; K : Term_Count; A : Word_Bits; I : Term_Index)
      return Element
   is (Add (Product_Upto (L, K), Mul (Shift (I), Encode (A))));

   function Assertion_Upto
     (L : Word_List; K : Term_Count; A : Word_Bits; N : Term_Upto)
      return Element
   is (if N = 0 then One
       else Mul (Assertion_Upto (L, K, A, N - 1), Difference (L, K, A, N - 1)))
   with Subprogram_Variant => (Decreases => N);

   --  The element assert_eqmod (A, the sum of the K words, K) asserts to
   --  be zero.
   function Assertion
     (L : Word_List; K : Term_Count; A : Word_Bits) return Element
   is (Assertion_Upto (L, K, A, K));

   --  The sum of the values of the first N words. It is below 7 2^32,
   --  so it never wraps; and it is only read modulo 2^32, which divides
   --  2^64, so the statement below would hold even if it did.
   function Sum_Upto (L : Word_List; N : Term_Upto) return Unsigned_64 is
     (if N = 0 then 0 else Sum_Upto (L, N - 1) + Value (L (N - 1)))
   with Subprogram_Variant => (Decreases => N);

   --  G3, bridged from Lean (LongfellowSpark.Model.assert_eqmod): for
   --  1 to 7 words of bits and a word A of bits, the assertion holds
   --  exactly when the sum of the words modulo 2^32 is the value of A.
   --  The theorem's hypotheses: 0 < K and K <= 7 (Term_Count), the bits
   --  of the K words and of A are 0 or 1 (the precondition).
   procedure Lemma_Assert_Eqmod (L : Word_List; K : Term_Count; A : Word_Bits)
   with
     Ghost,
     Global => null,
     Pre    => All_Bits (L, K) and then All_Bits (A),
     Post   =>
       (Assertion (L, K, A) = Zero) = (Sum_Upto (L, K) mod 2 ** 32 = Value (A));

end Gadgets.Words;
