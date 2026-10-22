--  Clmul64: the carry-less product of two 64-bit words (Phase D,
--  milestone M2, ADR 0065), as clmul64 of upstream's generic.rs
--  computes it (rust/runtime/algebra/src/arch/generic.rs at d5e6be7),
--  with no special instruction.
--
--  The low word, Clmul_Lo, splits each operand into four classes of bit
--  positions (one bit in four) and adds up sixteen integer products of
--  masked words: in each product the carries land in the bits of other
--  classes, which the masks clear, or above bit 63. The high word,
--  Clmul_Hi, is the low word of the bit-reversed operands, reversed and
--  shifted right by one.
--
--  Documentation: docs/guide/01-gf2_128.md.
--
--  Clmul_Kara makes the three products of one Karatsuba step and shares
--  the reversals among them; GF2_128.Mul calls it.
--
--  Proof status: Gold. Clmul_Lo equals Lo_Ref (X, Y, 64) and Clmul_Hi
--  equals Hi_Ref (X, Y, 64) for all operands, and Clmul_Kara gives the
--  same words. Lo_Ref and Hi_Ref are the
--  two words of the carry-less product, written as xors of shifts over
--  the bits of Y. The proof of Clmul_Lo reads each integer product as
--  a number in base 16 whose digits are sums of 0 and 1, and shows that
--  no digit below the top one reaches 16 (the lemmas of the body).
--  The lemmas below are the ones GF2_128 uses to prove Mul.
--
--  Constant-time discipline (ADR 0006): no branch and no memory access
--  depend on the operands. The integer multiplications assume that the
--  processor's multiplier takes a time independent of its operands
--  (ADR 0065), as upstream does.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Proof_Levels;

package Clmul64 is

   subtype U64 is Unsigned_64;

   --  The low word of the carry-less product of X by the bits of Y
   --  below N: bit J of Y contributes X shifted left by J.
   function Lo_Ref (X, Y : U64; N : Natural) return U64 is
     (if N = 0 then 0
      elsif (Shift_Right (Y, N - 1) and 1) = 1
      then Lo_Ref (X, Y, N - 1) xor Shift_Left (X, N - 1)
      else Lo_Ref (X, Y, N - 1))
   with Ghost => Proof_Only,
        Global => null,
        Pre => N <= 64,
        Subprogram_Variant => (Decreases => N);

   --  The high word of the carry-less product of X by the top N bits of
   --  Y: bit 64 - N of Y contributes X shifted right by N (nothing for
   --  bit 0, which lands entirely in the low word).
   function Hi_Ref (X, Y : U64; N : Natural) return U64 is
     (if N = 0 then 0
      elsif (Shift_Right (Y, 64 - N) and 1) = 1
      then Hi_Ref (X, Y, N - 1) xor Shift_Right (X, N)
      else Hi_Ref (X, Y, N - 1))
   with Ghost => Proof_Only,
        Global => null,
        Pre => N <= 64,
        Subprogram_Variant => (Decreases => N);

   --  clmul64_lo: the low word of the carry-less product.
   function Clmul_Lo (X, Y : U64) return U64 with
     Inline,
     Global => null,
     Post   => (Proof_Only => Clmul_Lo'Result = Lo_Ref (X, Y, 64));

   --  clmul64_hi: the high word of the carry-less product.
   function Clmul_Hi (X, Y : U64) return U64 with
     Global => null,
     Post   => (Proof_Only => Clmul_Hi'Result = Hi_Ref (X, Y, 64));

   --  The three products of one Karatsuba step, as GF2_128.Mul uses
   --  them: A0 by B0 in L0 and H0, A1 by B1 in L2 and H2, and in L1
   --  and H1 the product of A0 xor A1 by B0 xor B1 with the other two
   --  added. Each operand is reversed once, the middle product reuses
   --  those reversals and its high word takes one reversal after the
   --  sum, so the high words cost seven reversals where three calls of
   --  Clmul_Hi cost nine.
   procedure Clmul_Kara
     (A0, A1, B0, B1 : U64;
      L0, H0, L1, H1, L2, H2 : out U64)
   with
     Global => null,
     Post   =>
       (Proof_Only =>
          L0 = Lo_Ref (A0, B0, 64)
          and then H0 = Hi_Ref (A0, B0, 64)
          and then L2 = Lo_Ref (A1, B1, 64)
          and then H2 = Hi_Ref (A1, B1, 64)
          and then L1 = (Lo_Ref (A0 xor A1, B0 xor B1, 64) xor L0 xor L2)
          and then H1 = (Hi_Ref (A0 xor A1, B0 xor B1, 64) xor H0 xor H2));

   -------------------------------------------------------------------
   --  The lemmas GF2_128 uses: linearity in each operand, the product
   --  by one bit, the product by zero.
   -------------------------------------------------------------------

   procedure Lemma_Lo_Lin_X (X1, X2, Y : U64; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N <= 64,
     Post   => Lo_Ref (X1 xor X2, Y, N)
               = (Lo_Ref (X1, Y, N) xor Lo_Ref (X2, Y, N)),
     Subprogram_Variant => (Decreases => N);

   procedure Lemma_Lo_Lin_Y (X, Y1, Y2 : U64; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N <= 64,
     Post   => Lo_Ref (X, Y1 xor Y2, N)
               = (Lo_Ref (X, Y1, N) xor Lo_Ref (X, Y2, N)),
     Subprogram_Variant => (Decreases => N);

   procedure Lemma_Hi_Lin_X (X1, X2, Y : U64; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N <= 64,
     Post   => Hi_Ref (X1 xor X2, Y, N)
               = (Hi_Ref (X1, Y, N) xor Hi_Ref (X2, Y, N)),
     Subprogram_Variant => (Decreases => N);

   procedure Lemma_Hi_Lin_Y (X, Y1, Y2 : U64; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N <= 64,
     Post   => Hi_Ref (X, Y1 xor Y2, N)
               = (Hi_Ref (X, Y1, N) xor Hi_Ref (X, Y2, N)),
     Subprogram_Variant => (Decreases => N);

   procedure Lemma_Lo_Bit (X : U64; K, N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => K < 64 and then N <= 64,
     Post   => Lo_Ref (X, Shift_Left (1, K), N)
               = (if N <= K then 0 else Shift_Left (X, K)),
     Subprogram_Variant => (Decreases => N);

   procedure Lemma_Hi_Bit (X : U64; K, N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => K < 64 and then N <= 64,
     Post   => Hi_Ref (X, Shift_Left (1, K), N)
               = (if N < 64 - K then 0 else Shift_Right (X, 64 - K)),
     Subprogram_Variant => (Decreases => N);

   procedure Lemma_By_Zero (X : U64; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N <= 64,
     Post   => Lo_Ref (X, 0, N) = 0 and then Hi_Ref (X, 0, N) = 0,
     Subprogram_Variant => (Decreases => N);

end Clmul64;
