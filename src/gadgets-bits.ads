pragma SPARK_Mode (On);

--  Gadgets.Bits: G1, the unpacking of a field element into four bits
--  (ADR 0091, piece 2; chapter 10, Section 2), the model of upstream's
--  BitPlucker<Logic, 4> (lib/circuits/logic/bit_plucker.h at 0d92f80c,
--  lines 125 to 168).
--
--  The witness of the SHA-256 circuit holds each word of 32 bits as 8
--  field elements, 4 bits each (the packed form). The plucker reads an
--  element e through four polynomials p_0 .. p_3 of degree 15: bit K of
--  e is p_K (e) = the sum over J of C (K, J) e^J, and the circuit
--  asserts p_K (e) - p_K (e)^2 = 0 for each of the four. Bit 4 I + K of
--  the word is p_K of element I. The coefficients are those of the
--  polynomial with p_K (P_I) = bit K of I at the 16 points
--  P_I = Inject ((2 I) xor 15) (bit_plucker_constants.h): Interpolate
--  computes them.
--
--  The soundness of the circuit rests only on the assertions: whatever
--  element the witness holds, the four outputs are bits (Lemma_Unpack).
--  It does not rest on the coefficients, which are a parameter C of
--  every statement here. That an honest witness decodes to the word it
--  was packed from is completeness: the interpolation, tested.
--
--  A fact of the coefficients the checker of the hash circuit needs:
--  the constant term C (K, 0) of each of the four polynomials is neither
--  0 nor 1. The element 0 then decodes to no bits, so the circuit
--  refuses a count of blocks outside 1 to 40, for which the mux of
--  assert_hash gives 0 (chapter 10, Section 1.4). Tested both ways: on
--  Interpolate's coefficients, and on the registered circuit.
--
--  Proved (Gold over Lean lemmas): Lemma_Output_Is_Bit, an output whose
--  assertion holds is 0 or 1. GNATprove takes it from its contract: its
--  body is null and outside SPARK. It is the Lean theorem
--  LongfellowSpark.Model.output_is_bit (lean/LongfellowSpark/Model.lean),
--  its hypothesis the precondition here; the definitions are the same
--  by reading (register row L3). Lemma_Unpack follows from it by proof.
--  Silver: Interpolate. Tested (gadgets_kat): the interpolation at the
--  64 points, the constant terms, and the bridged statement itself on
--  every element tried.
--
--  Linked into the library archive with every unit of src/, and named
--  by no unit of the library. Public data only, as for Gadgets.

package Gadgets.Bits is

   use GF2_128;

   subtype Nibble is Natural range 0 .. 15;
   subtype Pluck_Index is Natural range 0 .. 3;
   subtype Power_Index is Natural range 0 .. 15;
   subtype Power_Count is Natural range 0 .. 16;

   --  The point of nibble I: Inject ((2 I) xor 15).
   function Point (I : Nibble) return Element is
     (Inject (Subfield_Value (Unsigned_32 (2 * I) xor 15)));

   --  The coefficients of the four plucking polynomials, C (K, J) the
   --  coefficient of e^J in p_K.
   type Coefficients is array (Pluck_Index, Power_Index) of Element;

   --  e^J, one factor at a time.
   function Power (E : Element; J : Power_Index) return Element is
     (if J = 0 then One else Mul (Power (E, J - 1), E))
   with Subprogram_Variant => (Decreases => J);

   function Pluck_Upto
     (C : Coefficients; K : Pluck_Index; E : Element; N : Power_Count)
      return Element
   is (if N = 0 then Zero
       else Add (Pluck_Upto (C, K, E, N - 1), Mul (C (K, N - 1), Power (E, N - 1))))
   with Subprogram_Variant => (Decreases => N);

   --  p_K (E).
   function Pluck
     (C : Coefficients; K : Pluck_Index; E : Element) return Element
   is (Pluck_Upto (C, K, E, 16));

   --  The circuit's assertion on an output V: V - V * V, which it
   --  asserts to be zero (assert_is_bit, logic.h 249 to 252). In
   --  characteristic 2 the difference is the sum.
   function Bit_Assertion (V : Element) return Element is
     (Add (V, Mul (V, V)));

   --  G1, bridged from Lean (LongfellowSpark.Model.output_is_bit): an
   --  output whose assertion holds is 0 or 1. The theorem's hypotheses:
   --  V is below 2^128 (every Element) and the assertion holds.
   procedure Lemma_Output_Is_Bit (V : Element) with
     Ghost,
     Global => null,
     Pre    => Bit_Assertion (V) = Zero,
     Post   => Is_Bit (V);

   --  A word in the packed form: element I holds bits 4 I to 4 I + 3.
   subtype Packed_Index is Natural range 0 .. 7;
   type Packed_Word is array (Packed_Index) of Element;

   --  The 32 outputs of the plucker on a packed word.
   function Unpack (C : Coefficients; P : Packed_Word) return Word_Bits is
     [for J in Bit_Index => Pluck (C, J mod 4, P (J / 4))];

   --  Every assertion of the plucker on the word holds.
   function Plucks_Hold (C : Coefficients; P : Packed_Word) return Boolean is
     (for all J in Bit_Index => Bit_Assertion (Unpack (C, P) (J)) = Zero);

   --  The decoding of a packed word: the value of its 32 outputs. It is
   --  defined for every element, and is the one decoding of the packed
   --  words in this project.
   function Decode (C : Coefficients; P : Packed_Word) return Unsigned_32 is
     (Word_Value (Unpack (C, P)));

   --  When the plucker's assertions on a word hold, its outputs are bits.
   procedure Lemma_Unpack (C : Coefficients; P : Packed_Word) with
     Ghost,
     Global => null,
     Pre    => Plucks_Hold (C, P),
     Post   => All_Bits (Unpack (C, P));

   --  The coefficients of the polynomials with p_K (Point (I)) = bit K
   --  of I, by Lagrange interpolation (upstream's monomial_of_lagrange).
   function Interpolate return Coefficients;

end Gadgets.Bits;
