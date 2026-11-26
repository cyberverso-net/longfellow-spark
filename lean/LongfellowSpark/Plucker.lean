/-
G1 of ADR 0091, bit unpacking: the outputs of upstream's `BitPlucker` are
bits (`lib/circuits/logic/bit_plucker.h` at 0d92f80c, line 147: each output
v of the plucking polynomials is asserted with `v - v ^ 2`). In any field,
`v - v ^ 2 = 0` holds only for `v = 0` and `v = 1`.

Cited by the SPARK unit `Gadgets.Bits` (chapter 10, Section 2).
-/
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.LinearCombination

namespace LongfellowSpark.Plucker

theorem output_is_bit {F : Type*} [Field F] (v : F) (h : v - v ^ 2 = 0) :
    v = 0 ∨ v = 1 := by
  have h' : v * (1 - v) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1).symm

end LongfellowSpark.Plucker
