/-
G3 of ADR 0091, words in the multiplicative group: the semantics of
upstream's `BitAdderAux` over a field of characteristic 2
(`lib/circuits/logic/bit_adder.h` at 0d92f80c, lines 83 to 147). First
written for the feasibility study of the milestone (#88).

In the multiplicative group of the field, a word `v` of `N` bits is the
element `α ^ v`, built as the product of one factor per bit:
`1 + b_i (α ^ (2 ^ i) - 1)`, which is `α ^ (2 ^ i)` when the bit `b_i` is 1
and `1` when it is 0 (the gadget's `mux (v[i], α^(2^i), 1)`; in characteristic
2 the minus is a plus, as the circuit's terms have it). The sum of words is the
product of their elements. `assert_eqmod (a, b, k)` asserts
`∏_{i < k} (b - α ^ (i 2^N) · aa) = 0`, where `aa` encodes the word `a`.

The theorem: if `α` has no power equal to one below `k 2^N` (an assumption on
the order of `α`, stated as a hypothesis and discharged for the circuit's field
in `LongfellowSpark.GF128`), and the factors encode bits, then the product of
the `k` differences is zero if and only if the sum of the `k` words, modulo
`2^N`, is the word `a`.

Cited by the SPARK unit `Gadgets.Words` (chapter 10, Section 2).
-/
import Mathlib

namespace LongfellowSpark.BitAdder

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- The factor of bit `i` in the circuit's form, `1 + b (α ^ (2 ^ i) - 1)`. -/
def factor (α : F) (i : ℕ) (b : F) : F := 1 + b * (α ^ (2 ^ i) - 1)

/-- A bit as the field holds it: `0` or `1`. -/
def IsBit (b : F) : Prop := b = 0 ∨ b = 1

/-- The value of the word whose bit `i` is `bits i`, `N` bits. -/
noncomputable def value (N : ℕ) (bits : ℕ → F) : ℕ :=
  ∑ i ∈ range N, if bits i = 1 then 2 ^ i else 0

/-- The element of a word: the product of its factors. -/
def encode (α : F) (N : ℕ) (bits : ℕ → F) : F :=
  ∏ i ∈ range N, factor α i (bits i)

lemma factor_of_bit (α : F) (i : ℕ) {b : F} (hb : IsBit b) :
    factor α i b = α ^ (if b = 1 then 2 ^ i else 0) := by
  rcases hb with h | h <;> simp [factor, h]

/-- The factors encode the word: `encode α N bits = α ^ value N bits`. -/
theorem encode_eq_pow (α : F) (N : ℕ) (bits : ℕ → F) (hbits : ∀ i, IsBit (bits i)) :
    encode α N bits = α ^ value N bits := by
  unfold encode value
  induction N with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, sum_range_succ, ih, factor_of_bit α n (hbits n), pow_add]

/-- A word of `N` bits is below `2 ^ N`. -/
theorem value_lt (N : ℕ) (bits : ℕ → F) : value N bits < 2 ^ N := by
  unfold value
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, pow_succ]
    have h2 : 0 < 2 ^ n := by positivity
    split_ifs <;> linarith

omit [DecidableEq F] in
/-- Below the order of `α`, its powers are distinct. -/
theorem pow_inj_of_lt (α : F) (hα0 : α ≠ 0) (M : ℕ)
    (hord : ∀ m, 0 < m → m < M → α ^ m ≠ 1)
    {x y : ℕ} (hx : x < M) (hy : y < M) (h : α ^ x = α ^ y) : x = y := by
  have key : ∀ {x y : ℕ}, x < y → y < M → α ^ x = α ^ y → False := by
    intro x y hxy hy h
    have hsplit : α ^ y = α ^ x * α ^ (y - x) := by
      rw [← pow_add, Nat.add_sub_cancel' hxy.le]
    rw [hsplit] at h
    have hne : α ^ x ≠ 0 := pow_ne_zero _ hα0
    have hone : α ^ (y - x) = 1 :=
      mul_left_cancel₀ hne (h.symm.trans (mul_one (α ^ x)).symm)
    exact hord (y - x) (by omega) (by omega) hone
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact (key hxy hy h).elim
  · exact hxy
  · exact (key hxy hx h.symm).elim

omit [DecidableEq F] in
/-- `assert_eqmod` on the exponents: with `a < 2^N`, `s < k 2^N` and no power
of `α` equal to one below `k 2^N`, the product of the `k` differences
`α^s - α^(i 2^N) α^a` is zero iff `s mod 2^N = a`. -/
theorem eqmod_iff (α : F) (hα0 : α ≠ 0) (N k a s : ℕ)
    (hord : ∀ m, 0 < m → m < k * 2 ^ N → α ^ m ≠ 1)
    (ha : a < 2 ^ N) (hs : s < k * 2 ^ N) :
    (∏ i ∈ range k, (α ^ s - α ^ (i * 2 ^ N) * α ^ a)) = 0 ↔ s % 2 ^ N = a := by
  have hpos : 0 < 2 ^ N := by positivity
  rw [prod_eq_zero_iff]
  constructor
  · rintro ⟨i, hi, h⟩
    rw [mem_range] at hi
    have h' : α ^ s = α ^ (i * 2 ^ N + a) := by
      rw [pow_add]; exact sub_eq_zero.mp h
    have hlt : i * 2 ^ N + a < k * 2 ^ N :=
      calc i * 2 ^ N + a < i * 2 ^ N + 2 ^ N := by omega
        _ = (i + 1) * 2 ^ N := by ring
        _ ≤ k * 2 ^ N := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hi)
    have := pow_inj_of_lt α hα0 (k * 2 ^ N) hord hs hlt h'
    rw [this, Nat.mul_add_mod_of_lt ha]
  · intro h
    refine ⟨s / 2 ^ N, ?_, ?_⟩
    · rw [mem_range]; exact (Nat.div_lt_iff_lt_mul hpos).mpr hs
    · rw [← h, sub_eq_zero, ← pow_add, Nat.div_add_mod']

/-- The lemma of the gadget in the form of F2's: the `k` words are given by
the factors of their bits, `aa` by the factors of the bits of `a`; the circuit's
product of the `k` differences `b - α^(i 2^32) aa`, with `b` the product of the
words' elements, is zero iff the sum of the words modulo `2^32` is `a`. -/
theorem assert_eqmod_words (α : F) (hα0 : α ≠ 0) (k : ℕ) (hk : 0 < k)
    (hord : ∀ m, 0 < m → m < k * 2 ^ 32 → α ^ m ≠ 1)
    (abits : ℕ → F) (ha : ∀ i, IsBit (abits i))
    (words : Fin k → ℕ → F) (hw : ∀ j i, IsBit (words j i)) :
    (∏ i ∈ range k, ((∏ j : Fin k, encode α 32 (words j))
        - α ^ (i * 2 ^ 32) * encode α 32 abits)) = 0
      ↔ (∑ j : Fin k, value 32 (words j)) % 2 ^ 32 = value 32 abits := by
  have hb : (∏ j : Fin k, encode α 32 (words j)) = α ^ (∑ j : Fin k, value 32 (words j)) := by
    rw [prod_congr rfl (fun j _ => encode_eq_pow α 32 (words j) (hw j)),
      prod_pow_eq_pow_sum]
  rw [hb, encode_eq_pow α 32 abits ha]
  refine eqmod_iff α hα0 32 k _ _ hord (value_lt 32 abits) ?_
  have hne : (univ : Finset (Fin k)).Nonempty := univ_nonempty_iff.mpr ⟨⟨0, hk⟩⟩
  calc ∑ j : Fin k, value 32 (words j) < ∑ _j : Fin k, 2 ^ 32 :=
        sum_lt_sum_of_nonempty hne (fun j _ => value_lt 32 (words j))
    _ = k * 2 ^ 32 := by simp

end LongfellowSpark.BitAdder
