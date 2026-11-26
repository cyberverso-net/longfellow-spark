/-
The two statements the SPARK units cite, over the model of the field over
`Nat` of `LongfellowSpark.GF128`: an element is a number below `2 ^ 128`
(bit i is the coefficient of x ^ i), addition is `^^^` and the product is
`GF128.mul`. That model and `GF2_128.Mul_Ref` are both bit-level definitions
of the product of GF(2)[x] / (x ^ 128 + x ^ 7 + x ^ 2 + x + 1); the
correspondence page of the guide compares them line by line, and the vectors
of `lean/scripts/Vectors.lean` are checked against `GF2_128.Mul` by the tests.

The constants are built as upstream builds them (`bit_adder.h` at 0d92f80c,
lines 90 to 98 and 120 to 124): `alpha2 i` is x squared i times, `shift i` is
`alpha2 32` multiplied in i times. Products are taken in a row, one factor at
a time (`prodN`).

- `output_is_bit` (G1, cited by `Gadgets.Bits`): the plucker's assertion
  `v - v * v = 0` holds only for 0 and 1.
- `assert_eqmod` (G3, cited by `Gadgets.Words`): for k from 1 to 7 words of
  32 bits, the circuit's product of the k differences is zero if and only if
  the sum of the words, modulo 2 ^ 32, is the word `a`.

Both are proved by carrying the model into `AdjoinRoot P` with `GF128.ev`, an
injective homomorphism below 2 ^ 128, and applying `Plucker.output_is_bit` and
`GF128.assert_eqmod_words_gf128` there.
-/
import LongfellowSpark.GF128
import LongfellowSpark.Plucker

namespace LongfellowSpark.Model

open Finset GF128

/-! ## 1. The definitions -/

/-- x squared `n` times: x ^ (2 ^ n). -/
def alpha2 : ℕ → ℕ
  | 0 => 2
  | n + 1 => mul (alpha2 n) (alpha2 n)

/-- `alpha2 32` multiplied in `n` times: x ^ (n 2 ^ 32). -/
def shift : ℕ → ℕ
  | 0 => 1
  | n + 1 => mul (alpha2 32) (shift n)

/-- The product of `f 0`, ..., `f (n - 1)`, one factor at a time. -/
def prodN : ℕ → (ℕ → ℕ) → ℕ
  | 0, _ => 1
  | n + 1, f => mul (prodN n f) (f n)

/-- The factor of bit `i`: `1 + b (x ^ (2 ^ i) - 1)`, the gadget's mux. -/
def factor (i b : ℕ) : ℕ := 1 ^^^ mul b (alpha2 i ^^^ 1)

/-- The element of a word of 32 bits. -/
def encode (bits : ℕ → ℕ) : ℕ := prodN 32 (fun i => factor i (bits i))

/-- The value of a word of 32 bits. -/
def value (bits : ℕ → ℕ) : ℕ := ∑ i ∈ range 32, if bits i = 1 then 2 ^ i else 0

/-- The sum of the values of the words 0 to k - 1. -/
def sumN (k : ℕ) (words : ℕ → ℕ → ℕ) : ℕ := ∑ j ∈ range k, value (words j)

/-- `assert_eqmod (a, b, k)` with b the product of the k words' elements:
the product over i < k of `b - x ^ (i 2 ^ 32) * aa`. -/
def assertion (k : ℕ) (words : ℕ → ℕ → ℕ) (abits : ℕ → ℕ) : ℕ :=
  prodN k (fun i => prodN k (fun j => encode (words j)) ^^^ mul (shift i) (encode abits))

/-! ## 2. Bounds and evaluation -/

theorem xor_lt {a b : ℕ} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128) : a ^^^ b < 2 ^ 128 :=
  Nat.xor_lt_two_pow ha hb

theorem alpha2_lt : ∀ n, alpha2 n < 2 ^ 128
  | 0 => by norm_num [alpha2]
  | n + 1 => by rw [alpha2]; exact mul_lt _ _ (alpha2_lt n)

theorem shift_lt : ∀ n, shift n < 2 ^ 128
  | 0 => by norm_num [shift]
  | n + 1 => by rw [shift]; exact mul_lt _ _ (alpha2_lt 32)

theorem prodN_lt : ∀ n f, prodN n f < 2 ^ 128
  | 0, _ => by norm_num [prodN]
  | n + 1, f => by rw [prodN]; exact mul_lt _ _ (prodN_lt n f)

theorem encode_lt (bits : ℕ → ℕ) : encode bits < 2 ^ 128 := prodN_lt _ _

theorem ev_alpha2 : ∀ n, ev (alpha2 n) = AdjoinRoot.root P ^ (2 ^ n)
  | 0 => by simp [alpha2, ev_two]
  | n + 1 => by
    rw [alpha2, ev_mul _ _ (alpha2_lt n), ev_alpha2 n, ← pow_add]
    congr 1; ring

theorem ev_shift : ∀ n, ev (shift n) = AdjoinRoot.root P ^ (n * 2 ^ 32)
  | 0 => by simp [shift, ev_one]
  | n + 1 => by
    rw [shift, ev_mul _ _ (shift_lt n), ev_alpha2, ev_shift n, ← pow_add]
    congr 1; ring

theorem ev_prodN (f : ℕ → ℕ) : ∀ n, (∀ i < n, f i < 2 ^ 128) →
    ev (prodN n f) = ∏ i ∈ range n, ev (f i)
  | 0, _ => by simp [prodN, ev_one]
  | n + 1, hf => by
    rw [prodN, ev_mul _ _ (hf n (by omega)), ev_prodN f n (fun i hi => hf i (by omega)),
      prod_range_succ]

/-- Characteristic 2: `2 = 0` in `AdjoinRoot P`. -/
theorem two_eq_zero_R : (2 : R) = 0 := by
  have h : (2 : ZMod 2) = 0 := by decide
  have := congrArg (AdjoinRoot.of P) h
  rwa [map_ofNat, map_zero] at this

theorem sub_eq_add_R (a b : R) : a - b = a + b := by
  have hb : b + b = 0 := by rw [← two_mul, two_eq_zero_R, zero_mul]
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left hb]

/-! ## 3. G1: the outputs of the plucker are bits -/

/-- The plucker's assertion `v - v * v = 0`, in the model `v ^^^ mul v v = 0`,
holds only for `v = 0` and `v = 1`. -/
theorem output_is_bit (v : ℕ) (hv : v < 2 ^ 128) (h : v ^^^ mul v v = 0) :
    v = 0 ∨ v = 1 := by
  have hc : ev v - ev v ^ 2 = 0 := by
    rw [sub_eq_add_R, sq, ← ev_mul _ _ hv, ← ev_xor, h, ev_zero]
  letI := field
  rcases Plucker.output_is_bit (ev v) hc with h0 | h1
  · exact Or.inl (ev_inj hv (by norm_num) (h0.trans ev_zero.symm))
  · exact Or.inr (ev_inj hv (by norm_num) (h1.trans ev_one.symm))

/-! ## 4. G3: words in the multiplicative group -/

/-- `assert_eqmod` in the model: for 1 to 7 words whose 32 bits are 0 or 1,
and a word `a` whose 32 bits are 0 or 1, the circuit's product is zero if and
only if the sum of the words modulo 2 ^ 32 is the value of `a`. -/
theorem assert_eqmod (k : ℕ) (hk : 0 < k) (hk7 : k ≤ 7)
    (words : ℕ → ℕ → ℕ) (hw : ∀ j < k, ∀ i < 32, words j i = 0 ∨ words j i = 1)
    (abits : ℕ → ℕ) (ha : ∀ i < 32, abits i = 0 ∨ abits i = 1) :
    assertion k words abits = 0 ↔ sumN k words % 2 ^ 32 = value abits := by
  have hz : assertion k words abits = 0 ↔ ev (assertion k words abits) = 0 :=
    ⟨fun h => by rw [h, ev_zero],
     fun h => ev_inj (prodN_lt _ _) (by norm_num) (h.trans ev_zero.symm)⟩
  rw [hz]
  letI := field
  letI : DecidableEq R := Classical.decEq _
  have ev_mul' : ∀ a b, b < 2 ^ 128 → ev (mul a b) = ev a * ev b :=
    fun a b hb => ev_mul a b hb
  have ev_xor' : ∀ a b, ev (a ^^^ b) = ev a + ev b := fun a b => ev_xor a b
  have sub' : ∀ a b : R, a - b = a + b := fun a b => sub_eq_add_R a b
  have ev_one' : ev 1 = 1 := ev_one
  have ev_zero' : ev 0 = 0 := ev_zero
  have zero_ne_one' : (0 : R) ≠ 1 := zero_ne_one_R
  have ev_alpha2' : ∀ n, ev (alpha2 n) = AdjoinRoot.root P ^ (2 ^ n) := ev_alpha2
  have ev_shift' : ∀ n, ev (shift n) = AdjoinRoot.root P ^ (n * 2 ^ 32) := ev_shift
  have ev_prodN' : ∀ (f : ℕ → ℕ) n, (∀ i < n, f i < 2 ^ 128) →
      ev (prodN n f) = ∏ i ∈ range n, ev (f i) := ev_prodN
  have bit' : ∀ b : ℕ, (b = 0 ∨ b = 1) → (ev b = 0 ∨ ev b = 1) := by
    rintro b (h | h) <;> simp [h, ev_zero', ev_one']
  -- The words and `a` in `AdjoinRoot P`, extended by 0 above bit 31.
  have hWbit : ∀ (j : Fin k) i,
      BitAdder.IsBit (if i < 32 then ev (words j i) else (0 : R)) := by
    intro j i
    by_cases hi : i < 32
    · rw [if_pos hi]; exact bit' _ (hw j j.isLt i hi)
    · rw [if_neg hi]; exact Or.inl rfl
  have hAbit : ∀ i, BitAdder.IsBit (if i < 32 then ev (abits i) else (0 : R)) := by
    intro i
    by_cases hi : i < 32
    · rw [if_pos hi]; exact bit' _ (ha i hi)
    · rw [if_neg hi]; exact Or.inl rfl
  have key := assert_eqmod_words_gf128 k hk hk7
    (fun i => if i < 32 then ev (abits i) else 0) hAbit
    (fun (j : Fin k) i => if i < 32 then ev (words j i) else 0) hWbit
  -- The element of a word in the model is the element of the gadget's lemma.
  have henc : ∀ bits : ℕ → ℕ, (∀ i < 32, bits i < 2 ^ 128) →
      ev (encode bits) = BitAdder.encode (AdjoinRoot.root P) 32
        (fun i => if i < 32 then ev (bits i) else 0) := by
    intro bits hb
    unfold encode BitAdder.encode
    rw [ev_prodN' (fun i => factor i (bits i)) 32
      (fun i hi => xor_lt (by norm_num) (mul_lt _ _ (hb i hi)))]
    refine prod_congr rfl (fun i hi => ?_)
    have hi' : i < 32 := mem_range.mp hi
    simp only [if_pos hi']
    unfold factor BitAdder.factor
    rw [ev_xor', ev_one', ev_mul' _ _ (xor_lt (alpha2_lt i) (by norm_num)), ev_xor',
      ev_alpha2', ev_one', sub']
  have lt_of_bit : ∀ b : ℕ, (b = 0 ∨ b = 1) → b < 2 ^ 128 := by
    rintro b (h | h) <;> simp [h]
  have hL : ev (assertion k words abits) =
      ∏ i ∈ range k, ((∏ j : Fin k, BitAdder.encode (AdjoinRoot.root P) 32
          (fun i => if i < 32 then ev (words j i) else 0))
        - AdjoinRoot.root P ^ (i * 2 ^ 32) * BitAdder.encode (AdjoinRoot.root P) 32
          (fun i => if i < 32 then ev (abits i) else 0)) := by
    unfold assertion
    rw [ev_prodN'
      (fun i => prodN k (fun j => encode (words j)) ^^^ mul (shift i) (encode abits)) k
      (fun i _ => xor_lt (prodN_lt _ _) (mul_lt _ _ (shift_lt i)))]
    refine prod_congr rfl (fun i _ => ?_)
    rw [ev_xor', ev_mul' (shift i) (encode abits) (encode_lt abits), ev_shift', sub',
      ev_prodN' (fun j => encode (words j)) k (fun j _ => encode_lt (words j)),
      Fin.prod_univ_eq_prod_range (fun j => BitAdder.encode (AdjoinRoot.root P) 32
        (fun i => if i < 32 then ev (words j i) else 0)) k,
      henc abits (fun i hi => lt_of_bit _ (ha i hi)),
      prod_congr rfl (fun j hj =>
        henc (words j) (fun i hi => lt_of_bit _ (hw j (mem_range.mp hj) i hi)))]
  -- The value of a word in the model is the value of the gadget's lemma.
  have hval : ∀ bits : ℕ → ℕ, (∀ i < 32, bits i = 0 ∨ bits i = 1) →
      BitAdder.value 32 (fun i => if i < 32 then ev (bits i) else 0) = value bits := by
    intro bits hb
    unfold BitAdder.value value
    refine sum_congr rfl (fun i hi => ?_)
    have hi' : i < 32 := mem_range.mp hi
    rcases hb i hi' with h | h <;> simp [hi', h, ev_zero', ev_one', zero_ne_one']
  rw [hL]
  refine key.trans ?_
  rw [Fin.sum_univ_eq_sum_range (fun j => BitAdder.value 32
      (fun i => if i < 32 then ev (words j i) else 0)) k, hval abits ha]
  unfold sumN
  rw [sum_congr rfl (fun j hj => hval (words j) (hw j (mem_range.mp hj)))]

end LongfellowSpark.Model
