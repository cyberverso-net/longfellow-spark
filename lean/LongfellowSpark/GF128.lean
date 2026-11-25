/-
The field of the hash circuit, GF(2^128) = GF(2)[x] / (x^128 + x^7 + x^2 + x + 1),
and the order of x in it (ADR 0091, G3).

Three parts:

1. A computable model over `Nat`: an element is a number below 2^128 whose bit
   i is the coefficient of x^i, as in `GF2_128` of longfellow-spark (bit I of
   the element is the coefficient of x^I, the reduction constant 16#87#). The
   product is the carry-less product followed by two folds of the part above
   degree 127, and the power is square-and-multiply. All recursion is
   structural on a fuel argument, so that the kernel reduces it.
2. The nine checks of the order of x, x^((2^128 - 1) / q) ≠ 1 for the nine
   primes q of 2^128 - 1, and x^(2^128 - 1) = 1, by `decide +kernel` on the
   model: kernel reduction, no `native_decide`.
3. The link to the algebra: `ev` maps the model into `AdjoinRoot P` over
   `ZMod 2`, P = X^128 + X^7 + X^2 + X + 1. It is injective below 2^128 and
   carries the model's xor and product to the ring's sum and product. From the
   checks, x has order 2^128 - 1 among the units of that ring, the ring is a
   field, and the theorem of `BitAdder` applies to it with α = x
   (`assert_eqmod_words_gf128`).

The primality of the nine factors and their product are upstream's
(`Upstream.GeneratorChecks`, ported with its provenance).

Cited by the SPARK unit `Gadgets.Words` (chapter 10, Section 2).
-/
import Mathlib.Data.Nat.Bitwise
import Upstream.GeneratorChecks
import LongfellowSpark.BitAdder

namespace LongfellowSpark.GF128

/-! ## 1. The model over `Nat` -/

/-- Carry-less product: the xor of `a <<< i` over the set bits i of `b`, for
the first `n` bits of `b`, into `acc`. -/
def clmulAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, a, b, acc =>
    clmulAux n (a <<< 1) (b >>> 1) (if b % 2 = 1 then acc ^^^ a else acc)

/-- One fold of the part above degree 127: x^128 = x^7 + x^2 + x + 1. -/
def fold (t : Nat) : Nat := t % 2 ^ 128 ^^^ clmulAux 8 (t / 2 ^ 128) 0x87 0

/-- The product of the field. -/
def mul (a b : Nat) : Nat := fold (fold (clmulAux 128 a b 0))

/-- Square-and-multiply over the first `n` bits of `e`. -/
def powAux : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, acc => acc
  | n + 1, b, e, acc =>
    powAux n (mul b b) (e / 2) (if e % 2 = 1 then mul acc b else acc)

/-- The power `b ^ e` of the field, for `e < 2 ^ 128`. -/
def pow (b e : Nat) : Nat := powAux 128 b e 1

/-! ## 2. The checks of the order of x (x is the element 2) -/

theorem x_pow_q3 : pow 2 ((2 ^ 128 - 1) / 3) ≠ 1 := by decide +kernel
theorem x_pow_q5 : pow 2 ((2 ^ 128 - 1) / 5) ≠ 1 := by decide +kernel
theorem x_pow_q17 : pow 2 ((2 ^ 128 - 1) / 17) ≠ 1 := by decide +kernel
theorem x_pow_q257 : pow 2 ((2 ^ 128 - 1) / 257) ≠ 1 := by decide +kernel
theorem x_pow_q641 : pow 2 ((2 ^ 128 - 1) / 641) ≠ 1 := by decide +kernel
theorem x_pow_q65537 : pow 2 ((2 ^ 128 - 1) / 65537) ≠ 1 := by decide +kernel
theorem x_pow_q274177 : pow 2 ((2 ^ 128 - 1) / 274177) ≠ 1 := by decide +kernel
theorem x_pow_q6700417 : pow 2 ((2 ^ 128 - 1) / 6700417) ≠ 1 := by decide +kernel
theorem x_pow_q67280421310721 :
    pow 2 ((2 ^ 128 - 1) / 67280421310721) ≠ 1 := by decide +kernel
theorem x_pow_order : pow 2 (2 ^ 128 - 1) = 1 := by decide +kernel

open Polynomial

/-! ## 3. The link to the algebra -/

/-- The polynomial of the field. -/
noncomputable def P : (ZMod 2)[X] := X ^ 128 + X ^ 7 + X ^ 2 + X + 1

theorem P_monic : P.Monic := by unfold P; monicity!

theorem P_natDegree : P.natDegree = 128 := by unfold P; compute_degree!

/-- The polynomial whose coefficient i is bit i of `n`. -/
noncomputable def toPoly (n : ℕ) : (ZMod 2)[X] :=
  ∑ i ∈ Finset.range n, if n.testBit i then X ^ i else 0

theorem coeff_toPoly (n j : ℕ) :
    (toPoly n).coeff j = if n.testBit j then 1 else 0 := by
  unfold toPoly
  rw [finsetSum_coeff]
  simp only [apply_ite (fun p : (ZMod 2)[X] => p.coeff j), coeff_X_pow, coeff_zero]
  by_cases hj : j < n
  · rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [Ne.symm hij]
    · intro h; exact absurd (Finset.mem_range.mpr hj) h
  · have hb : n.testBit j = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (Nat.lt_two_pow_self)
        (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hj)))
    rw [hb]
    apply Finset.sum_eq_zero
    intro i hi
    have : i ≠ j := by
      intro h; subst h; exact hj (Finset.mem_range.mp hi)
    simp [this.symm]

theorem toPoly_ext {a b : ℕ} : toPoly a = toPoly b ↔ a = b := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (fun p => p.coeff i) h
    simp only [coeff_toPoly] at this
    cases ha : a.testBit i <;> cases hb : b.testBit i <;> simp_all
  · rintro rfl; rfl

theorem toPoly_xor (a b : ℕ) : toPoly (a ^^^ b) = toPoly a + toPoly b := by
  ext j
  simp only [coeff_add, coeff_toPoly, Nat.testBit_xor]
  cases a.testBit j <;> cases b.testBit j <;> decide

theorem toPoly_shiftLeft (a k : ℕ) : toPoly (a <<< k) = X ^ k * toPoly a := by
  ext j
  rw [coeff_X_pow_mul', coeff_toPoly, Nat.testBit_shiftLeft]
  by_cases h : k ≤ j
  · simp [h, coeff_toPoly]
  · simp [h]

theorem toPoly_mod_add_div (t k : ℕ) :
    toPoly t = toPoly (t % 2 ^ k) + X ^ k * toPoly (t / 2 ^ k) := by
  ext j
  rw [coeff_add, coeff_X_pow_mul', coeff_toPoly, coeff_toPoly, Nat.testBit_mod_two_pow]
  by_cases h : k ≤ j
  · have hn : ¬ j < k := not_lt.mpr h
    simp only [hn, decide_false, Bool.false_and, h, if_true, coeff_toPoly,
      Nat.testBit_div_two_pow]
    rw [Nat.sub_add_cancel h]
    simp
  · have hj : j < k := not_le.mp h
    simp [hj, h]

theorem toPoly_one : toPoly 1 = 1 := by
  ext j; rw [coeff_toPoly, coeff_one]; cases j <;> simp [Nat.testBit_succ]

theorem toPoly_zero : toPoly 0 = 0 := by simp [toPoly]

/-- The model's carry-less product is the product of polynomials. -/
theorem toPoly_clmulAux (n : ℕ) : ∀ a b acc,
    toPoly (clmulAux n a b acc) = toPoly acc + toPoly a * toPoly (b % 2 ^ n) := by
  induction n with
  | zero => intro a b acc; simp [clmulAux, Nat.mod_one, toPoly_zero]
  | succ n ih =>
    intro a b acc
    rw [clmulAux, ih, toPoly_shiftLeft, Nat.shiftRight_one, pow_one]
    have hsplit := toPoly_mod_add_div (b % 2 ^ (n + 1)) 1
    have hm : b % 2 ^ (n + 1) % 2 ^ 1 = b % 2 :=
      Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (Nat.le_add_left 1 n))
    have hdiv : b % 2 ^ (n + 1) / 2 ^ 1 = b / 2 % 2 ^ n := by
      rw [pow_succ', pow_one, Nat.mod_mul_right_div_self]
    rw [hm, hdiv, pow_one] at hsplit
    rw [hsplit]
    by_cases hb : b % 2 = 1
    · rw [if_pos hb, toPoly_xor, hb, toPoly_one]; ring
    · have hb0 : b % 2 = 0 := by omega
      rw [if_neg hb, hb0, toPoly_zero]; ring

/-- The ring of the field, and x in it. -/
abbrev R := AdjoinRoot P

noncomputable def ev (n : ℕ) : R := AdjoinRoot.mk P (toPoly n)

theorem ev_xor (a b : ℕ) : ev (a ^^^ b) = ev a + ev b := by
  simp [ev, toPoly_xor]

theorem ev_mod_add_div (t k : ℕ) :
    ev t = ev (t % 2 ^ k) + AdjoinRoot.root P ^ k * ev (t / 2 ^ k) := by
  simp only [ev]
  rw [toPoly_mod_add_div t k, map_add, map_mul, map_pow, AdjoinRoot.mk_X]

theorem toPoly_two_pow (k : ℕ) : toPoly (2 ^ k) = X ^ k := by
  have h := toPoly_shiftLeft 1 k
  rw [Nat.one_shiftLeft, toPoly_one, mul_one] at h
  exact h

theorem toPoly_0x87 : toPoly 0x87 = X ^ 7 + X ^ 2 + X + 1 := by
  have h : (0x87 : ℕ) = ((2 ^ 7 ^^^ 2 ^ 2) ^^^ 2 ^ 1) ^^^ 2 ^ 0 := by
    rfl
  rw [h, toPoly_xor, toPoly_xor, toPoly_xor, toPoly_two_pow, toPoly_two_pow,
    toPoly_two_pow, toPoly_two_pow]
  ring

theorem root_pow_128 :
    AdjoinRoot.root P ^ 128 = ev 0x87 := by
  have h0 : AdjoinRoot.mk P P = 0 := AdjoinRoot.mk_self
  have hP : (X ^ 128 : (ZMod 2)[X]) = P + (X ^ 7 + X ^ 2 + X + 1) := by
    unfold P
    have h2 : ∀ q : (ZMod 2)[X], q + q = 0 := fun q => CharTwo.add_self_eq_zero q
    linear_combination (-1 : (ZMod 2)[X]) * h2 (X ^ 7 + X ^ 2 + X + 1)
  rw [ev, toPoly_0x87, ← AdjoinRoot.mk_X, ← map_pow, hP, map_add, h0, zero_add]

theorem ev_fold (t : ℕ) : ev (fold t) = ev t := by
  unfold fold
  rw [ev_xor, ev_mod_add_div t 128, add_right_inj]
  simp only [ev]
  rw [toPoly_clmulAux, toPoly_zero, zero_add, map_mul]
  rw [show (0x87 : ℕ) % 2 ^ 8 = 0x87 by decide]
  rw [← ev, ← ev, ← root_pow_128, mul_comm]

theorem ev_mul (a b : ℕ) (hb : b < 2 ^ 128) : ev (mul a b) = ev a * ev b := by
  unfold mul
  rw [ev_fold, ev_fold]
  simp only [ev]
  rw [toPoly_clmulAux, toPoly_zero, zero_add, Nat.mod_eq_of_lt hb, map_mul]

theorem ev_zero : ev 0 = 0 := by simp [ev, toPoly_zero]

theorem ev_one : ev 1 = 1 := by simp [ev, toPoly_one]

theorem ev_two : ev 2 = AdjoinRoot.root P := by
  have h := toPoly_two_pow 1
  rw [pow_one, pow_one] at h
  rw [ev, h, AdjoinRoot.mk_X]

theorem P_degree : P.degree = 128 := by
  rw [degree_eq_natDegree P_monic.ne_zero, P_natDegree]; rfl

set_option maxRecDepth 100000 in
/-- `ev` is injective below 2^128. -/
theorem ev_inj {a b : ℕ} (ha : a < 2 ^ 128) (hb : b < 2 ^ 128) (h : ev a = ev b) :
    a = b := by
  rw [ev, ev, AdjoinRoot.mk_eq_mk] at h
  have hdeg : (toPoly a - toPoly b).degree < P.degree := by
    rw [P_degree, show (128 : WithBot ℕ) = ((128 : ℕ) : WithBot ℕ) from rfl,
      degree_lt_iff_coeff_zero]
    intro m hm
    have hm' : 128 ≤ m := by exact_mod_cast hm
    have h2 : (2 : ℕ) ^ 128 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm'
    rw [coeff_sub, coeff_toPoly, coeff_toPoly,
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha h2),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb h2)]
    simp
  have h0 : toPoly a - toPoly b = 0 :=
    Polynomial.eq_zero_of_dvd_of_degree_lt (p := P) h hdeg
  exact toPoly_ext.mp (sub_eq_zero.mp h0)

/-- The carry-less product stays below 2^K when its shifted operand does. -/
theorem clmulAux_lt (K : ℕ) : ∀ n a b acc,
    a * 2 ^ n ≤ 2 ^ K → acc < 2 ^ K → clmulAux n a b acc < 2 ^ K := by
  intro n
  induction n with
  | zero => intro a b acc _ h; simpa [clmulAux] using h
  | succ n ih =>
    intro a b acc ha hacc
    rw [clmulAux]
    have ha' : a < 2 ^ K ∨ a = 0 := by
      rcases Nat.eq_zero_or_pos a with h | h
      · exact Or.inr h
      · left
        have : a * 2 ≤ a * 2 ^ (n + 1) :=
          Nat.mul_le_mul_left a (by
            calc 2 = 2 ^ 1 := by norm_num
              _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega))
        omega
    apply ih
    · rw [Nat.shiftLeft_eq, pow_one, mul_assoc, ← pow_succ']; exact ha
    · split
      · rcases ha' with h | h
        · exact Nat.xor_lt_two_pow hacc h
        · simpa [h] using hacc
      · exact hacc

theorem mul_lt (a b : ℕ) (ha : a < 2 ^ 128) : mul a b < 2 ^ 128 := by
  have ht : clmulAux 128 a b 0 < 2 ^ 256 :=
    clmulAux_lt 256 128 a b 0 (by
      calc a * 2 ^ 128 ≤ (2 ^ 128 - 1) * 2 ^ 128 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ 256 := by norm_num) (by norm_num)
  have hfold : ∀ t K, t < 2 ^ (K + 128) → 128 ≤ K + 8 →
      fold t < 2 ^ (K + 8) := by
    intro t K hlt hK
    unfold fold
    have hhi : t / 2 ^ 128 < 2 ^ K := by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add]; exact hlt
    have hlo : t % 2 ^ 128 < 2 ^ (K + 8) :=
      lt_of_lt_of_le (Nat.mod_lt _ (by positivity))
        (Nat.pow_le_pow_right (by norm_num) hK)
    have hc : clmulAux 8 (t / 2 ^ 128) 0x87 0 < 2 ^ (K + 8) :=
      clmulAux_lt (K + 8) 8 _ _ 0
        (by rw [pow_add]; exact Nat.mul_le_mul_right _ hhi.le) (by positivity)
    exact Nat.xor_lt_two_pow hlo hc
  have h1 : fold (clmulAux 128 a b 0) < 2 ^ (128 + 8) := hfold _ 128 ht (by norm_num)
  have h2 : fold (fold (clmulAux 128 a b 0)) < 2 ^ (120 + 8) :=
    hfold _ 120 (by
      calc fold (clmulAux 128 a b 0) < 2 ^ (128 + 8) := h1
        _ ≤ 2 ^ (120 + 128) := Nat.pow_le_pow_right (by norm_num) (by norm_num))
      (by norm_num)
  simpa [mul] using h2

theorem powAux_lt : ∀ n b e acc, b < 2 ^ 128 → acc < 2 ^ 128 →
    powAux n b e acc < 2 ^ 128 := by
  intro n
  induction n with
  | zero => intro b e acc _ h; simpa [powAux] using h
  | succ n ih =>
    intro b e acc hb hacc
    rw [powAux]
    apply ih _ _ _ (mul_lt b b hb)
    split
    · exact mul_lt acc b hacc
    · exact hacc

theorem ev_powAux : ∀ n b e acc, b < 2 ^ 128 → acc < 2 ^ 128 →
    ev (powAux n b e acc) = ev acc * ev b ^ (e % 2 ^ n) := by
  intro n
  induction n with
  | zero => intro b e acc _ _; simp [powAux, Nat.mod_one]
  | succ n ih =>
    intro b e acc hb hacc
    rw [powAux, ih _ _ _ (mul_lt b b hb) (by split <;> [exact mul_lt acc b hacc; exact hacc]),
      ev_mul b b hb, pow_succ', Nat.mod_mul]
    split
    · rename_i h
      rw [ev_mul acc b hb, h]; ring
    · rename_i h
      have h0 : e % 2 = 0 := by omega
      rw [h0]; ring

theorem ev_pow (e : ℕ) (he : e < 2 ^ 128) : ev (pow 2 e) = AdjoinRoot.root P ^ e := by
  rw [pow, ev_powAux 128 2 e 1 (by norm_num) (by norm_num), ev_one, ev_two, one_mul,
    Nat.mod_eq_of_lt he]

theorem pow_lt (e : ℕ) : pow 2 e < 2 ^ 128 := powAux_lt 128 2 e 1 (by norm_num) (by norm_num)

/-! ## The order of x, and the field -/

theorem root_pow_order : AdjoinRoot.root P ^ (2 ^ 128 - 1) = 1 := by
  rw [← ev_pow _ (by norm_num), x_pow_order, ev_one]

theorem root_pow_ne_one {e : ℕ} (he : e < 2 ^ 128) (h : pow 2 e ≠ 1) :
    AdjoinRoot.root P ^ e ≠ 1 := by
  intro hc
  rw [← ev_pow e he, ← ev_one] at hc
  exact h (ev_inj (pow_lt e) (by norm_num) hc)

/-- x as a unit of the ring. -/
noncomputable def alpha : (AdjoinRoot P)ˣ :=
  Units.ofPowEqOne (AdjoinRoot.root P) (2 ^ 128 - 1) root_pow_order (by norm_num)

theorem alpha_val : (alpha : AdjoinRoot P) = AdjoinRoot.root P := rfl

theorem alpha_pow_val (e : ℕ) : ((alpha ^ e : (AdjoinRoot P)ˣ) : AdjoinRoot P) =
    AdjoinRoot.root P ^ e := by
  rw [Units.val_pow_eq_pow_val, alpha_val]

open LfzkV2.Current.Adapter.Mdoc in
/-- The order of x in the field of the hash circuit is 2^128 - 1: x generates
the multiplicative group. -/
theorem alpha_order : orderOf alpha = 2 ^ 128 - 1 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num)
  · exact Units.ext (by rw [alpha_pow_val, root_pow_order, Units.val_one])
  · intro q hq hd
    have hprod : orderFactors.prod = 2 ^ 128 - 1 := by
      rw [orderFactors_product]; rfl
    have hm := ECDSA.mem_of_prime_dvd_prod orderFactors_prime hq (hprod ▸ hd)
    intro hc
    have hc' := congrArg Units.val hc
    rw [alpha_pow_val, Units.val_one] at hc'
    simp only [orderFactors, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact root_pow_ne_one (by norm_num) x_pow_q3 hc'
    · exact root_pow_ne_one (by norm_num) x_pow_q5 hc'
    · exact root_pow_ne_one (by norm_num) x_pow_q17 hc'
    · exact root_pow_ne_one (by norm_num) x_pow_q257 hc'
    · exact root_pow_ne_one (by norm_num) x_pow_q641 hc'
    · exact root_pow_ne_one (by norm_num) x_pow_q65537 hc'
    · exact root_pow_ne_one (by norm_num) x_pow_q274177 hc'
    · exact root_pow_ne_one (by norm_num) x_pow_q6700417 hc'
    · exact root_pow_ne_one (by norm_num) x_pow_q67280421310721 hc'

/-! ## The ring is a field -/

instance : Module.Finite (ZMod 2) (AdjoinRoot P) :=
  (AdjoinRoot.powerBasis' P_monic).finite

instance : Finite (AdjoinRoot P) := Module.finite_of_finite (ZMod 2)

/-- The ring has 2^128 elements: a basis of 128 elements over `ZMod 2`. -/
noncomputable instance : Fintype (AdjoinRoot P) :=
  Fintype.ofFinite _

theorem card_R : Fintype.card (AdjoinRoot P) = 2 ^ 128 := by
  have hb := Module.card_fintype (AdjoinRoot.powerBasis' P_monic).basis
  rw [hb, ZMod.card, Fintype.card_fin, AdjoinRoot.powerBasis'_dim, P_natDegree]

theorem zero_ne_one_R : (0 : AdjoinRoot P) ≠ 1 := by
  intro h
  rw [← ev_zero, ← ev_one] at h
  exact absurd (ev_inj (by norm_num) (by norm_num) h) (by norm_num)

/-- Every nonzero element is a unit: the units hold the 2^128 - 1 distinct
powers of x, as many as the nonzero elements. -/
theorem isUnit_of_ne_zero (r : AdjoinRoot P) (hr : r ≠ 0) : IsUnit r := by
  classical
  by_contra hnu
  have hcard_units : 2 ^ 128 - 1 ≤ Fintype.card (AdjoinRoot P)ˣ := by
    rw [← alpha_order]; exact orderOf_le_card_univ
  let S := (Finset.univ : Finset (AdjoinRoot P)ˣ).image Units.val
  have hS : S.card = Fintype.card (AdjoinRoot P)ˣ := by
    rw [Finset.card_image_of_injective _ Units.val_injective, Finset.card_univ]
  have hsub : S ⊆ ((Finset.univ.erase 0).erase r) := by
    intro x hx
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩⟩
    · intro h; exact hnu (h ▸ u.isUnit)
    · intro h
      have h1 : (u : AdjoinRoot P) * ↑u⁻¹ = 1 := u.mul_inv
      rw [h, zero_mul] at h1
      exact zero_ne_one_R h1
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hr, Finset.mem_univ _⟩),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_R, hS] at hle
  omega

theorem isField_R : IsField (AdjoinRoot P) where
  exists_pair_ne := ⟨0, 1, zero_ne_one_R⟩
  mul_comm := mul_comm
  mul_inv_cancel := fun {a} ha => (isUnit_of_ne_zero a ha).exists_right_inv

/-- The field of the hash circuit. -/
noncomputable abbrev field : Field (AdjoinRoot P) := isField_R.toField

theorem root_ne_zero : AdjoinRoot.root P ≠ 0 := by
  intro h
  have := root_pow_order
  rw [h, zero_pow (by norm_num)] at this
  exact zero_ne_one_R this

/-- x has no power equal to one below 2^128 - 1. -/
theorem root_pow_ne_one_of_lt (m : ℕ) (hm0 : 0 < m) (hm : m < 2 ^ 128 - 1) :
    AdjoinRoot.root P ^ m ≠ 1 := by
  intro h
  have hu : alpha ^ m = 1 := Units.ext (by rw [alpha_pow_val, h, Units.val_one])
  have hd := orderOf_dvd_of_pow_eq_one hu
  rw [alpha_order] at hd
  exact absurd (Nat.le_of_dvd hm0 hd) (not_le.mpr hm)

open Finset in
/-- G3 for the field of the hash circuit: `assert_eqmod` over k words of 32
bits, k from 1 to 7 (the circuit's k are 2, 4, 6 and 7), with α = x. -/
theorem assert_eqmod_words_gf128 (k : ℕ) (hk : 0 < k) (hk7 : k ≤ 7)
    (abits : ℕ → AdjoinRoot P)
    (ha : ∀ i, @BitAdder.IsBit _ field (abits i))
    (words : Fin k → ℕ → AdjoinRoot P)
    (hw : ∀ j i, @BitAdder.IsBit _ field (words j i)) :
    letI := field
    letI : DecidableEq (AdjoinRoot P) := Classical.decEq _
    (∏ i ∈ range k, ((∏ j : Fin k, BitAdder.encode (AdjoinRoot.root P) 32 (words j))
        - AdjoinRoot.root P ^ (i * 2 ^ 32) * BitAdder.encode (AdjoinRoot.root P) 32 abits)) = 0
      ↔ (∑ j : Fin k, BitAdder.value 32 (words j)) % 2 ^ 32 = BitAdder.value 32 abits := by
  letI := field
  letI : DecidableEq (AdjoinRoot P) := Classical.decEq _
  apply BitAdder.assert_eqmod_words (AdjoinRoot.root P) _ k hk _ abits ha words hw
  · exact root_ne_zero
  · intro m hm0 hm
    exact root_pow_ne_one_of_lt m hm0 (by
      calc m < k * 2 ^ 32 := hm
        _ ≤ 7 * 2 ^ 32 := Nat.mul_le_mul_right _ hk7
        _ < 2 ^ 128 - 1 := by norm_num)

end LongfellowSpark.GF128
