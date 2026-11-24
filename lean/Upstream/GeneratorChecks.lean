-- Ported from upstream's formal/: formal/lfzk-v2/LfzkV2/Current/
-- GeneratorChecks.lean at commit 6ef3c750, as on upstream's main
-- 1424f50e (19 November 2026), https://github.com/longfellow-zk/
-- longfellow-zk. Upstream's file carries no header of its own; the
-- repository is Copyright 2025 Google LLC, under the Apache License,
-- Version 2.0 (LICENSE at 1424f50e). This project's Lean pin is
-- 7bf8a6b, where these declarations do not exist (ADR 0091, Status note
-- of block 2).
--
-- Changed from upstream, and nothing else: the import of
-- LfzkV2.Current.AdapterParameters is replaced by the imports below and
-- by the two definitions the statements use, binaryOrder and
-- groupOrder, copied from that file (formal/lfzk-v2/LfzkV2/Current/
-- AdapterParameters.lean at d803c314, lines 9 and 11); and the file's
-- last theorem, generator_order_of_check, is left out, since it rests
-- on generator_order of that file and this project does not use it.
-- The other declarations of upstream's file follow as they are,
-- statements and proofs.

import Upstream.PowMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic.NormNum.Prime

namespace LfzkV2.Current.Adapter.Mdoc

def binaryOrder : ℕ := 2^128
def groupOrder : ℕ := binaryOrder - 1

end LfzkV2.Current.Adapter.Mdoc


/-! The public generator validation of the mdoc adapter's fixed base.  The nine
factors are a complete prime factorization of `2^128-1`; checking the nine
reduced powers therefore establishes primitive order.  No discrete-log or
generator-order assumption is needed after this check succeeds.  The base is
fixed, so Rust checks it once per arithmetic backend, in the unit test
`adapter_base_is_primitive`, not per proof. -/
namespace LfzkV2.Current.Adapter.Mdoc

def orderFactors : List ℕ := [3, 5, 17, 257, 641, 65537, 274177, 6700417, 67280421310721]

set_option maxRecDepth 10000 in
private theorem prime_large_factor : Nat.Prime 67280421310721 := by
  refine lucas_primality 67280421310721 ((3 : ℕ) : ZMod 67280421310721) ?_ ?_
  · exact ECDSA.cast_pow_eq_one (fuel := 64) (by norm_num) (by decide) (by decide)
  · intro q hq hd
    have hprod : 67280421310721-1 =
        ([2, 2, 2, 2, 2, 2, 2, 2, 5, 47, 373, 2998279] : List ℕ).prod := by norm_num
    have hprimes : ∀ r ∈ ([2, 2, 2, 2, 2, 2, 2, 2, 5, 47, 373, 2998279] : List ℕ),
        Nat.Prime r := by
      norm_num
    have hm := ECDSA.mem_of_prime_dvd_prod hprimes hq (hprod ▸ hd)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ECDSA.cast_pow_ne_one (fuel := 64) (by norm_num) (by decide) (by decide)

theorem orderFactors_product : orderFactors.prod = groupOrder := by
  norm_num [orderFactors, groupOrder, binaryOrder]

theorem orderFactors_prime (q : ℕ) (hq : q ∈ orderFactors) : q.Prime := by
  simp only [orderFactors, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact prime_large_factor | norm_num

def generatorCheck {B : Type} [Field B] [DecidableEq B] (x : Bˣ) : Bool :=
  orderFactors.all fun q => decide (x^(groupOrder/q) ≠ 1)

theorem primitive_order_of_check {B : Type} [Field B] [Fintype B] [DecidableEq B]
    (hcard : Fintype.card B = binaryOrder) (x : Bˣ) (hcheck : generatorCheck x = true) :
    orderOf x = groupOrder := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num [groupOrder, binaryOrder])
  · have hx : x ^ Fintype.card Bˣ = 1 := pow_card_eq_one
    simpa only [Fintype.card_units, hcard, groupOrder] using hx
  · intro q hq hd
    have hm := ECDSA.mem_of_prime_dvd_prod orderFactors_prime hq (orderFactors_product ▸ hd)
    have hc := (List.all_eq_true.mp hcheck) q hm
    exact of_decide_eq_true hc

end LfzkV2.Current.Adapter.Mdoc
