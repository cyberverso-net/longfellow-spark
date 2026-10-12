# 0026 Sparse Expression

## Status

Proposed

## Date

2026-10-12

## Context

The symbolic core (draft Section 6.7) manipulates affine expressions `k + SUM_i a[i] * Var (i)` over the combined witness: a known constant k and a coefficient per variable. The reference implementation (`zk/expression.rs`) stores the coefficients in a hash map keyed by variable index, removes an entry whose coefficient becomes zero, and emits a linear constraint by walking the map (`constrain_to_be_zero`), one `LigeroTerm` per entry plus the constant into b. The walk order of a Rust hash map is unspecified and differs from one process to the next.

The expressions of the core are small. The claim of a layer starts from the two pad variables c0 and c1 of the previous layer, gains two variables per hand and round (the pads of p0 and p2) and ends with the three claim pads c0, c1, cr of the current layer: at most 2 + 4 * logw + 3 variables. The input constraint holds the ninput - npublic private input variables plus the two claim pads of the last layer. SPARK has no hash maps, and an unconstrained array needs a bound stated in advance.

## Decision

- `Expression` is a discriminated record with a discriminant `Capacity`, a `Length` in 0 .. Capacity, an array `Terms (1 .. Capacity)` of pairs (`Variable`, `Coefficient`) and a `Known` constant term. A type predicate states that `Terms (1 .. Length)` is strictly increasing in `Variable`; strict order gives the absence of duplicates for free and makes the predicate a check on adjacent pairs.
- Zero coefficients are not stored: an operation that produces a zero coefficient drops the entry, as the reference does. This is a run-time test on the computed value and needs no field law to prove.
- The ghost function `Coefficient (E, V)` returns the stored coefficient of V, or `Zero` if V is absent. Every operation has a postcondition stating `Coefficient` of the result for all V and the `Known` of the result:
  - `From_Constant (K)`: no variables, `Known = K`;
  - `Add_Term (E, V, K)` (adds `K * Var (V)`): `Coefficient (Result, W) = Coefficient (E, W) + (if W = V then K else Zero)` for all W, `Known` unchanged;
  - `Add (E, F)` and `Sub (E, F)`: coefficient-wise sum or difference, `Known` summed or subtracted;
  - `Scale (E, S)`: every coefficient and `Known` multiplied by S; `Scale (E, Zero)` empties the variables;
  - `Add_Constant (E, K)` and `Sub_Constant (E, K)`: `Known` only.

  Because the field laws are not available ([ADR 0023](0023-gold-perimeter-for-protocol-code.md)), the postconditions are stated exactly in the association the body computes (`Coefficient (E, W) + K`, not `K + Coefficient (E, W)`), and the identities `Zero + X = X` and `One * X = X` are not assumed: a postcondition on an absent variable says `Zero + K`, which the body stores as `K`, and the two are expected to be proved equal in each instance from the field's own `Add` contract (xor with zero on GF(2^128); `To_Int` of zero and the injectivity lemma of chapter 2 on P-256). If an instance does not discharge that step, the fallback is a case-split postcondition (`Coefficient (E, W) + K` when W is present in E, `K` otherwise), which needs no identity at all; the choice is recorded in the chapter.
- Capacity bound: `Capacity = max (ninput - npublic + 2, 4 * MAX_LOGW + 5)` with MAX_LOGW = 40, so 165 or more. The per-layer bound counts the variables that can enter the claim (2 + 4 * logw + 3, with logw at most MAX_LOGW because the reference draws at most 40 binding challenges); the input bound counts the private inputs and the two claim pads carried by `got_expr`. The bound is proved by arithmetic on `Length` (each `Add_Term` grows `Length` by at most one, `Add` by at most the other operand's `Length`), not by reasoning about which variables are distinct.
- Emission (`Constrain_To_Be_Zero`) appends one `LigeroTerm` per stored pair, in ascending variable order, and the constant to b. The order within a constraint is deterministic here and unspecified upstream; it is not part of the protocol (A is a sparse matrix), so comparisons with recorded upstream runs are made per constraint as a set of (variable, coefficient) pairs ([ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md)).

## Alternatives considered

- **A dense coefficient array over the whole witness.** Rejected: the witness has ninput - npublic + SUM_layers (4 * logw + 3) positions; every operation would cost that length and the emitted constraints would have to be filtered for non-zero entries anyway; the draft calls the terms sparse.
- **An unsorted array with linear search on insertion.** Rejected: the no-duplicates property becomes a quantified statement over all pairs, costly for the provers; the sorted invariant is local.
- **Keeping zero coefficients.** Rejected: the emitted constraints would differ from upstream by zero terms, and the capacity bound would have to count every variable ever touched rather than every variable present.
- **Fixed capacity for all expressions (a single large constant).** Rejected: the input constraint depends on ninput, which the circuit fixes at run time; a discriminant carries the right bound without a global maximum on circuit size.

## Consequences

- `Expression` is the first discriminated record and the first type predicate on a composite in the project; chapter 3 explains both on first use.
- Every operation on expressions copies at most Capacity pairs; the core performs O(logw) of them per layer on arrays of at most 165 pairs, negligible next to the field arithmetic of `Eval_Bound_Quad`.
- The predicate is checked at every assignment of an `Expression` in the assertion-enabled test build.

## Verification impact

- Provable: the postconditions above for every operation, hence the exact coefficient and constant of every constraint the core emits, as a function of the inputs; the capacity bound; absence of run-time errors.
- Tested: the emitted constraints against recorded upstream runs, per constraint, ignoring order within a constraint.
- Trusted: nothing new.
- Constant time: no requirement; the data are public.

## References

- draft-google-cfrg-libzk-03, Section 6.7 (expressions, `constrain_to_be_zero`, `LigeroTerm`), Section 6.5 (pad layout), Section 6.6 (MAX_LOGW).
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/zk/expression.rs`, `zk/symbolic_sumcheck_verifier.rs`, `ligero/common.rs` (`LigeroTerm`).
- SPARK User's Guide, "Type predicates" and "Discriminated records".
