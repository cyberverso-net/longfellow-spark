# 0026 Sparse Expression

## Status

Accepted (2026-10-12, after block 2 of stage 3)

## Date

2026-10-12

## Context

The symbolic core (draft Section 6.7) manipulates affine expressions `k + SUM_i a[i] * Var (i)` over the combined witness: a known constant k and a coefficient per variable. The reference implementation (`zk/expression.rs`) stores the coefficients in a hash map keyed by variable index, removes an entry whose coefficient becomes zero, and emits a linear constraint by walking the map (`constrain_to_be_zero`), one `LigeroTerm` per entry plus the constant into b. The walk order of a Rust hash map is unspecified and differs from one process to the next.

The expressions of the core are small. The claim of a layer starts from the two pad variables c0 and c1 of the previous layer, gains two variables per hand and round (the pads of p0 and p2) and ends with the three claim pads c0, c1, cr of the current layer: at most 2 + 4 * logw + 3 variables. The input constraint holds the ninput - npublic private input variables plus the two claim pads of the last layer. SPARK has no hash maps, and an unconstrained array needs a bound stated in advance.

## Decision

- `Expression` is a discriminated record with a discriminant `Capacity`, a `Length` in 0 .. Capacity, an array `Terms (1 .. Capacity)` of pairs (`Variable`, `Coefficient`) and a `Known` constant term. A type predicate states that `Terms (1 .. Length)` is strictly increasing in `Variable`; strict order gives the absence of duplicates for free and makes the predicate a check on adjacent pairs.
- Zero coefficients are kept. The reference drops an entry whose coefficient becomes zero and clears the terms on a scale by zero; here a stored coefficient is whatever the field operations produced, because dropping it would make the postconditions depend on the field facts `c + (-c) = 0` and `0 * s = 0`, which the provers do not have ([ADR 0023](0023-gold-perimeter-for-protocol-code.md)). A zero coefficient emitted to Ligero adds nothing to the constraint; the comparison with upstream ignores zero coefficients on both sides ([ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md)).
- `Find (E, V)` returns the position of V in the sorted prefix, or 0; the ghost `Has (E, V)` is `Find (E, V) /= 0` and the ghost `Coef (E, V)` is the stored coefficient, or `Zero` when V is absent. Every operation has a postcondition stating, for all W, whether W is present in the result and what its coefficient is, with the logical equality `Same` ([ADR 0023](0023-gold-perimeter-for-protocol-code.md)), plus the `Known` of the result:
  - `From_Constant (K, Capacity)`: no variables, `Known = K`; `Var (I, Capacity)`: the single term `One * Var (I)`, `Known = Zero`;
  - `Add_Term (E, V, K)` (adds `K * Var (V)`): V present in the result, other variables unchanged, `Coef (Result, V) = Coef (E, V) + K` (the body computes exactly that sum, `Zero + K` when V was absent), `Known` unchanged;
  - `Add (E, F)` and `Sub (E, F)`: a variable of F gets `Coef (E, W) + Coef (F, W)` (or the difference), a variable only in E keeps `Coef (E, W)`; `Known` summed or subtracted;
  - `Scale (E, S)`: the same variables, every coefficient and `Known` multiplied by S;
  - `Add_Constant (E, K)` and `Sub_Constant (E, K)`: `Known` only.

  The postconditions are stated exactly in the association the body computes (`Coef (E, W) + K`, not `K + Coef (E, W)`), and the identities `Zero + X = X` and `One * X = X` are never assumed: where the reference's formula would read `Zero + K`, the body computes `Zero + K`; where a variable is absent on both sides, the postcondition says so instead of writing `Zero + Zero`.
- Capacity bound: `Capacity = max (ninput - npublic + 2, 4 * MAX_LOGW + 5)` with MAX_LOGW = 40, so 165 or more. The per-layer bound counts the variables that can enter the claim (2 + 4 * logw + 3, with logw at most MAX_LOGW because the reference draws at most 40 binding challenges); the input bound counts the private inputs and the two claim pads carried by `got_expr`. The bound is proved by arithmetic on `Length` (each `Add_Term` grows `Length` by at most one, `Add` by at most the other operand's `Length`), not by reasoning about which variables are distinct.
- Emission (`Constrain_To_Be_Zero`) appends one `LigeroTerm` per stored pair, zero coefficients included, in ascending variable order, and the constant to b. The order within a constraint is deterministic here and unspecified upstream; it is not part of the protocol (A is a sparse matrix), so comparisons with recorded upstream runs are made per constraint as a set of (variable, coefficient) pairs ([ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md)).

## Alternatives considered

- **A dense coefficient array over the whole witness.** Rejected: the witness has ninput - npublic + SUM_layers (4 * logw + 3) positions; every operation would cost that length and the emitted constraints would have to be filtered for non-zero entries anyway; the draft calls the terms sparse.
- **An unsorted array with linear search on insertion.** Rejected: the no-duplicates property becomes a quantified statement over all pairs, costly for the provers; the sorted invariant is local.
- **Dropping zero coefficients, as the reference does.** Rejected after the first proofs: the postconditions would then rest on field identities the provers do not have; the emitted constraints differ from upstream only by terms with coefficient zero, which the comparison ignores, and the capacity bound counts every variable added, which is what the bound above does anyway.
- **Fixed capacity for all expressions (a single large constant).** Rejected: the input constraint depends on ninput, which the circuit fixes at run time; a discriminant carries the right bound without a global maximum on circuit size.

## Consequences

- `Expression` is the second discriminated record under a type predicate in the project, after `Circuit`; chapter 3 explains both on first use.
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
