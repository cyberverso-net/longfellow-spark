# 0023 Gold perimeter for protocol code

## Status

Proposed

## Date

2026-10-12

## Context

Stages 1 and 2 proved the field operations against a reference: `Mul = Mul_Ref` for GF(2^128) ([ADR 0005](0005-mul-ref-as-proof-target.md)), `To_Int (Mul (A, B)) = To_Int (A) * To_Int (B) mod P` for P-256 ([ADR 0014](0014-p256-functional-specification-and-ghost-model.md)). Neither proof gives GNATprove the field laws. Inside a unit generic over a field ([ADR 0024](0024-field-genericity-by-formal-package.md)) the operations `+`, `-`, `*` are formal subprograms: the provers see uninterpreted functions, know nothing of commutativity, associativity or distributivity, and a lemma stating a field law with no proof would be an axiom, which ADR 0014 excludes. Even for a concrete instance, `Mul_Ref` is a Horner recursion and the integer model needs `mod P` reasoning; neither yields the ring laws to an SMT solver at the step budget of [ADR 0020](0020-prover-configuration-step-budget.md).

A specification such as "`eq (r, x)` is the product over the bits of x" is therefore provable only as a structural statement: the executable code computes the same sequence of field operations, in the same order, as a ghost reference that transcribes the formula of the draft or of the reference implementation. This is exactly what Gold meant for `Mul` at stage 1, and the project should say so again rather than let "Gold" suggest more.

## Decision

Gold at stage 3 is structural: a ghost reference function transcribes the formula in a fixed order of operations, and the executable code is proved equal to it for all inputs. The reference is the specification; whether the reference matches the draft is a tested property, as for `Mul_Ref`. The package header and the chapter state this meaning in those words.

Gold kernels and their references:

- `Eq (R, X, N)`: equal to a recursive reference over the bits of X in ascending order, `Eq_Ref (R, X, 0) = One` and `Eq_Ref (R, X, K) = Eq_Ref (R, X, K - 1) * (if bit K - 1 of X then R (K - 1) else One - R (K - 1))`, the fold order of the reference `eq`.
- `Eq2`: an expression function, `Eq (G0, X, N) + Alpha * Eq (G1, X, N)`; Gold by definition.
- `Bindeq (C)`: pointwise against the recursive definition of Section 6.2: element i equals `(if i is even then One - C (0) else C (0)) * Bindeq (C (1 ..)) (i / 2)`, with the empty-challenge case equal to `One`. That `Bindeq (C) (i) = Eq (C, i, N)` is an algebraic truth (the two folds multiply in opposite orders) and is tested, not proved.
- `Bind (A, X)`: element i of the result equals `(One - X) * A (2 i) + X * A (2 i + 1)` with zero padding beyond the length of A (Section 6.1); the formula is the postcondition itself.
- `Lagrange_Basis (R)`: equal to the three formulas of `lagrange_basis` with the per-field denominator inverses as constants ([ADR 0025](0025-polynomials-and-lagrange-constants.md)). That the constants are inverses, and that the basis interpolates at the three points, are tested.
- `Eval_Quad (NV, W, Terms)`: the result and the status equal a reference that walks the term list in order: for a term with k = 0 the Z assertion `W (h1) * W (h0) = Zero` is checked; otherwise `k * W (h1) * W (h0)`, in that association, is added to the accumulator of wire g. The reference states the accumulated value of each output wire after the first N terms and the conjunction of the assertions seen so far.
- `Eval_Circuit`: layer by layer from the input layer, each layer Gold by `Eval_Quad`, with the final check that every output wire is `Zero`; the status is the conjunction.
- `Bind_G` and `Eval_Bound_Quad`: per term, in list order, the formulas of the reference (`beta * eq2 (g)` when k = 0, else `k * eq2 (g)`, then the two `eq` factors on h0 and h1).
- The `Expression` operations: every operation has a postcondition giving the coefficient of every variable and the constant term of the result ([ADR 0026](0026-sparse-expression.md)).
- `Symbolic_Sumcheck_Round`: the next claim equals `P0 * L0 + P1 * L1 + P2 * L2` with `P0 = Var (pad0) + hp0`, `P2 = Var (pad1) + hp2`, `P1 = Claim - P0`, stated through the coefficient function of `Expression`.

Tested, not proved: every algebraic truth about the above (bindeq agrees with eq, the Lagrange basis interpolates, the constraints emitted for an honest proof are satisfied by the honest witness, soundness). Silver everywhere else: `Verify_Layer`, `Input_Constraint`, `Symbolic_Sumcheck_Verifier_Core`, with postconditions limited to sizes, index ranges and the count of emitted constraints.

## Alternatives considered

- **Stating the field laws as lemmas with null bodies, so that contracts could speak of sums and products freely.** Rejected: an axiom; ADR 0014 excludes it, and a wrong axiom proves anything.
- **Proving the field laws for each instance.** Not pursued: for GF(2^128) it would mean proving that Horner evaluation is a ring homomorphism, a Platinum-style effort ADR 0005 already declined; for P-256 the laws hold in `Big_Integer` arithmetic modulo P, but connecting them to the formal operations of the generic would need the same lemmas at every call site. The gain over tests is small: the algebraic truths are checked on both fields by the vectors.
- **Gold only on `Eval_Circuit`, Silver on the rest.** Rejected: the symbolic core is where a transcription error (a swapped hand, a missing factor) would make the verifier accept a wrong constraint set silently; its formulas are cheap to state and the structural proof catches exactly that class.
- **No Gold at all on protocol code (tests only).** Rejected: a verifier whose arithmetic is proved only on samples contradicts the trust model of [ADR 0003](0003-proof-policy-and-trust-model.md), which names circuit evaluation semantics as a Gold target.

## Consequences

- The reference functions are ghost and recursive; they execute in the assertion-enabled test build ([ADR 0010](0010-assertion-enabled-test-project.md)) at every call, so harness run time grows with the size of the circuits used; the explicit circuits are small.
- The order of operations in the executable code is fixed by the reference: a later optimisation that reorders a product is a change to the reference and to this record's list.
- The README trust model gains the entry "Gold at stage 3 is structural: equality with a ghost transcription of the draft's formulas; the algebraic properties of those formulas are tested".

## Verification impact

- Provable: equality of each Gold kernel with its reference for all inputs; absence of run-time errors everywhere.
- Tested: the references against the draft and the upstream reference (explicit circuits, structural and random cases, recorded runs), per [ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md).
- Trusted: the field laws of the two instances (never stated to the prover); the soundness argument of the protocol.
- Constant time: not required at this stage ([ADR 0022](0022-stage-3-scope-and-challenges-as-input.md)); ghost code is excluded from executable builds with assertions disabled, as before.

## References

- [ADR 0003](0003-proof-policy-and-trust-model.md), [ADR 0005](0005-mul-ref-as-proof-target.md), [ADR 0014](0014-p256-functional-specification-and-ghost-model.md).
- draft-google-cfrg-libzk-03, Sections 6.1, 6.2, 6.3.2, 6.3.3, 6.4, 6.7.
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/sumcheck/common.rs` (`eq`, `eq2`, `eval_quad`, `eval_circuit`, `bind_g`, `eval_bound_quad`), `sumcheck/prover.rs` (`bind`, `vector_ref`), `zk/symbolic_sumcheck_verifier.rs` (`symbolic_sumcheck_round`).
