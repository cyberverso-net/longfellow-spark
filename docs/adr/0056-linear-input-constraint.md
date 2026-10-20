# 0056 The input constraint in linear time

## Status

Proposed (2026-10-19, block 1 of Phase D; realised in block 2)

## Date

2026-10-19

## Context

The symbolic verifier core of stage 3 ([ADR 0022](0022-stage-3-scope-and-challenges-as-input.md), [ADR 0026](0026-sparse-expression.md)) emits the input constraint of Section 6.7 as one `Expression`: the claim about the inputs at the point alpha_input, a sum over every private input of a coefficient times its variable. `Expression` is a sparse list of terms searched and merged on insertion, so building the input constraint costs a number of operations quadratic in the private inputs, and the memory of the expression is on the stack ([chapter 6](../guide/06-circuits.md), the one piece of the verifier not sized by the heap). Phase B recorded it as adequate for 6657 inputs and a problem for the prover's phase; Phase C's prover calls the same core. At 84 166 private inputs (the version 7 hash circuit) the constraint overflows the default 8 MB stack in `Input_Constraint` (the verifier of block 1 failed there; with a 64 MB stack the verification took 166 seconds and 452 MB, the prover's core the same), and `Eval_Circuit` overflows it before the core does, on a layer of 2^20 wires.

The same constraint is a theorem of the stage 3 Gold: `Verifier_Core` is Silver with proved bounds on what it emits, and the `Expression` operations are Gold against ghost references ([ADR 0023](0023-gold-perimeter-for-protocol-code.md)).

## Decision

- The input constraint is written directly in the form the core emits it. Each private input in turn gets one term, whose coefficient is computed on the spot, written straight into the Ligero terms, which are already on the heap. The few terms of the claims follow, built as before with the operations of `Expression`. There is no search-and-merge and no array of coefficients: a linear pass, with no stack in proportion to the inputs.
- The perimeter, stated explicitly. `Expression` stays as it is and stays Gold for the claim expressions of the layers, which are small. `Input_Constraint`, which was Silver, becomes Gold against the formula of Section 6.7. Term W has witness W and coefficient `Eq2 (npublic + W)`. The constant is the public binding minus the final claim, where the binding is `Pub_Binding_Ref`, the sum over the public inputs in input order. The last terms are those of `Input_Tail`, built with the Gold operations of `Expression`. No lemma relates the new form to the old sorted expression: the old construction is removed, and the formula is the reference. The postconditions of `Verifier_Core` on what it emits stand. `Eval_Circuit` with its per-layer value arrays on the heap keeps its Gold postconditions of stage 3 (`Layer_Holds`, `Layer_Z`, the inputs in the last segment) unchanged.
- The Gold postconditions are at the assertion level `Proof_Only`, next to the executable bounds of the same contract (ADR 0044).
- `Eval_Circuit`'s per-layer value arrays move to the heap under [ADR 0047](0047-heap-allocation-by-ownership.md) in the same block, so that the prover and the verifier run within the default stack on every circuit in the bounds.
- Chapter 3 (Section 3.5, the capacities) and chapter 6 (the stack as the limit of the input constraint) receive an update note pointing to this record.
- The vectors of stage 3 (`sumcheck_kat`, the recorded upstream runs) and the byte identity of the two Phase C proofs must stay green; the time of the core on the hash circuit is measured before and after.

## Alternatives considered

- **A hash map inside `Expression`.** Rejected: a general sparse structure for one dense constraint, and a data structure to prove.
- **Capping the circuits to what the quadratic form handles.** Rejected by the goal of the phase.

## Consequences

- One more construction in the core, Gold against the same reference; the `Expression` type stays for the layer claims, which are small.
- The verifier benefits as much as the prover: the verification of an mDoc proof runs the same core.

## Verification impact

- Provable: the direct construction equal to the formula of Section 6.7; absence of run-time errors; the ownership checks on the new heap object of `Eval_Circuit`.
- Measured before the change (block 2, on the proving machine): the input constraint took 17% of the verification of the version 7 hash circuit and 2% of its proof. The quadratic insertion itself took about 4%. The gain of this record is the stack more than the time. The largest cost of the verifier core, `Eval_Bound_Quad` at 57% of that verification, is left to a block of its own, because a table of eq values needs a proof that its entries equal `Eq`.
- Tested: the vectors of stage 3 unchanged; the byte identity of Phase C.
- Trusted: unchanged.
- Constant time: the pass is over public positions with public coefficients; not applicable to the verifier, declared for the prover as ADR 0051.

## References

- `src/sumcheck_expression.ads`, `src/sumcheck_verifier.adb` (the input constraint), `src/sumcheck_algebra.adb` (`Eval_Circuit`).
- [ADR 0022](0022-stage-3-scope-and-challenges-as-input.md), [ADR 0023](0023-gold-perimeter-for-protocol-code.md), [ADR 0026](0026-sparse-expression.md), [ADR 0047](0047-heap-allocation-by-ownership.md), [ADR 0055](0055-phase-d-scope-mdoc-scale.md).
