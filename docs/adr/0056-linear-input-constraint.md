# 0056 The input constraint in linear time

## Status

Proposed (2026-10-19, block 1 of Phase D; realised in block 2)

## Date

2026-10-19

## Context

The symbolic verifier core of stage 3 ([ADR 0022](0022-stage-3-scope-and-challenges-as-input.md), [ADR 0026](0026-sparse-expression.md)) emits the input constraint of Section 6.7 as one `Expression`: the claim about the inputs at the point alpha_input, a sum over every private input of a coefficient times its variable. `Expression` is a sparse list of terms searched and merged on insertion, so building the input constraint costs a number of operations quadratic in the private inputs, and the memory of the expression is on the stack ([chapter 6](../guide/06-circuits.md), the one piece of the verifier not sized by the heap). Phase B recorded it as adequate for 6657 inputs and a problem for the prover's phase; Phase C's prover calls the same core. At 84 166 private inputs (the version 7 hash circuit) the constraint overflows the default 8 MB stack in `Input_Constraint` (the verifier of block 1 failed there; with a 64 MB stack the verification took 166 seconds and 452 MB, the prover's core the same), and `Eval_Circuit` overflows it before the core does, on a layer of 2^20 wires.

The same constraint is a theorem of the stage 3 Gold: `Verifier_Core` is Silver with proved bounds on what it emits, and the `Expression` operations are Gold against ghost references ([ADR 0023](0023-gold-perimeter-for-protocol-code.md)).

## Decision

- The input constraint is built directly in the form the core emits it, one term per private input in input order, without the search-and-merge of `Expression`: a linear pass, on the heap.
- The specification does not change: the constraint is the same polynomial, stated by the same ghost reference; the structural Gold of the stage is kept, and the postconditions of `Verifier_Core` on what it emits stand. Where the new construction needs a lemma connecting the direct form to `Expression`'s reference, the lemma is proved, not assumed.
- `Eval_Circuit`'s per-layer value arrays move to the heap under [ADR 0047](0047-heap-allocation-by-ownership.md) in the same block, so that the prover runs within the default stack on every circuit in the bounds.
- The vectors of stage 3 (`sumcheck_kat`, the recorded upstream runs) and the byte identity of the two Phase C proofs must stay green; the time of the core on the hash circuit is measured before and after.

## Alternatives considered

- **A hash map inside `Expression`.** Rejected: a general sparse structure for one dense constraint, and a data structure to prove.
- **Capping the circuits to what the quadratic form handles.** Rejected by the goal of the phase.

## Consequences

- One more construction in the core, Gold against the same reference; the `Expression` type stays for the layer claims, which are small.
- The verifier benefits as much as the prover: the verification of an mDoc proof runs the same core.

## Verification impact

- Provable: the direct construction equal to the reference polynomial; absence of run-time errors; the ownership checks on the new heap objects.
- Tested: the vectors of stage 3 unchanged; the byte identity of Phase C.
- Trusted: unchanged.
- Constant time: the pass is over public positions with public coefficients; not applicable to the verifier, declared for the prover as ADR 0051.

## References

- `src/sumcheck_expression.ads`, `src/sumcheck_verifier.adb` (the input constraint), `src/sumcheck_algebra.adb` (`Eval_Circuit`).
- [ADR 0022](0022-stage-3-scope-and-challenges-as-input.md), [ADR 0023](0023-gold-perimeter-for-protocol-code.md), [ADR 0026](0026-sparse-expression.md), [ADR 0047](0047-heap-allocation-by-ownership.md), [ADR 0055](0055-phase-d-scope-mdoc-scale.md).
