# 0005 Ghost reference Mul_Ref as the proof target of Mul

## Status

Accepted

## Date

2026-10-06 (retroactive record, written 2026-10-09)

## Context

A functional contract for multiplication needs a definition of the product to compare against. Writing it as a polynomial identity over coefficients would require quantified reasoning over 255 product terms and a modular reduction, which SMT solvers do not handle well. SPARK ghost code allows a reference implementation that exists only for proof, so the contract can be "the result equals what the reference computes".

## Decision

`Mul_Ref (A, B, N)` is a ghost expression function: MSB-first Horner evaluation over the top N bits of B, defined recursively with `Xtime` and `Add`, with `Subprogram_Variant => (Decreases => N)` for termination. `Mul_Ref (A, B, 128)` is taken as the definition of A * B mod Q(x), on the ground that Horner evaluation of the bits of B is polynomial multiplication with reduction interleaved. The postcondition of `Mul` is `Mul'Result = Mul_Ref (A, B, 128)`, and the loop invariant of the implementation is `R = Mul_Ref (A, B, K)` after K iterations, so the implementation mirrors the reference step by step.

The package header states explicitly that the proof establishes Mul = Mul_Ref for all inputs, and that Mul_Ref matching the draft's convention is a tested property, not a proved one.

## Alternatives considered

- A coefficient-level specification (for all i, bit i of the result equals the xor of the products of the coefficients, reduced). Rejected: far beyond level 2 SMT reach and hard to read.
- LSB-first iteration (as the upstream Rust `clmul_reduce`, which shifts the multiplicand). Rationale for choosing MSB-first not recorded at the time. What is known: MSB-first Horner lets the accumulator be reduced by one `Xtime` per step and gives a one-line invariant.
- Prove Mul_Ref itself equal to a polynomial model. Not pursued: it would be a Platinum-style effort for a gain that vectors already give, see [0003](0003-proof-policy-and-trust-model.md).

## Consequences

- `Mul` is Gold relative to `Mul_Ref`; the same reference serves `Square` by composition ([0007](0007-square-as-wrapper-over-mul.md)).
- When assertions are enabled, `Mul_Ref` executes at run time inside the postcondition and inside the loop invariant; this is the reason for the scope limit of the constant-time claim ([0006](0006-constant-time-discipline-and-scope.md)) and for the cost of the test build ([0010](0010-assertion-enabled-test-project.md)).
- The gap "Mul_Ref versus the draft" is closed by known-answer vectors anchored on upstream constants ([0009](0009-known-answer-vectors.md)).

## Verification impact

- Provable: Mul = Mul_Ref for every pair of inputs, discharged by CVC5 at level 2 (six checks for Mul, five for Mul_Ref).
- Tested: Mul_Ref = the draft's product, on 105 vectors including 22 external anchors.
- Trusted: that Horner evaluation is multiplication (a mathematical fact, stated in the header, not proved in SPARK).
- Constant time: ghost code is excluded from executable builds only when assertions are disabled.

## References

- `src/gf2_128.ads`, `Mul_Ref`, `Mul`; `src/gf2_128.adb`, the loop invariant of `Mul`.
- google/longfellow-zk at d5e6be7, `docs/specs/rust/src/algebra/gf2_128.rs`, `clmul_reduce` (the LSB-first alternative).
- SPARK User's Guide, "Ghost code" and "Subprogram_Variant".
