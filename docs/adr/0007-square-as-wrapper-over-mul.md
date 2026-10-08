# 0007 Square as a wrapper over Mul

## Status

Accepted

## Date

2026-10-08 (retroactive record, written 2026-10-09)

## Context

Squaring in characteristic 2 is linear (the Frobenius map): the square of a sum is the sum of the squares, so a square can be computed by spreading the bits of the input and reducing, much faster than a general multiplication. The inversion chain ([0008](0008-inv-fixed-chain-total-function.md)) performs 127 squarings per inverse, so the fast path matters for performance. It does not matter for correctness at stage 1, and a fast squaring would need its own proof against the reference.

## Decision

`Square (E)` is implemented as `Mul (E, E)` with the postcondition `Square'Result = Mul_Ref (E, E, 128)`. The contract is proved by composition from the postcondition of `Mul`, so `Square` is Gold at no proof cost. The linear fast path is deferred as a later optimisation; when it comes, the current postcondition is already the right specification for it.

## Alternatives considered

- Implement the Frobenius fast path now. Rejected for stage 1: more code and a non-trivial proof (the bit-spreading step against `Mul_Ref`) for a speed gain that nothing needs yet.
- No `Square` at all, callers use `Mul (E, E)`. Rejected: the name documents intent in the inversion chain and gives the optimisation a single place to land without touching callers or contracts.

## Consequences

- One trivial subprogram, one verification condition (the postcondition).
- Squaring costs a full multiplication; `Inv` costs 139 multiplications.
- Square vectors ([0009](0009-known-answer-vectors.md)) exist now and will test the fast path later without change.

## Verification impact

- Provable: Square = Mul_Ref (E, E, 128) for every input, by composition.
- Tested: 48 square vectors, 8 of them anchored on upstream constants (beta_i^2 = beta_(2i)).
- Trusted: nothing additional.
- Constant time: inherits the discipline of `Mul`.

## References

- `src/gf2_128.ads`, `Square`; `src/gf2_128.adb`.
- `tests/vectors/gf2_128_square.txt`.
- [0005](0005-mul-ref-as-proof-target.md).
