# 0008 Inv as a fixed Itoh-Tsujii chain, total on zero

## Status

Accepted

## Date

2026-10-08 (retroactive record, written 2026-10-09)

## Context

The multiplicative inverse in GF(2^128) is E^(2^128 - 2) by Fermat's little theorem. Proving that the result is an inverse would need the theorem itself, which is out of reach of SMT solvers; the project plan assigns `Inv` Silver plus known-answer tests. Two further choices arise: how to compute the fixed exponent in constant time, and what to do on zero, which has no inverse. The upstream implementations disagree: the C++ returns zero for the inverse of zero, the Rust reference asserts.

## Decision

- The exponentiation is a fixed addition chain in the style of Itoh and Tsujii: with T_k = E^(2^k - 1), the step T_(a+b) = T_a^(2^b) * T_b follows from (2^a - 1) * 2^b + (2^b - 1) = 2^(a+b) - 1; the chain 1, 2, 3, 6, 7, 14, 15, 30, 31, 62, 63, 126, 127 followed by one squaring gives E^(2^128 - 2) in 12 multiplications and 127 squarings. There is no test of any exponent bit: the control flow is identical for every input.
- `Inv` is a total function with `Inv (Zero) = Zero`. This is what the chain yields with no extra statement, matches the upstream C++ behaviour, and leaves no branch at call sites. Callers that must reject zero do so themselves. The header documents this.
- Proof level: Silver only. Correctness is anchored by vectors: `Inv (x) = x^-1`, `Inv (beta_i) = g^(65535 - i)`, `E * Inv (E) = 1` on random elements, and `Inv (Zero) = Zero`, with the harness re-checking `E * Inv (E) = One` at run time.

## Alternatives considered

- `Pre => E /= Zero`. Rejected: GNATprove would require every caller to prove its argument non-zero, which for values derived from adversarial input means an explicit data-dependent check before each call, against the constant-time discipline, and it would diverge from the C++ behaviour (an exception instead of zero in assertion-enabled builds).
- Square-and-multiply over the bits of the constant exponent. Rejected: the exponent is public so the branches would not leak, but a chain with no branches at all is simpler to read and to audit, and does 12 instead of 126 multiplications.
- Prove `E * Inv (E) = One` as a postcondition. Rejected by the proof policy ([0003](0003-proof-policy-and-trust-model.md)): it requires Fermat's little theorem.

## Consequences

- `Inv` and the local helper `Square_N` generate no run-time checks; their only verification conditions are termination.
- A division by zero somewhere up the stack produces zero silently; the layers that must detect it (verifier checks on adversarial input) carry that responsibility explicitly.
- The chain costs 139 multiplications until the Frobenius squaring arrives ([0007](0007-square-as-wrapper-over-mul.md)).

## Verification impact

- Provable: absence of run-time errors and termination.
- Tested: 56 inverse vectors, every expected value computed by two independent references (Fermat exponentiation and extended Euclid on GF(2)[x]) that must agree.
- Trusted: Fermat's little theorem and the exponent arithmetic of the chain (stated in the body, checked by the vectors).
- Constant time: fixed sequence of operations, no data-dependent control flow; same scope as [0006](0006-constant-time-discipline-and-scope.md).

## References

- `src/gf2_128.ads`, `Inv`; `src/gf2_128.adb`, `Square_N` and the chain.
- `tests/vectors/gf2_128_inv.txt`, `tests/vectors/gen_gf2_128_vectors.py` (`inv_fermat`, `inv_euclid`).
- google/longfellow-zk at d5e6be7: `lib/gf2k/gf2_128_test.cc` (tests Invert0, Invert1), `docs/specs/rust/src/algebra/gf2_128.rs` (inverse asserts on zero).
