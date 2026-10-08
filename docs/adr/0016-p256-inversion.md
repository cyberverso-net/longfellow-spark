# 0016 P-256 base field: inversion

## Status

Proposed

## Date

2026-10-09

## Context

The inverse in F_p is E^(p - 2) by Fermat's little theorem. The two upstream implementations differ: the Rust reference computes `pow (p - 2)` and asserts on zero; the C++ (`fp_generic.h`, `invertf`) uses a binary extended Euclidean algorithm with data-dependent branches and loop length, which returns zero for zero and is not constant time. [0008](0008-inv-fixed-chain-total-function.md) fixed, for GF(2^128), a total function with `Inv (Zero) = Zero` computed by a fixed chain; consistency across fields matters for callers and for the trust model.

## Decision (proposed)

- Fermat exponentiation with a fixed addition chain for p - 2 = 2^256 - 2^224 + 2^192 + 2^96 - 3, exploiting the structure of the exponent (long runs of ones and zeros): a short sequence of windowed powers combined with repeated squarings, in the style of the P-256 chains used by constant-time libraries, about 255 squarings and under 20 multiplications. The chain is written out as constants, as in stage 1; no exponent bit is tested at run time.
- Total function, `Inv (Zero) = Zero`, as in [0008](0008-inv-fixed-chain-total-function.md); the chain yields zero on zero with no extra statement. The header documents the C++ and Rust behaviours.
- Silver plus vectors: `Inv (1) = 1`, `Inv (2) = (p + 1) / 2`, `Inv (p - 1) = p - 1`, `E * Inv (E) = 1` on random elements and on the base point coordinates, `Inv (Zero) = Zero`, every expected value computed by two independent Python methods (Fermat and extended Euclid) that must agree.
- The sumcheck layer needs the inverse of two as a constant (upstream `half_`); it is declared as a constant with a vector, not computed at elaboration.

## Alternatives considered

- **Binary extended Euclid, as upstream C++.** Fewer multiplications, but data-dependent control flow (against [0006](0006-constant-time-discipline-and-scope.md)) and a loop whose termination and bounds would need a measure on the operands; a constant-time variant (fixed iteration count, Bernstein-Yang style) is considerably more intricate to prove Silver. Rejected.
- **`Pre => E /= Zero`.** Rejected for the reasons of [0008](0008-inv-fixed-chain-total-function.md): forces data-dependent checks at call sites and diverges from C++.
- **Square-and-multiply over the 256 exponent bits.** Branch pattern is public (the exponent is a constant), but 255 squarings plus about 250 multiplications and a longer chain to read. Rejected in favour of the windowed chain.

## Consequences

- `Inv` costs roughly 270 multiplications until squaring is specialised.
- A division by zero yields zero silently; the layers that must detect it do so explicitly, as decided in [0008](0008-inv-fixed-chain-total-function.md).
- The chain's exponent arithmetic is documented in the chapter and checked numerically by the vector generator (the generator recomputes the chain symbolically and verifies that it equals p - 2).

## Verification impact

- Provable: absence of run-time errors, termination, canonical form of the result (by the predicate of [0015](0015-p256-canonical-form-and-conditional-subtraction.md)).
- Tested: inverse property on vectors, chain exponent by the generator.
- Trusted: Fermat's little theorem.
- Constant time: fixed sequence, no data-dependent control flow.

## References

- google/longfellow-zk at d5e6be7: `lib/algebra/fp_generic.h` (`invertf`, binary extended Euclid; `half_`), `docs/specs/rust/src/algebra/p256.rs` (`inv`, assert on zero).
- [0008](0008-inv-fixed-chain-total-function.md).
