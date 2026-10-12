# 0025 Polynomials and Lagrange constants

## Status

Proposed

## Date

2026-10-12

## Context

The sumcheck polynomials are of degree two and are represented by their evaluations at three points, P0 = 0, P1 = 1 and P2 (draft Section 6.4). The prover sends p(P0) and p(P2), one-time padded; p(P1) is reconstructed from the claim, since p(P0) + p(P1) is the claim of the round. The verifier evaluates p at the challenge r through the Lagrange basis of the three points: `lagrange_basis (r) = [l0, l1, l2]` with

    l0 = (r - x1) (r - x2) / ((x0 - x1) (x0 - x2))
    l1 = (r - x0) (r - x2) / ((x1 - x0) (x1 - x2))
    l2 = (r - x0) (r - x1) / ((x2 - x0) (x2 - x1))

(`algebra/interpolation.rs`). P2 depends on the field: 2 in odd characteristic; on GF(2^128) it is inj(2) of Section 2.2.2, the second element of the subfield basis, beta_1 = 0x5c5971877501d4b8f1871e01b64fda4c (`SUBFIELD_BASIS[1]`, already an external anchor of [ADR 0009](0009-known-answer-vectors.md)). The reference divides at run time. In this project `Inv` is Silver on both fields and is not a function the Gold kernels may lean on ([ADR 0008](0008-inv-fixed-chain-total-function.md), [ADR 0016](0016-p256-inversion.md)).

## Decision

- Polynomials are kept as evaluations, as the draft fixes; no coefficient form is introduced. The symbolic round computes `p1 = claim - p0` and `next_claim = p0 * l0 + p1 * l1 + p2 * l2` ([ADR 0023](0023-gold-perimeter-for-protocol-code.md)).
- The three denominators are per-field constants and their inverses are formal objects of `Field_Signature` ([ADR 0024](0024-field-genericity-by-formal-package.md)): `L0_Den_Inv`, `L1_Den_Inv`, `L2_Den_Inv`. `Lagrange_Basis (R)` computes `(R - One) * (R - P2) * L0_Den_Inv`, `R * (R - P2) * L1_Den_Inv`, `R * (R - One) * L2_Den_Inv` in that association, with `R - Zero` written as `R`; `Inv` is not called anywhere in the verifier.
- Values. On GF(2^128), where subtraction is addition: d0 = P2, d1 = One + P2, d2 = P2 * (One + P2). On P-256: d0 = 2, d1 = -1, d2 = 2, so the inverses are (p + 1) / 2, p - 1, (p + 1) / 2.
- The vector generator computes each inverse independently (extended Euclid in GF(2)[x], modular inverse of the integer), checks `d * inv (d) = 1` with its own arithmetic, and writes the constants into the vector files; the harness recomputes `d * Inv_Constant = One` with the library's `Mul` at start-up and fails if it does not hold. The constants in the instantiation packages are copied from the generator's output and cited to it.

## Alternatives considered

- **Divide at run time with `Inv`, as the reference does.** Rejected: three inversions per round for a value that never changes, and a Gold kernel would depend on a Silver function; the postcondition of `Lagrange_Basis` could then only say "equals the formula with `Inv`", which proves nothing about the value.
- **Coefficient representation of the polynomials.** Rejected: the draft fixes evaluations at three points; converting would add arithmetic to prove and to test for no protocol benefit.
- **Hard-coding the three basis polynomials in simplified per-field form (for example l1 = r (r + P2) / (1 + P2) on GF(2^128)).** Rejected: the simplification uses field laws the prover does not have; the uniform formula keeps one generic body and one proof.
- **Computing the inverses once at elaboration with `Inv`.** Rejected: library elaboration with field arithmetic complicates the SPARK elaboration checks for no gain over a checked constant.

## Consequences

- `Field_Signature` carries three constants that a reader must trust to be inverses; the trust is discharged by the generator and re-checked by the harness at every run.
- Adding a field means computing its three inverses in the generator, which aborts if the check fails.
- The interpolation property (l0 + l1 + l2 = 1, and the basis evaluated at x0, x1, x2 yields the unit vectors) is tested in tier 2, not proved.

## Verification impact

- Provable: `Lagrange_Basis` equals the formula with the constants, for every R; absence of run-time errors.
- Tested: the constants are inverses (generator, independently; harness, with `Mul`); the interpolation property on structural and random cases.
- Trusted: nothing new. The correctness of P2 on GF(2^128) rests on the same upstream constant that anchors stage 1.
- Constant time: no requirement.

## References

- draft-google-cfrg-libzk-03, Section 6.4, Section 2.2.2 (inj and the subfield basis).
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/algebra/interpolation.rs` (`lagrange_basis`), `algebra/gf2_128.rs` (`sumcheck_eval_points`, `SUBFIELD_BASIS`), `algebra/p256.rs` (`sumcheck_eval_points`).
- [ADR 0009](0009-known-answer-vectors.md), [ADR 0024](0024-field-genericity-by-formal-package.md), [ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md).
