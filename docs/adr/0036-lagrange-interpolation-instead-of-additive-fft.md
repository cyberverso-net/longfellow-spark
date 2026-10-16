# 0036 Reed-Solomon by Lagrange interpolation, not the additive FFT

## Status

Accepted (2026-10-15, before block 2 of stage 5)

## Date

2026-10-15

## Context

The `extend` method of the draft turns k field elements into n evaluations of the polynomial of degree below k that interpolates them at the first k evaluation points (Section 2.2.1 for prime fields, 2.2.2 for GF(2^k)). The draft presents an additive FFT for the binary field; the reference implementation that produced the Appendix B.3 vectors does neither: `ReedSolomonCode::new` builds the Lagrange matrix of `algebra/interpolation.rs` (k rows, n columns, an identity block for x < k, otherwise the product over j of (pts[x] - pts[j]) for j not i, times the inverse of the product of (pts[i] - pts[j])) and `encode_row` is the matrix-vector product, in the order "for each column x, the sum over i of row[i] times L[i][x]". The evaluation points are `reed_solomon_eval_point (x)`: for GF(2^128) the injection of x through the subfield basis (the sum of basis[i] over the set bits of x, x below 2^16), for P-256 the integer x.

The verifier uses the code in one way only: it needs the encoding of a response polynomial at the NREQ queried columns DBLOCK + idx, three times (the LDT polynomial of BLOCK elements, the linear polynomial and the reconstructed quadratic polynomial of DBLOCK elements), and the encoding of each row of the linear-test vector at the same columns. The reference computes the whole encoding and reads the queried entries.

## Decision

- `extend` is Lagrange interpolation over the reference's evaluation points, as a matrix-vector product in the reference's order. The convention, the points and the interpolating polynomial, is normative and anchored by the vectors; the algorithm is not: a future prover may use the draft's additive FFT, checked against this.
- The verifier builds, once per geometry, the columns of the Lagrange matrix it will read: for each queried column x = DBLOCK + idx and each i below k, the entry L[i][x], for k = BLOCK and for k = DBLOCK, two tables of k times NREQ elements. The inverses of the k denominators are computed once per table ([ADR 0037](0037-checked-inv-and-public-data-scope.md)). The full k times n matrix of the reference exists in test code, where the interpolation property is checked, and nowhere in the library.
- The three tests and the linear-test rows receive the tables and evaluate "the polynomial with these coefficients at the queried columns" as the dot product of the coefficients with each table column, in the reference's order of operations.

## Alternatives considered

- **The additive FFT of the draft.** Rejected for the verifier: it would compute n evaluations to use NREQ of them, it is defined for the binary field only (the reference uses Lagrange for both), and the vectors were produced with Lagrange; the stage would carry a second algorithm to prove equal to the first.
- **The full Lagrange matrix, as the reference.** Rejected: k times NCOL elements, gigabytes at the profile of Section 5.1 (NCOL in the tens of thousands); the verifier reads NREQ columns of it.
- **Evaluating each polynomial directly by the barycentric formula at the queried points.** Equivalent in cost; rejected in favour of the table because the table is the reference's object with fewer columns, so the structural proof reads against `lagrange_matrix` line by line.

## Consequences

- Memory of the verifier for the code: 2 (BLOCK + DBLOCK) NREQ elements instead of (BLOCK + DBLOCK) NCOL; for the Section 5.1 profile, hundreds of kilobytes instead of gigabytes.
- The evaluation points are a formal of the generic (or derived from the field's subfield basis for GF(2^128), from the integers for P-256) and are anchored by the tier 2 vectors on both fields.

## Verification impact

- Provable: the table entries are the formula of `lagrange_matrix` for the queried columns, structurally (ADR 0038); the evaluation is the dot product in the reference's order.
- Tested: the interpolation property (the encoding of k values agrees with them at the first k points) and agreement with the reference's full matrix, by the generator; the end-to-end vectors.
- Trusted: nothing new.
- Constant time: not applicable (ADR 0037).

## References

- draft-google-cfrg-libzk-03, Sections 2.2.1, 2.2.2, 4.3.
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/ligero/reed_solomon.rs`, `algebra/interpolation.rs` (`lagrange_matrix`), `algebra/gf2_128.rs` and `algebra/p256.rs` (`reed_solomon_eval_point`).
- [ADR 0035](0035-stage-5-scope-ligero-and-the-complete-verifier.md).
