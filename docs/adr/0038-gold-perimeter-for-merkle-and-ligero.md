# 0038 Gold perimeter for Merkle and Ligero

## Status

Accepted (2026-10-15, before block 2 of stage 5)

## Date

2026-10-15

## Context

[ADR 0023](0023-gold-perimeter-for-protocol-code.md) made Gold structural for protocol code: equality with a ghost transcription of the formula in the reference's order of operations, the algebraic content left to tests; [ADR 0031](0031-transcript-gold-perimeter.md) applied it to the transcript. Stage 5 has three kinds of code: hashing and path discipline (Merkle), where the properties are exactly what the commitment relies on; index arithmetic (geometry), where an error is an out-of-range read of the proof; and the four tests, linear algebra over the field in a fixed order, where a swapped index or a missing term changes the verdict and no vector that passes can tell.

## Decision

Gold perimeter of stage 5, in the structural sense of ADR 0023:

- **Merkle heap construction** (test code and the recomputation inside verification): node i is the hash of nodes 2 i and 2 i + 1, against the recursive definition `Layers (I) = H (Layers (2 I) || Layers (2 I + 1))` for 1 <= I < N, leaves at N .. 2 N - 1.
- **Path discipline** of batch verification: exactly `Path'Length` digests consumed, every index below n, no duplicate index, k = 0 rejected, each as a postcondition or a status tied to its cause.
- **Root reconstruction**: a ghost model stating that every computed node is H of its two children, each child either computed (on a path) or taken from the proof in order (left then right, i from n - 1 down to 1), and that the root compared is node 1 of that model. If this proof does not close within the budget after two iterations with the author, it falls back to Silver plus the negative vectors of [ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md), and this record is amended to say so, as a temporary state.
- **Geometry**: the inequalities of Section 4.2.1 as postconditions of the constructor, and every row and column index the verifier uses proved in range from them, so that the proof-length checks of the reference become proved preconditions on the records.
- **Lagrange table**: structural Gold against the formula of `lagrange_matrix` restricted to the queried columns (ADR 0036); the interpolation property is tested.
- **The four tests**: structural Gold against the formulas of Sections 4.4 and 4.5 in the reference's order, with `axpy`, `vaxpy`, `dot`, `dot1` as ghost references transcribing `algebra/blas.rs`: the LDT combination `y_ldt = T[ILDT] + sum u_ldt[i] T[IW + i]` at the queried columns, the linear combination with the per-row encodings of the constraint vector, the sum check `dot1 (linear_poly [NREQ .. NREQ + WR)) + dot (b, alphal) = 0`, the quadratic combination `z - x y` per row times u_quad. Equalities stated with `Same` (ADR 0023).
- **Run-length reader**: Gold on the rules of Section 7.4 (first run full field, alternation, zero-length run only first and once, exact count, run length bound).
- **Silver with proved shape**: the Ligero verifier and the complete verifier, whose statuses are tied to the failed test where the structure allows (ADR 0039). Soundness is the paper's theorem and out of scope.

## Alternatives considered

- **Gold on the verdict** ("accept implies the witness satisfies the constraints with high probability"). Not a SPARK statement; the paper's theorem, trusted.
- **Silver only on the tests, with vectors.** Rejected: the vectors exercise one geometry; a swapped row index for another geometry would pass them.
- **Gold on Merkle through a ghost tree built from the leaves.** Not available to the verifier, which has k leaves only; the model above is what it can state.

## Consequences

- The ghost references of `blas.rs` are the project's written form of the tests, readable against the reference line by line.
- A fallback rule exists for one proof, recorded in advance so that it is a decision and not a silent weakening.

## Verification impact

- Provable: the properties above, on both instances; absence of run-time errors everywhere.
- Tested: the interpolation property, the Merkle vectors of Appendix B.1 and the tier 2 trees, the upstream recordings of tier 3, the two complete proofs of Appendix B.3, the negative cases ([ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md)).
- Trusted: the soundness of the protocol; SHA-256 beyond its vectors (ADR 0029); the field laws (ADR 0023).
- Constant time: not applicable (ADR 0037).

## References

- draft-google-cfrg-libzk-03, Sections 4.1.2, 4.1.4, 4.2.1, 4.4, 4.5, 7.4.
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/merkle.rs`, `ligero/common.rs`, `ligero/verifier.rs`, `ligero/proof.rs`, `algebra/blas.rs`.
- [ADR 0023](0023-gold-perimeter-for-protocol-code.md), [ADR 0031](0031-transcript-gold-perimeter.md), [ADR 0035](0035-stage-5-scope-ligero-and-the-complete-verifier.md), [ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md).
