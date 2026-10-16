# 0035 Stage 5 scope: Ligero and the complete verifier

## Status

Accepted (2026-10-15, before block 2 of stage 5)

## Date

2026-10-15

## Context

Stages 3 and 4 leave the verifier one step short of a verdict: the symbolic core emits a constraint system (A, b) and quadratic triples over the committed witness ([ADR 0022](0022-stage-3-scope-and-challenges-as-input.md)), and the transcript replays every challenge the core consumed ([ADR 0028](0028-stage-4-scope-and-challenge-replay.md)). What checks those constraints against the commitment is the Ligero verifier of draft Section 4; what reads a complete proof string is Section 7.5; what composes the three is `ZkVerifier::verify` of the reference (`docs/specs/rust/src/zk/verifier.rs` at d5e6be7). Phase A ends when a proof string of Appendix B.3 is accepted end to end on both fields.

The reference verifier is self-contained: `ligero/common.rs` (configuration, geometry, the four challenge generators), `merkle.rs` (heap construction, batch opening, batch verification), `ligero/reed_solomon.rs` with `algebra/interpolation.rs` (the Lagrange matrix), `algebra/blas.rs` (`axpy`, `vaxpy`, `dot`, `dot1`), `ligero/verifier.rs` (the four tests), `ligero/proof.rs` (the run-length coded reader of Section 7.4), `zk/proof.rs` (the reader of Section 7.5). Its configuration for the Appendix B.3 vectors is RATE_INV 4, NREQ 6, NCOL 64 (`unit_tests.rs`); the profile of Section 5.1 for real use is NREQ 132 and rate 7, so the implementation must scale beyond the vectors.

## Decision

Stage 5 is the Ligero verifier and the complete verifier, following the reference at d5e6be7:

- **Merkle** (Section 4.1): heap construction of 4.1.2 (an array of 2 n digests, leaves at n .. 2 n - 1, node i the hash of nodes 2 i and 2 i + 1 from n - 1 down to 1, root at 1), and batch proof verification of 4.1.4 (the nodes on the paths from the k leaves to the root are recomputed; a child not on a path is taken from the proof, in the order left then right for i from n - 1 down to 1; exactly the whole path must be consumed; an index at or above n, a duplicate index and k = 0 are rejected; n = 1 has its root equal to its leaf). Batch opening of 4.1.3 is implemented in test code only, to generate vectors.
- **Geometry** (Sections 4.2, 4.3): `LigeroGeometry::new` with every constraint of 4.2.1 (BLOCK = (NCOL + 1) / (2 + RATE_INV) > 0, DBLOCK = 2 BLOCK - 1 <= NCOL, NCOL - DBLOCK >= NREQ, BLOCK > NREQ, WR = BLOCK - NREQ > 0) and the row indices of 4.3 (ILDT 0, IDOT 1, IQD 2, IW 3, the quadratic rows x, y, z after the NWROW witness rows; NROW = 3 + NWROW + 3 NQT). For B.3.2: BLOCK 10, DBLOCK 19, WR 4, NW 29, NQ 2, NWROW 8, NQT 1, NROW 14, 45 committed columns; verified against `LigeroGeometry::new`. The configuration (RATE_INV, NREQ, NCOL) is an input of the verifier, not a constant: the vectors use (4, 6, 64) and the reference's default is (4, 16, 256).
- **Reed-Solomon** by Lagrange interpolation ([ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md)).
- **The Ligero verifier** of 4.5, in the reference's order: `write_bytes` of the statement hash; the geometry; the length checks (queried columns NROW times NREQ; polynomials of BLOCK, DBLOCK, NREQ and DBLOCK - BLOCK elements; NREQ nonces); the challenges u_ldt (NQW = NROW - 3 draws), alphal (one per linear constraint, b'Length), alphaq (three per quadratic triple), u_quad (one per quadratic row), in that order; the four polynomials absorbed as element slices; `choose (NCOL - DBLOCK, NREQ)` for the column indices; then `verify_merkle` (leaf i: the nonce followed by the NROW elements of the opened column in their full-field encoding, hashed), `verify_ldt`, `verify_dot` with the sum check, `verify_quad`, each as in the reference, with `axpy`, `vaxpy`, `dot`, `dot1` as the vocabulary.
- **The Ligero proof reader** of 7.4: the four polynomials, the NREQ nonces of 32 bytes, the run-length coded opened columns (4-byte little-endian sizes; runs alternate, full field first; a zero-length run only as the very first run, never two consecutive; the elements of a subfield run in the subfield encoding of 7.2.2, 2 bytes on the basis for GF(2^128), the field's own encoding for P-256; exactly NROW times NREQ elements, a run that overshoots is an error; a run longer than 2^25 elements rejected, the draft's bound, which the reference does not enforce), then a 4-byte count of path digests of 32 bytes.
- **The ZK proof reader** of 7.5: the root (32 bytes), the sumcheck part (stage 4 reader), the Ligero part; no trailing bytes.
- **The complete verifier**, `ZkVerifier.verify`: the public input count checked; the transcript reset from the label; the root absorbed; the statement; the core's challenges replayed (stage 4) and the core run (stage 3) for A, b and the quadratic triples (`generate_lqc_triples`: triple j at the pad offset of layer j plus 4 logw, three consecutive variables); nw = (ninput - npublic) + the sum over layers of 4 logw + 3; the Ligero verifier with the fixed `DEFAULT_STATEMENT_HASH` (the four bytes 0xde 0xad 0xbe 0xef then 28 zero bytes), which the reference hard-codes because the root, the public inputs and the sumcheck transcript have already been absorbed.

Out of scope: the prover and the commitment (phase C); the additive FFT of the draft (ADR 0036); the GF(2^16) subfield beyond the evaluation points of the code and the byte decoding that the run-length reader needs; the subfield boundary SF of the commitment, which the verifier never sees.

## Alternatives considered

- **The Ligero verifier without the complete verifier**, leaving the composition to phase B. Rejected: the composition is thirty lines and the only point where a verdict exists; without it the B.3 vectors cannot be accepted end to end.
- **A configurable statement hash.** Rejected: the reference fixes it, the vectors depend on it, and the draft's argument (everything statement-specific is already in the transcript) makes it a constant.
- **The circuit loader (LFC2) before Ligero.** Rejected for this stage: the explicit circuits of Appendix B.3 are in memory and suffice for the vectors; the loader brings with it the memory redesign for large circuits, a phase B concern that Ligero's own sizes raise anyway ([ADR 0039](0039-sizes-allocation-and-status.md)).

## Consequences

- Phase A is complete at the end of this stage: a verifier of Longfellow ZK from the proof string to a verdict, on the explicit circuits, with the draft's vectors accepted on both fields.
- The transcript of stage 4 continues after `alpha_input` as ADR 0028 foresaw; `Choose` and `Write_Element_Slice` are used at the sizes of Ligero, which [ADR 0039](0039-sizes-allocation-and-status.md) addresses.
- `Inv` enters the verification path for the first time ([ADR 0037](0037-checked-inv-and-public-data-scope.md)).
- The README trust model gains the entries of ADR 0037, 0038 and 0040 and records Phase A as complete.

## Verification impact

- Provable: the Gold perimeter of [ADR 0038](0038-gold-perimeter-for-merkle-and-ligero.md); absence of run-time errors and termination on every subprogram of the stage.
- Tested: the vectors of [ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md), including the two complete proofs of Appendix B.3 accepted end to end.
- Trusted: the soundness of Ligero and of the composition, the paper's theorem, which no contract states; the statement hash convention of the reference.
- Constant time: not applicable to the units of this stage (ADR 0037).

## References

- draft-google-cfrg-libzk-03, Sections 4.1 to 4.5, 5.1, 7.4, 7.5; Appendix B.1, B.3.
- google/longfellow-zk at d5e6be7, `docs/specs/rust/src/`: `ligero/common.rs`, `ligero/verifier.rs`, `ligero/proof.rs`, `ligero/reed_solomon.rs`, `merkle.rs`, `algebra/interpolation.rs`, `algebra/blas.rs`, `zk/verifier.rs`, `zk/common.rs`, `zk/proof.rs`; `tests/unit_tests.rs` (the configuration of the B.3 vectors).
- [ADR 0022](0022-stage-3-scope-and-challenges-as-input.md), [ADR 0028](0028-stage-4-scope-and-challenge-replay.md), [ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md) to [ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md).
