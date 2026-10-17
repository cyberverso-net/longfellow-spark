# 0053 Prover vectors and cross-verification

## Status

Proposed (2026-10-17, block 1 of Phase C)

## Date

2026-10-17

## Context

The verifier's vectors came from the draft, from independent references and from recorded upstream runs ([ADR 0009](0009-known-answer-vectors.md), [ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md), [ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md), [ADR 0048](0048-circuit-vectors-and-interop-proofs.md)). For the prover the strongest vector is already in the repository: the two upstream proof files are the output of the upstream prover on the shipped circuits and inputs with a known generator and known seeds (`tests/test_reference.rs`), so a prover that consumes randomness as the reference does must reproduce them byte for byte. The Appendix B.3 proofs of the draft cannot serve the same way: the draft does not say which randomness produced them.

## Decision

Vectors in three tiers, in the notation of ADR 0009, plus the negative cases and a cross-verification outside the CI.

- **Tier 1, the upstream proof files as expected bytes.** `prover_kat` runs the prover on `sha256_circuit.lfc2` with `sha256_inputs.json` and `Simple_Rng (12345)` under the label `sha256_spec_test` and the configuration rate 3, 16 queries, 256 columns, and on `ecdsa2` with seed 123456789, `ecdsa2_spec_test`, rate 4, 16, 256; the bytes must equal `sha256_proof.bin` and `ecdsa2_proof.bin`. The harness reports the first differing offset and which section of the proof it falls in (root, sumcheck part, Ligero part, which polynomial, nonce, column or path digest), so that a divergence localises itself without a recording.
- **Tier 2, an independent Python reference** (`gen_prover_vectors.py`, built on the field arithmetic, the Merkle tree, the Lagrange matrix and the transcript already written for earlier generators): the writers (every proof of the repository, the two of Appendix B.3 and the two upstream files, read by the verifier's readers and rewritten identical, in `writer.txt` for the harness `writer_kat` of the test project); the subfield projection (the sixteen masks of ADR 0051 derived from the basis and checked on every subfield element, written as a vector for `gf2_128_kat`); and, since the pieces exist, a complete prover for small circuits: the Appendix B.3 circuits with chosen seeds, the proof bytes to compare with the SPARK prover's, and the intermediate values (the pads, the tableau rows before encoding, the root) as lines for `prover_kat`. Where this reference and the SPARK prover disagree, one of them is wrong and the lines say where.
- **Tier 3, recordings of the upstream prover's intermediates** on the Appendix B.3 circuits, with the recorders of `tests/vectors/upstream/` extended to the prover: produced only if tier 1 shows a divergence that tier 2 does not localise. The format follows ADR 0027.
- **Negative cases**, each with its status: inputs of the wrong length (`Input_Length`), inputs that do not satisfy the circuit (`Not_Satisfied`: an output not zero, a Z assertion violated), a private input below the subfield boundary outside GF(2^16) on GF(2^128) (`Not_In_Subfield`, which the Python reference of tier 2 exercises too), a configuration that violates Section 4.2.1 or does not fit (`Config_Invalid`); and a proof from false inputs that `Zk_Verifier` must refuse, produced by a prover instance that skips the satisfiability check. That instance exists in the harness only, through a generic parameter or a test procedure of the test project, and is not reachable from `longfellow_prove`.
- **Other seeds, both verifiers.** `prover_kat` also proves each upstream circuit with another seed and checks the proof with `Zk_Verifier` (and `scripts/check.sh cli` with `longfellow_verify`); the proof files are written under `cli/out/`, ignored by git, for the cross-verification. A Rust test, `tests/vectors/upstream/verify_proof_file.rs`, kept beside the recorders with its instructions in the README there, loads the circuit, reads a proof file produced by this project with a seed other than the test's, and verifies it with the upstream `ZkVerifier` under the same label and configuration; the author runs it with `cargo`, outside the CI, at the close of block 5 and after any change to the prover.

## Alternatives considered

- **Only the byte identity.** Rejected: a divergence in the bytes says little about where; tier 2 says where, on circuits small enough to read.
- **Running the upstream verifier in the CI.** Rejected: a Rust toolchain on the runner for one test; the recordings have the same arrangement (ADR 0027).
- **Recording the upstream prover in advance.** Not taken: tier 1 is exact and tier 2 is independent; the recorder is the tool held in reserve.

## Consequences

- `tests/vectors/` gains `gen_prover_vectors.py`, `prover.txt` (tier 2 lines), the projection masks in `gf2_128_bytes.txt` or a file of their own, and the harness `prover_kat` (release project, as `interop_kat`, since it runs the prover on the upstream circuits); `tests/vectors/upstream/` gains the Rust test.
- The README trust model lists the two upstream proofs as reproduced byte for byte, and the acceptance of this project's proofs by the upstream verifier as tested by hand.

## Verification impact

- Provable: nothing; vectors are tests.
- Tested: byte identity with upstream on both fields; the writers' round trips on every proof file; the projection on every subfield element; the small-circuit prover against an independent reference; acceptance by both verifiers; every status by a negative case.
- Trusted: that `Simple_Rng` is the upstream test's generator (confirmed by the identity); the upstream verifier's verdict on the cross-verification, run by hand.
- Constant time: no effect.

## References

- google/longfellow-zk at d5e6be7: `docs/specs/rust/tests/test_reference.rs` (`SimpleRng`, `run_reference_test_helper`), `docs/specs/rust/tests/testdata/`.
- [ADR 0009](0009-known-answer-vectors.md), [ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md), [ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md), [ADR 0048](0048-circuit-vectors-and-interop-proofs.md), [ADR 0049](0049-phase-c-scope-the-prover.md), [ADR 0050](0050-randomness-as-a-byte-stream.md), [ADR 0051](0051-constant-time-in-the-prover.md).
