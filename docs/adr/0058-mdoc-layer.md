# 0058 The mDoc layer: MACs, public inputs, transcript, proof format and witness

## Status

Proposed (2026-10-19, block 1 of Phase D; realised in blocks 5 and 6)

## Date

2026-10-19

## Context

A Longfellow proof is accepted by an mDoc verifier only inside the construction of `applications/mdoc_zk`: two proofs, over GF(2^128) for the hash circuit and over P-256 for the signature circuit, bound together by MACs and by a shared transcript, with public inputs built from the requested attributes, the date, the issuer's public key and the transcript; the whole in one byte string (`runtime/src/proto.rs`, `MdocProof::write`: six MACs as little-endian u128, the hash proof, the signature proof). The prover (`runtime/src/prover.rs`, `run_mdoc_prover_inner`) draws `mac_ap` (`generate_mac_ap`), opens `Transcript::new (transcript)`, decompresses the archive, parses the mDoc (`parse_mdoc`), builds the two witnesses (`push_witness_hash`, `push_witness_sig`; concrete and legacy forms for version 7), commits both circuits, draws `av = tp.u128 ()`, computes the MACs (`push_macs`: legacy below version 8, modern from 8), builds the public inputs (`push_input_hash`, `push_input_sig`), proves both and writes the proof. The randomness of production is `SecureRandomEngine`, so byte identity with a production proof is not a possible criterion.

## Decision

- **Block 5, the layer on upstream witnesses.** In SPARK: the proof format, the MACs (legacy for version 7, modern for 8), the public inputs as `push_input_hash` and `push_input_sig` build them, the transcript as `Transcript::new (transcript)` with the two provers' labels, the table of specifications (version, attributes, circuit hashes, configurations, as `zk_spec.rs`). Two tools in `cli/`: `longfellow_prove_mdoc`, from the circuits, the two witnesses, `mac_ap`, the public inputs and the transcript to the mDoc proof; `longfellow_verify_mdoc`, the two `Zk_Verifier` plus the MACs. A Rust helper beside the recorders runs the upstream prover's path on the `age_over_18` test case up to the witnesses and writes witnesses, `mac_ap`, public inputs, transcript and the upstream proof to files; the author runs it with cargo. Criterion: our mDoc proof accepted by `run_mdoc_verifier` upstream; the upstream example proof accepted by `longfellow_verify_mdoc`.
- **Block 6, the witness in Ada.** From the mDoc (CBOR), the issuer's public key, the transcript, the requested attributes and the date: the two witnesses and the MACs, following the concrete and legacy forms of version 7 (`parse_mdoc`, the SHA-256 trace of the MSO, the attribute positions, the ECDSA witness of the issuer's signature, the device key). Criterion of the phase: `longfellow_prove_mdoc` from the test mDoc alone produces a proof accepted by `run_mdoc_verifier`, within the targets of ADR 0055.
- **Constant time.** CBOR parsing depends on the data, and the data is the secret; this record, completed at block 6, says which parts are constant time (the field arithmetic, the hashes over fixed-length buffers, the proof), which are not (the parse of a variable-length document and the search for attribute positions) and why the reference is not either, as [ADR 0051](0051-constant-time-in-the-prover.md) did for the prover.
- **Trust.** The upstream verifier as the arbiter of the format; the upstream test mDoc as the fixture; the mDoc layer's cryptography (MAC construction, ECDSA witness) as specified by the reference's code, since no document of the pinned draft covers it.

## Alternatives considered

- **Instrumenting the production runtime for byte identity.** Not taken unless the author asks: the randomness is the system's; the recorders remain the tool held in reserve, as [ADR 0053](0053-prover-vectors-and-cross-verification.md).
- **Generating the witness in Rust only.** Rejected for the goal: the proof must come from this project alone, from the mDoc.

## Consequences

- New units, a proof partition `mdoc`, chapter 9 (and a chapter 10 for the witness if its size asks for it).
- The trust model gains the mDoc entries; the README documents the two tools.

## Verification impact

- Provable: absence of run-time errors on any byte string for the format and the CBOR parse; the layout of the mDoc proof; the MACs as fixed computations.
- Tested: acceptance upstream; the example proof; the witnesses against the upstream helper's files.
- Trusted: as the Decision says.
- Constant time: as the Decision says, completed at block 6.

## References

- google/longfellow-zk at d5e6be7: `rust/applications/mdoc_zk/runtime/src/{prover,verifier,proto,mac,zk_spec}.rs`, `circuits/src/{cbor,hash,mso_attribute,signature}`, `testcases/src/vectors.rs`, `runtime/tests/all/current_zk.rs`.
- [ADR 0051](0051-constant-time-in-the-prover.md), [ADR 0053](0053-prover-vectors-and-cross-verification.md), [ADR 0055](0055-phase-d-scope-mdoc-scale.md).
