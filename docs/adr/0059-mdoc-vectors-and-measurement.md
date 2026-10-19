# 0059 mDoc vectors, witness inputs and measurement

## Status

Proposed (2026-10-19, block 1 of Phase D)

## Date

2026-10-19

## Context

The production artifacts (`rust/applications/mdoc_zk/artifacts/` at d5e6be7) are the data of the phase: the circuit archives, one example mDoc proof and two witness files per archive. The archives are zstd streams of LFA2 archives (`rust/core/proto/src/archive`), a format this project did not have; the witness files are the circuits' inputs as raw little-endian field elements, public inputs first, 16 and 32 bytes each (their sizes are exactly `ninput` elements); the example proofs are in the mDoc format of ADR 0058.

## Decision

- **Copied and pinned** under `tests/vectors/upstream/mdoc/`, with SHA-256 and provenance in the README there: the version 7 and version 6 archives with one attribute, their example proofs and their four witness files, and the four decompressed LFC2 payloads (`<hash>_hash.lfc2`, `<hash>_sig.lfc2`), so that the harnesses and the command-line tools read circuits without a decompressor.
- **The extractor** `gen_mdoc_vectors.py` parses the LFA2 format independently (magic, version byte, circuit version, combined identifier equal to the SHA-256 of the entries' identifiers, four strings, entries), checks the committed payloads against the archives when a zstd decompressor is available (the standard library module `compression.zstd` of Python 3.14 and later, or the `zstd` command) and checks the committed payloads alone otherwise, parses each circuit with the independent LFC2 reader of `gen_circuit_vectors.py`, checks its identifier against the archive's, and writes `mdoc_summary.txt` in the format of `circuit_summary.txt`; `circuit_kat` loads the four circuits (82 cases) as a third default file.
- **Witness inputs.** `longfellow_prove` gains `--inputs-bin FILE`, the witness file format (raw little-endian elements, `ninput` of them), beside the JSON format; the mDoc tools of ADR 0058 read the same files. No JSON copies of the witnesses are committed (2.6 MB each).
- **Measurement.** `scripts/measure-mdoc.sh` runs the prover and the verifier on the four circuits with the upstream witnesses under the configurations of `zk_spec.rs`, with time and peak memory, outside `make check`; the numbers of each block are recorded in the session note and in the records that use them. The cross-verification of the bare proofs with the upstream `ZkVerifier` uses `verify_proof_file.rs` of ADR 0053 as it is, on the extracted LFC2 and the witness file converted to JSON, run by the author.

## Alternatives considered

- **Committing only the archives.** Rejected: the CI runner's Python may lack a zstd module and the `zstd` command is not guaranteed; the committed payloads make the harnesses independent of it and the generator checks them when it can.
- **Committing the witnesses as JSON.** Rejected: 5 MB of text for data the binary format carries in 2.8 MB, and a conversion the command-line prover can do itself.

## Consequences

- 4.2 MB of upstream artifacts in the repository, pinned.
- One more default file for `circuit_kat` (36 seconds with assertions on).

## Verification impact

- Tested: the archive format against the production reader on the two archives; the circuits loaded and `Well_Formed`; the identifiers.
- Trusted: the artifacts as what d5e6be7 ships (pinned by hash), and that the witness files are the inputs of the example proofs.

## References

- google/longfellow-zk at d5e6be7: `rust/applications/mdoc_zk/artifacts/src/lib.rs`, `rust/core/proto/src/archive/`, `runtime/src/proto.rs` (`decompress_circuits`).
- [ADR 0048](0048-circuit-vectors-and-interop-proofs.md), [ADR 0053](0053-prover-vectors-and-cross-verification.md), [ADR 0055](0055-phase-d-scope-mdoc-scale.md), [ADR 0058](0058-mdoc-layer.md).
