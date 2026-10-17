# 0048 Circuit vectors and the upstream interop proofs

## Status

Accepted (2026-10-17, at the close of block 3 of Phase B; proposed 2026-10-16 and edited until then)

## Date

2026-10-16

## Context

Every stage has tested its code against the draft's vectors, an independent reference and recorded upstream runs ([ADR 0009](0009-known-answer-vectors.md), [ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md), [ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md)). The loader of [ADR 0046](0046-phase-b-scope-lfc2-loader-and-interop.md) has no vectors in the draft, since the format is upstream's; what exists is the two upstream circuits with their inputs and proofs under `docs/specs/rust/tests/testdata/` at d5e6be7 (`sha256_circuit.lfc2`, `sha256_inputs.json`, `sha256_proof.bin`, and the same for `ecdsa2`), the labels and configurations in `test_reference.rs`, and the production reader as the definition of the format. The files are binary; every vector of this project so far has been text, generated and compared by `scripts/check.sh vectors`.

## Decision

Vectors come in three tiers, in the notation of ADR 0009, plus negative cases.

- **Tier 1, the upstream files.** The three files of each circuit (the circuit, the inputs, the proof) are copied unchanged into `tests/vectors/upstream/circuits/`, with their SHA-256 and provenance (repository, commit, path, licence Apache-2.0, the same as this project's) in `tests/vectors/upstream/README.md`. Neither circuit has public inputs, so the verifier needs nothing of the inputs files, which are kept for the prover of Phase C; the labels and configurations go into `interop.txt`, one line per case: `interop <name> <field> <circuit file> <proof file> <label> <rate_inv> <nreq> <ncol> <npublic> <public inputs...> <expected status>`. The generator also writes a summary of each upstream circuit as its own LFC2 reader parses it (`circuit_summary.txt`: layer count, per layer `logw`, `nw`, term count, the total, the identifier), for the harness to compare with the SPARK loader.
- **Tier 2, an independent Python reference** (`gen_circuit_vectors.py`): an LFC2 reader and writer written from the production code's rules, NIST-free; the explicit circuits of Appendix B.3 (the term lists `gen_sumcheck_vectors.py` already holds) written in LFC2 with the identifier computed independently, so that the loaded circuit must equal the in-memory circuit of stage 3 term by term and the identifier must match; the same circuits written in a second valid encoding (one segment per term, no deduplication) to show the reader accepts any valid encoding; and the malformed cases, each with its status: a wrong magic, a wrong field identifier, `ncopies` 2, each bound exceeded, a constant index, a delta index and a token out of range, a non-canonical constant on P-256, a truncated file at each section, trailing bytes, a wrong identifier, a wire index out of its layer's range, `nw` above `2^logw`, a last layer whose width is not `ninput`.
- **Tier 3, the interop proofs.** The two upstream proofs verified end to end by `Zk_Verifier.Verify` on the loaded circuits, under the circuit's identifier, the label and the configuration of the upstream test, with no public inputs; then the proof with one byte altered in its root, in its sumcheck part and in its Ligero part, each refused. The harness builds the three copies; the status of each refusal, observed at the first run (`Merkle_Failed` in all six cases: every altered byte is absorbed by the transcript and moves the chosen columns), is recorded in `interop.txt` and checked from then on, so that a regression that changes the status while still refusing the proof is seen. Recordings of the upstream verifier's intermediate values, as ADR 0027 and ADR 0040 made them, are not produced in advance: the proofs are accepted or they are not, and a recording is the tool to localise a divergence if one appears.
- **Harnesses.** `circuit_kat` runs tiers 1 and 2 and the negative cases through the loader, in the assertion-enabled test project, with the other harnesses of `scripts/check.sh test`. `interop_kat` runs tier 3 through the loader and the verifier, reading the binary files; it lives in the release project `cli/` with the command-line verifier of ADR 0046, built without assertions, and runs in the step `scripts/check.sh cli`, which also runs the command-line verifier on the two proofs and checks its exit status. Both harnesses fail on any case and when no case ran.

## Alternatives considered

- **Converting the binary files to hexadecimal text**, as the Appendix B.3 proofs were. Rejected: the loader's input is a file, and a hex transcription would be one more artefact to keep equal to the original; the SHA-256 in the README pins the copies.
- **Generating more circuits with the upstream compiler.** Deferred: the two shipped circuits cover both fields, the subfield boundary, twelve and eleven layers; an mDoc circuit for the scale of ADR 0047 is an experiment outside the repository until Phase C has a prover to make proofs for it.
- **Recording the upstream verifier on the two proofs in advance.** Not taken, as above: the recordings of stages 3 and 5 exist because the intermediate values had to be matched step by step on circuits with known term lists; here the verdict is the criterion and the recording tool stays available.
- **Running `interop_kat` in the assertion-enabled test project.** Not taken: with assertions on, the postconditions of stage 3 quantify over the positions of the stored pairs and the `Expression` of the input constraint is quadratic in the private inputs, so one run on the 6657 inputs of `sha256` was stopped after thirty-five minutes against 1.3 seconds in the release build. The release project is where the verdict on real data is tested, on the binary code the project delivers.
- **Moving the stage 3 postconditions to the proof-only level**, as [ADR 0044](0044-field-contracts-at-proof-only-level.md) did for the fields, so that the interop run could keep assertions on. Not taken: it would lose exactly the execution of those contracts on the Appendix B.3 circuits in `sumcheck_kat`, which is what the test build is for; if it becomes necessary it is a record of its own.

## Consequences

- `tests/vectors/upstream/circuits/` holds the first binary files of the repository, pinned by hash; `tests/vectors/` gains `inputs_*.txt`, `interop.txt`, `circuit_summary.txt`, `circuit_lfc2.txt` (tier 2) and the generator.
- Two harnesses and the command-line verifier join `check.sh`; the test step stays within seconds on the loader cases and is measured on the two end-to-end runs.
- The README trust model moves "the loader agrees with the upstream format" to tested, and gains the interop entry: the two upstream proofs accepted.
- A limit of coverage, stated: the contracts of stage 3 are proved for all inputs, and their execution at run time is exercised on the Appendix B.3 circuits of `sumcheck_kat` only, not on the real circuits; the end-to-end verification on real data is a test of the verdict, not of the contracts.

## Verification impact

- Provable: nothing; vectors are tests.
- Tested: the format against an independent reference and the upstream files; the identifier against upstream's; the loaded circuits against the in-memory ones; the verifier against the upstream prover's output, end to end, on both fields.
- Trusted: that the four upstream files are what d5e6be7 ships (pinned by SHA-256); that the upstream prover's proofs are valid, which its own tests assert.
- Constant time: no effect.

## References

- google/longfellow-zk at d5e6be7: `docs/specs/rust/tests/testdata/`, `docs/specs/rust/tests/test_reference.rs` (labels, configurations, the input parsing), `rust/core/proto/src/reader/lfc2.rs`.
- [ADR 0009](0009-known-answer-vectors.md), [ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md), [ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md), [ADR 0046](0046-phase-b-scope-lfc2-loader-and-interop.md), [ADR 0047](0047-heap-allocation-by-ownership.md).
