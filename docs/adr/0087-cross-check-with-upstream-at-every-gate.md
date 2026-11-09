# 0087 The cross-check of the mDoc proofs with upstream's verifier at every gate

## Status

Proposed (2026-11-09, with #142; to be accepted at its merge).

## Date

2026-11-09

## Context

The exit criterion of the mDoc layer ([ADR 0058](0058-mdoc-layer.md), block 5; #65, criterion 1) is interoperability: a proof made by `longfellow_prove_mdoc` is accepted by upstream's `run_mdoc_verifier`. The gate of the project (`make check`, [ADR 0041](0041-verification-cadence.md) and [ADR 0044](0044-field-contracts-at-proof-only-level.md)) could not run that check: upstream's verifier is Rust code outside the repository, and the gate had neither cargo nor a copy of upstream. Block 5 therefore delivered `tests/vectors/upstream/verify_mdoc.rs`, an example for upstream's runtime crate at the pin d5e6be7 that reads a proof file and calls `run_mdoc_verifier_inner` under the parameters of the test case, to be run by hand with cargo; the run of 8 and 9 November 2026 is recorded in #65 and in chapter 9, Section 5.1.

A check by hand is evidence of one day. The code it checks changes at every block of Phase D (the witness from the credential, #66, changes what the prover reads but must not change what the verifier accepts), and a check that is not in the gate can drift from the code without anyone noticing. The proving machine, where every gate runs, already holds cargo and a clone of upstream for the measurement series of the performance page ([ADR 0060](0060-proving-machine-on-google-cloud.md), `docs/guide/performance.md`); nothing new has to be installed there.

## Decision

The cross-check is a step of `make check`, the last of the `cli` step: `scripts/cross-check-upstream.sh`, after `scripts/measure-mdoc.sh mdoc` has written the two mDoc proofs and the altered copy under `cli/out/`.

- The script takes the clone of upstream from `LONGFELLOW_UPSTREAM`, makes a shared working copy at the pin under a cache directory that persists between runs (`LONGFELLOW_CROSS_CHECK_DIR`, by default `~/.cache/longfellow-spark/cross-check`), copies `tests/vectors/upstream/verify_mdoc.rs` into the crate's examples and builds it with cargo. The reference clone is never built in or written to. Only the first run pays the build of upstream's crate.
- It runs the example on the version 7 and the version 6 proof, which must both be accepted (exit 0), and on the copy of the version 6 proof with one tag altered, which must be refused; otherwise the step, and the gate, fail.
- Where `LONGFELLOW_UPSTREAM` is not set, the step prints that it was skipped and why, and exits 0. This is the case of the hosted `verify` workflow and of a laptop without a clone of upstream. The gate's record therefore says which machine ran the check: the status `prove` of the proving machine, whose `make check` runs are launched by `scripts/remote-check.sh` with `LONGFELLOW_UPSTREAM` set to the machine's clone.

The commands by hand stay documented (the header of `verify_mdoc.rs`, `tests/vectors/upstream/README.md`) as the way for anyone to reproduce the check.

## Alternatives considered

- **Keep the check by hand.** The evidence would be the maintainer's word on a date; the check could drift from the code. Rejected.
- **Run it in the hosted `verify` workflow too.** The runner would install a Rust toolchain and clone and build upstream's crate at every run, several minutes on a job that takes a few, and a second toolchain to pin in the workflow. The proving machine runs `make check` on every pull request anyway, so the check runs at every gate without that cost. Rejected for now; the skip line keeps the record honest where it does not run.
- **Instrument upstream's prover instead.** ADR 0058 rejected a Rust helper in the prover's path; the verifier's path is the one that states interoperability, and the example instruments nothing: it calls upstream's public function on a file.
- **Pin a prebuilt `verify_mdoc` binary.** A binary nobody can read is not evidence; the source in the repository, built from upstream at the pin, is.

## Consequences

- `make check` on the proving machine depends on cargo and on a clone of upstream containing d5e6be7. Both are part of the machine's setup, now recorded in `scripts/remote-check.sh`; a machine without them skips the step and says so.
- The first gate after this change builds upstream's runtime crate on the proving machine, a few minutes once; later gates reuse the build.
- `tests/vectors/upstream/verify_mdoc.rs` is gate code: a change to it changes what the gate checks, which the rule for `--text-only` already treats as code (it is under `tests/`).
- The pin of upstream stays d5e6be7 (the README; [ADR 0048](0048-circuit-vectors-and-interop-proofs.md) for the interop files); a move of the pin changes the constant of the script with the rest.

## Verification impact

No Ada changes, no contract, no proof. The step adds one check to `make check` whose failure fails the gate: a proof of this project refused by upstream's verifier, or an altered proof accepted by it.

## References

- #65, #142; chapter 9, Section 5.1; `tests/vectors/upstream/README.md`.
- `scripts/cross-check-upstream.sh`, `scripts/check.sh` (the `cli` step), `scripts/remote-check.sh`.
- ADR 0041 and ADR 0044 (`make check` as the gate), ADR 0058 (the mDoc layer), ADR 0060 and ADR 0062 (the proving machine and the status `prove`).
