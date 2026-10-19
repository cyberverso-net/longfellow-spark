# 0062 The pull request checks as the gate

## Status

Accepted

## Date

2026-10-19

## Context

[ADR 0041](0041-verification-cadence.md) made `make check`, run by the developer before every commit, the gate for every change. At the time the hosted proof was only a safety net.

Since [ADR 0060](0060-proving-machine-on-google-cloud.md) that net is the whole check. On every pull request, `verify` runs every step of `make check` except the proof, and `prove` runs the full proof on the project's own machine, with the pinned toolchain. Together they certify what `make check` certifies.

Running `make check` before the commit as well now costs twice and buys nothing. On the author's laptop it takes over an hour and leaves the machine unusable. On the proving machine it competes for the same cores as the `prove` job. Under that contention the prover timeout of 120 seconds becomes the binding limit, and checks that pass on an idle machine fail. That happened to one assertion of `Ligero_Prover` in Phase C.

## Decision

- **The gate is the pull request.** At the end of a block the developer commits, pushes and opens the pull request. `verify` and `prove` must both be green before the merge, and branch protection requires both.
- **A red check is handled as before.** The unproved check is shown with its diagnosis and discussed before any code or contract changes. The fix is a new commit on the branch, never an amend or a rebase.
- **Text-only changes** (README, guide, records, changelog) need only the lint and a check of the links before the pull request.
- **`make check` stays the definition of what is checked.** `scripts/check.sh` still defines the steps, and the workflows run them. The developer may run `make check` on their own machine whenever useful, in parallel with the pull request checks.
- **`scripts/remote-check.sh` runs only when the proving machine is free.** It is meant for a result before a push, for example while iterating on a hard proof. It must not run while a `prove` job is running on the same machine.

## Alternatives considered

- **Keep `make check` before every commit.** Rejected: it repeats the pull request checks, at the cost of the laptop for an hour or of contention on the proving machine.
- **Run the remote check in parallel with the `prove` job.** Rejected: both slow down, and the timeouts make the result unreliable.

## Consequences

- ADR 0041 and ADR 0060 are amended in their Status lines.
- A commit on a branch is no longer guaranteed green; the merge into `main` is. A branch may carry fix commits after its pull request is opened.
- The README's definition of done and branch model change accordingly.
- `prove` also runs for text-only pull requests and for every push to an open pull request. That costs a run of the proving machine each time. Making the job pass quickly when only text files changed is left for a later change.
- Every push to a pull request starts a `prove` job, so a remote check should not run while any pull request is being updated.

## Verification impact

Nothing changes in what is proved, tested or trusted. What changes is where and when the checks run before a merge.

## References

- [ADR 0041](0041-verification-cadence.md), [ADR 0045](0045-proof-gate-restored-through-partitions.md), [ADR 0060](0060-proving-machine-on-google-cloud.md).
- `.github/workflows/verify.yml`, `.github/workflows/prove.yml`, `scripts/check.sh`, `scripts/remote-check.sh`.
