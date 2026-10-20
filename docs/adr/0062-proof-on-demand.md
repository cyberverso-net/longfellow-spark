# 0062 The proof on demand, posted as a commit status

## Status

Accepted

## Date

2026-10-19

## Context

[ADR 0060](0060-proving-machine-on-google-cloud.md) moved the proof to a machine of the project's own, driven by GitHub Actions. A hosted job started the virtual machine, and a self-hosted runner on it ran the proof on every pull request. Its first day showed three problems.

- **Contention.** Every push to a pull request started a proof on the one machine. Two proofs at once share the cores, and under that load the prover timeout of 120 seconds becomes the binding limit. Checks that pass on an idle machine then fail.
- **Waste.** Text-only changes and intermediate pushes each cost a full run, unless the workflow learns to tell code from text.
- **Exposure.** A self-hosted runner that executes the pull requests of a public repository can run someone else's code on the project's machine.

[ADR 0041](0041-verification-cadence.md) had made the developer's `make check` the gate. With a machine of our own, the developer can run that check there, on the exact commit, and leave the result where GitHub can see it.

## Decision

- **The proof leaves the workflows.** `prove.yml`, the self-hosted runner and its shutdown hook are withdrawn. `verify` stays as it is, on hosted runners, on every push and pull request.
- **`scripts/remote-check.sh` runs the proof on demand.** It requires a clean working tree whose commit is on GitHub. The machine fetches that commit into its own clone and runs `make check` there. The script then posts the result on the commit as the status `prove`: pending while it runs, then success or failure with the failing step. The run is detached on the machine, so the developer's laptop may sleep or lose the network: the machine keeps the log and the exit code on its disk and shuts itself down when done. The script checks once a minute, starts the machine again only to read the result if it has stopped, and then posts the status. `--collect` picks up a run whose script was closed. A run that disappears, for example because the machine was stopped under it, is posted as an error.
- **Text-only changes.** `scripts/remote-check.sh --text-only` checks that only Markdown files and `LICENSE` changed since a commit already proved: the nearest ancestor whose status `prove` is success, or else `main`. It then posts `prove` as passed, naming that commit, without starting the machine. A branch that closes a block with a text-only commit after a proved one needs no second proof.
- **Iteration.** `scripts/remote-check.sh --tree` copies the working tree as it is and runs any make target there, posting nothing. It is for a result before a push.
- **The gate.** Branch protection requires `verify` and `prove` on `main`. At the end of a block the developer commits, pushes, opens the pull request and runs the script once. A red check is shown with its diagnosis before any code or contract changes, and the fix is a new commit, never an amend or a rebase.
- **One run at a time.** The developer runs the script, so two proofs never share the machine, and the script refuses to start a run while another is in progress there. `make check` may still run on the developer's own machine whenever useful.

## Alternatives considered

- **The proof in the workflows, skipping text-only changes.** The first form of this record. It keeps an independent run on every pull request, but it keeps the contention between pushes and the self-hosted runner's exposure, for a project with two people who decide when a proof is worth running.
- **`make check` on the laptop before every commit.** The rule of ADR 0041. It leaves the laptop unusable for over an hour and records nothing on the commit.

## Consequences

- ADR 0041 and ADR 0060 are amended in their Status lines. The README's sections on building and on continuous integration change, and the `prove` badge goes.
- The `prove` status is posted by the developer's account. It certifies that the script ran `make check` on that commit on the proving machine; the log stays with the developer, as `remote-check.log`.
- There is no weekly run any more. Before a release, or after a change of toolchain, the developer runs the script on `main`.
- The runner is removed from the machine and from the repository. The service account and the Workload Identity Federation pool are no longer used; they can be deleted later.
- A branch may carry fix commits after its pull request is opened. The merge into `main` is what is guaranteed green.

## Verification impact

Nothing changes in what is proved, tested or trusted about the code. Trusted, as before ADR 0060: that the developer ran the check the status reports. The status is now tied to the exact commit, which the earlier rule did not record.

## References

- [ADR 0041](0041-verification-cadence.md), [ADR 0045](0045-proof-gate-restored-through-partitions.md), [ADR 0060](0060-proving-machine-on-google-cloud.md).
- `scripts/remote-check.sh`, `.github/workflows/verify.yml`, `scripts/check.sh`.
- GitHub REST API, commit statuses (`POST /repos/{owner}/{repo}/statuses/{sha}`).
