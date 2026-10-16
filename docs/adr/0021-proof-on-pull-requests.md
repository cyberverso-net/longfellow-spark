# 0021 Proof on pull requests to main

## Status

Accepted; amended by [ADR 0033](0033-parallel-proof-partitions.md) on 2026-10-15 (the `prove` job is a matrix of partitions) and by [ADR 0034](0034-proof-as-information-harnesses-in-parallel.md) on 2026-10-15 (the proof still runs on pull requests but is no longer a required check). Amended by [ADR 0041](0041-verification-cadence.md) (2026-10-16): the pre-push hook is withdrawn; the proof gate is `make check` by hand.

## Date

2026-10-11

## Context

[ADR 0019](0019-proof-off-the-hosted-gate.md) took the proof off the hosted gate because it cost fifteen to twenty-three minutes of a thirty-minute job on every push, against a budget of 2000 hosted minutes a month for a private repository, and left it to the local pre-push hook on every push and to a weekly hosted run. Its first consequence was accepted as a temporary cost: an unproved check could reach `main` if the hook was skipped, and be reported up to a week later, after merge.

The cost analysis changes when the unit is the pull request rather than the push. Work reaches `main` in one pull request per stage or block, a few a month. [ADR 0020](0020-prover-configuration-step-budget.md) raised the prover timeout to 120 seconds; the proof now takes about six minutes locally and an estimated twenty-five to forty on the four-core hosted runner, because the fifteen checks that only Alt-Ergo closes cost CVC5 and Z3 the whole timeout first. At forty minutes per pull request and a few pull requests a month, the proof on pull requests costs a small fraction of the budget. Pushes to branches, which are many, stay with the hook.

## Decision

- The workflow `prove` runs on every pull request to `main`, in addition to the weekly schedule and manual dispatch. It is a required check for merging, alongside `verify`.
- Pushes to branches do not run it; the pre-push hook of ADR 0019 proves them locally before they leave the developer's machine.
- `prove` has a concurrency group per ref with cancellation of the run in progress, so a pull request updated twice runs the proof once. Its job limit stays at 45 minutes.
- Everything else in ADR 0019 stands: `verify` without the proof on every push, the hook, the weekly run, the single definition of the checks in `scripts/check.sh`.

## Alternatives considered

- **Leaving the gate as in ADR 0019.** Rejected: the week between an unproved merge and its detection was the one consequence of 0019 that ADR 0018 had rejected as the most expensive point to attribute a regression; at the pull-request cadence the cost of closing it is small.
- **Proof on every push again.** Rejected for the reasons of ADR 0019: the budget, and twenty-five to forty minutes of waiting for a result the developer has in six.
- **A self-hosted runner.** Still the route to proving every push at local speed; deferred as in ADR 0019.

## Consequences

- Merging to `main` is again conditioned on the proof, run on the pinned toolchain by a machine other than the developer's.
- The hook remains the fast path: a branch is proved locally at every push, and the pull request confirms it once.
- The weekly run remains the independent record between pull requests.
- A pull request waits twenty-five to forty minutes for `prove`. If the hosted runner proves slower than estimated, the 45-minute job limit is raised, not the required check removed.
- Branch protection on `main` requires the checks `verify` and `prove`, the job names of the two workflows.

## Verification impact

What a green `prove` check on a pull request certifies: on the pinned toolchain, every SPARK check of the project is proved within the step budget of ADR 0020 with no unproved check and no justification, for the merge commit of that pull request. Between pull requests, the weekly run certifies the same for `main` as of its last run.

- Provable: nothing new; the proof is unchanged, and it is re-established by the hosted runner at every pull request.
- Tested: no change.
- Trusted: as ADR 0019, with the developer's discipline on the hook now covering only the branch between pushes, not the merge.
- Constant time: no effect.

## References

- `.github/workflows/prove.yml`, `.github/workflows/verify.yml`, `.githooks/pre-push`.
- Run durations of the `verify` workflow with the proof, 2026-10-10 and 2026-10-11, in the Context of ADR 0019; local measurements in ADR 0020.
- [ADR 0018](0018-continuous-verification-gate.md), [ADR 0019](0019-proof-off-the-hosted-gate.md), [ADR 0020](0020-prover-configuration-step-budget.md).
