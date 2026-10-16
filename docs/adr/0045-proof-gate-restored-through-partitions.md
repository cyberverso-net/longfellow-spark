# 0045 Proof gate restored through partitions

## Status

Accepted (2026-10-16, consolidation after Phase A)

## Date

2026-10-16

## Context

The proof has moved on and off the hosted gate as its cost changed. [ADR 0018](0018-continuous-verification-gate.md) put it on every push; [ADR 0019](0019-proof-off-the-hosted-gate.md) took it off when a run cost twenty to thirty minutes and left it to a pre-push hook and a weekly run; [ADR 0021](0021-proof-on-pull-requests.md) made it a required check on pull requests; [ADR 0033](0033-parallel-proof-partitions.md) split it into a matrix of partitions so that the wall time is that of the heaviest; [ADR 0034](0034-proof-as-information-harnesses-in-parallel.md) made the partition checks informational, because a single developer who proves every push through the hook gains nothing from waiting for the hosted repetition; [ADR 0041](0041-verification-cadence.md) withdrew the hook, since a full local proof had grown to about thirty-six minutes and the developer runs `make check` by hand before every commit anyway.

With the hook gone, the hosted proof is the only proof not run by the developer's own hand, and nothing requires it to be green before a merge. The matrix of ADR 0033 has six partitions; the heaviest took about twelve minutes on the hosted runner at the close of stage 4, and the two partitions of stage 5 take under three and twelve minutes locally with ten provers ([ADR 0043](0043-exhausted-status-and-streaming-slice.md), chapter 5). Pull requests come a few times a month, one per stage or block. Waiting twelve minutes a few times a month for an independent proof is not the cost that ADR 0034 removed; the cost then was waiting on every merge for what the hook had just established on every push.

## Decision

- The six `prove` checks are required for merging again, one status per partition, alongside `verify`. Branch protection on `main` requires `verify`, `prove (p256)`, `prove (primitives)`, `prove (sumcheck)`, `prove (protocol)`, `prove (ligero)` and `prove (verifier)`, the job names of the two workflows.
- The `prove` workflow keeps its triggers (pull requests to `main`, the weekly schedule, manual dispatch), its partitions, its reports and its job limit of forty-five minutes.
- The pre-push hook stays withdrawn. The local rule of ADR 0041 stands: `make check` by hand before every commit, which proves the whole project in one run. The hosted proof is the independent confirmation on the pinned toolchain, now required before the merge rather than read after it.
- When a partition grows past its limit, the partitions are rebalanced (ADR 0033), not the requirement removed.

## Alternatives considered

- **Leaving the proof informational, as ADR 0034.** Rejected: without the hook, an unproved commit reaches `main` whenever the developer forgets `make check` once, and the project's claim that every merge is proved would rest on habit alone.
- **A single required `prove` check that aggregates the matrix.** Rejected: a failing partition is named by its own status, and GitHub's required checks are per job name; an aggregating job would add a job for no information.
- **Restoring the hook as well.** Rejected, as ADR 0041: a thirty-six minute hook on every push holds the developer for a proof already run before the commit.

## Consequences

- A pull request waits for its slowest partition before merging, about twelve minutes on the hosted runner at this date.
- ADR 0034 and ADR 0041 are amended in their Status lines; their other decisions stand (the harnesses concurrent, the proof by hand before every commit).
- The README's continuous integration section and branch model say that `verify` and the six `prove` checks are required.

## Verification impact

Nothing changes in what is proved: the same partitions, the same configuration, the same treatment of unproved checks. What changes is that a merge to `main` is again conditioned on the hosted proof. Trusted: the developer's `make check` before every commit, as before, now confirmed by the runner before each merge.

## References

- [ADR 0018](0018-continuous-verification-gate.md), [ADR 0019](0019-proof-off-the-hosted-gate.md), [ADR 0021](0021-proof-on-pull-requests.md), [ADR 0033](0033-parallel-proof-partitions.md), [ADR 0034](0034-proof-as-information-harnesses-in-parallel.md), [ADR 0041](0041-verification-cadence.md).
- `.github/workflows/prove.yml`, `.github/workflows/verify.yml`, `scripts/prove-partitions.txt`.
