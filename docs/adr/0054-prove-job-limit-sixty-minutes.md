# 0054 Prove job limit raised to sixty minutes and the prover partition split

## Status

Accepted (2026-10-19, after the merge of Phase C). Amended 2026-10-19 by [ADR 0060](0060-proving-machine-on-google-cloud.md): the proof runs as one job on the project's own machine; the partitions remain for local use.

## Date

2026-10-19

## Context

The `prove` workflow runs the proof as a matrix of partitions, one job each, under a job limit of forty-five minutes ([ADR 0021](0021-proof-on-pull-requests.md), kept by [ADR 0033](0033-parallel-proof-partitions.md) and [ADR 0045](0045-proof-gate-restored-through-partitions.md)). Phase C added the partition `prover` ([ADR 0049](0049-phase-c-scope-the-prover.md)), which at the close of the phase holds 4591 of the project's 16 671 checks: the writers, the sumcheck prover, the Ligero prover and the composed prover, two instances each. On the pull request that merged the phase (number 16, 2026-10-19) seven partitions passed on the hosted runner in 8 to 41 minutes (`verifier` the longest at 41) and `prove (prover)` was stopped by the limit at 45 minutes 16 seconds, reported by GitHub as cancelled. Branch protection at that date required `verify` only, so the merge went through; ADR 0045 requires every `prove` check, and the `prover` partition was to be added to the required checks with the phase.

ADR 0021 foresaw the case: "if the hosted runner proves slower than estimated, the 45-minute job limit is raised, not the required check removed".

The first version of this record raised the limit to sixty minutes and left the partitions as they were. The run of the pull request that carried it (number 18, 2026-10-19) showed that this was not enough: `prove (prover)` was stopped at 60 minutes 17 seconds, and `prove (verifier)` took 49 minutes, the other six 5 to 17. The hosted runner is two to three times slower than the author's machine on these jobs.

## Decision

- The job limit of `prove` is sixty minutes (`timeout-minutes: 60` in `.github/workflows/prove.yml`).
- The `prover` partition is split in two: `prover` keeps the writers, the sumcheck prover, `Sampling`, `Simple_Rng` and `Prover_Status` (about 2300 checks), and the new partition `ligero-prover` holds the Ligero prover and the composed prover (`Ligero_Prover`, `Zk_Prover`, two instances each, about 2270). Nine partitions in `scripts/prove-partitions.txt` and in the matrix of the workflow; `make partitions-check` keeps them covering the project.
- Nothing else in the workflow changes: the triggers, the reports, the concurrency group.
- Branch protection on `main` is to require `verify` and the nine `prove (<partition>)` checks, `prove (prover)` and `prove (ligero-prover)` included, as ADR 0045 decided; at the date of this record it requires `verify` only, which this record states so that the gap is closed and not forgotten.

## Alternatives considered

- **Raising the limit alone.** Tried first in this record and refuted by the run of pull request 18: the partition exceeded sixty minutes as well. Raising further (ninety minutes) would leave `verifier` and `prover` near the limit and growing with Phase D.
- **Splitting `verifier` too.** Not now: forty-nine minutes leaves a margin of eleven; it is the next split if that margin closes.
- **Removing the requirement on `prove (prover)`.** Rejected by ADR 0021 in advance: the proof that gates a merge is the hosted one, and the partition that was too slow is the one that holds the new units.
- **A self-hosted runner.** Still deferred, as in ADR 0019 and ADR 0021.

## Consequences

- A pull request may wait up to an hour for `prove`; locally the whole proof takes about an hour inside `make check` ([chapter 7](../guide/07-prover.md)), so the two are now of a size.
- The README's continuous integration section states the limit, the nine partitions and that the nine checks are required; chapter 7's verification condition table gives the two partitions' counts.

## Verification impact

Nothing changes in what is proved, tested or trusted. What changes is the time the hosted runner is allowed to re-establish the proof of the heaviest partition.

## References

- `.github/workflows/prove.yml`, `scripts/prove-partitions.txt`; the run of pull request 16, 2026-10-19 (jobs `prove (prover)` 45:16 cancelled, `prove (verifier)` 40:26, the others 8 to 19 minutes) and the first run of pull request 18 (`prove (prover)` 60:17 cancelled, `prove (verifier)` 48:58).
- [ADR 0018](0018-continuous-verification-gate.md), [ADR 0021](0021-proof-on-pull-requests.md), [ADR 0033](0033-parallel-proof-partitions.md), [ADR 0045](0045-proof-gate-restored-through-partitions.md), [ADR 0049](0049-phase-c-scope-the-prover.md).
