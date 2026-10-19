# 0054 Prove job limit raised to sixty minutes

## Status

Accepted (2026-10-19, after the merge of Phase C)

## Date

2026-10-19

## Context

The `prove` workflow runs the proof as a matrix of partitions, one job each, under a job limit of forty-five minutes ([ADR 0021](0021-proof-on-pull-requests.md), kept by [ADR 0033](0033-parallel-proof-partitions.md) and [ADR 0045](0045-proof-gate-restored-through-partitions.md)). Phase C added the partition `prover` ([ADR 0049](0049-phase-c-scope-the-prover.md)), which at the close of the phase holds 4591 of the project's 16 671 checks: the writers, the sumcheck prover, the Ligero prover and the composed prover, two instances each. On the pull request that merged the phase (number 16, 2026-10-19) seven partitions passed on the hosted runner in 8 to 41 minutes (`verifier` the longest at 41) and `prove (prover)` was stopped by the limit at 45 minutes 16 seconds, reported by GitHub as cancelled. Branch protection at that date required `verify` only, so the merge went through; ADR 0045 requires every `prove` check, and the `prover` partition was to be added to the required checks with the phase.

ADR 0021 foresaw the case: "if the hosted runner proves slower than estimated, the 45-minute job limit is raised, not the required check removed".

## Decision

- The job limit of `prove` is sixty minutes (`timeout-minutes: 60` in `.github/workflows/prove.yml`). Nothing else in the workflow changes: the triggers, the eight partitions, the reports, the concurrency group.
- The partitions stay as they are. Splitting `prover` into two (the writers and the sumcheck prover; the Ligero prover and the composed prover) is the next step if a partition approaches the new limit, recorded here as the alternative not taken yet.
- Branch protection on `main` is to require `verify` and the eight `prove (<partition>)` checks, `prove (prover)` included, as ADR 0045 decided; at the date of this record it requires `verify` only, which this record states so that the gap is closed and not forgotten.

## Alternatives considered

- **Splitting the `prover` partition now.** Not taken yet: a ninth partition costs a ninth job, a ninth required check and a README change, for a limit that one job exceeded by sixteen seconds; the split is ready to be made when a job approaches sixty minutes.
- **Removing the requirement on `prove (prover)`.** Rejected by ADR 0021 in advance: the proof that gates a merge is the hosted one, and the partition that was too slow is the one that holds the new units.
- **A self-hosted runner.** Still deferred, as in ADR 0019 and ADR 0021.

## Consequences

- A pull request may wait up to an hour for `prove`; locally the whole proof takes about an hour inside `make check` ([chapter 7](../guide/07-prover.md)), so the two are now of a size.
- The README's continuous integration section states the limit and that the eight checks are required.

## Verification impact

Nothing changes in what is proved, tested or trusted. What changes is the time the hosted runner is allowed to re-establish the proof of the heaviest partition.

## References

- `.github/workflows/prove.yml`; the run of pull request 16, 2026-10-19 (jobs `prove (prover)` 45:16 cancelled, `prove (verifier)` 40:26, the others 8 to 19 minutes).
- [ADR 0018](0018-continuous-verification-gate.md), [ADR 0021](0021-proof-on-pull-requests.md), [ADR 0033](0033-parallel-proof-partitions.md), [ADR 0045](0045-proof-gate-restored-through-partitions.md), [ADR 0049](0049-phase-c-scope-the-prover.md).
