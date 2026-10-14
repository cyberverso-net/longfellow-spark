# 0033 Parallel proof partitions on the hosted runner

## Status

Accepted

## Date

2026-10-15

## Context

The hosted `prove` job of [ADR 0021](0021-proof-on-pull-requests.md) runs the full proof in one job with a limit of forty-five minutes. Its duration has grown with the project: five to nine minutes at stage 2 (3694 checks), twenty-two to twenty-eight at stage 3 (6811 checks), over thirty on the pull request of stage 4 (7810 checks). Stage 5, the Ligero verifier, adds several thousand checks and would cross the limit. Locally the full proof takes about six minutes on eight cores; the hosted runner has four and is slower per core, and the ratio has been fifty per cent or more between runs ([ADR 0018](0018-continuous-verification-gate.md)).

GNATprove proves units independently once the global contracts are generated: `gnatprove -u` analyses the listed units only, and a generic body is proved once per instance, through the instance unit (measured at stage 4: `-u sumcheck_algebra_p256.ads` analyses one unit, 680 checks; a generic unit on its own analyses nothing and, with unproved checks as errors, fails on the warning `generic-not-analyzed`). The phases before proof (data representation, global contracts) run on the whole project in every invocation, a fixed cost of about two minutes locally.

A second, unrelated defect of the proof runs surfaced three times in stage 4: the Why3 session under `obj/` returns stale "unproved" results for unchanged checks without re-running them, and a list of failures taken from such a session is false until the session is cleaned.

## Decision

- The proof on the hosted runner is a matrix of partitions, one job per partition, each running `scripts/check.sh prove-partition <name>`: `gnatprove -P longfellow_spark.gpr -j0 --checks-as-errors=on -u <units>` with the prover configuration of [ADR 0020](0020-prover-configuration-step-budget.md) unchanged. The jobs do not fail fast, keep the limit of forty-five minutes each, share the concurrency group per ref of ADR 0021, and upload one report each (`gnatprove-report-<partition>`). Triggers are unchanged: pull requests to `main`, the weekly schedule, manual dispatch.
- The partitions live in one place, `scripts/prove-partitions.txt`: a name and the units it proves, by unit name. At this date: `p256` (P256_Field, Field_P256), `primitives` (GF2_128, Field_GF2_128, Bytes, Sha256, Aes256, Transcript, Fisher_Yates), `sumcheck` (the four instances of Sumcheck_Algebra and Sumcheck_Expression), `protocol` (the four instances of Sumcheck_Verifier and Sumcheck_Transcript). Generic units are not listed: they are proved through their instances.
- `scripts/check.sh partitions-check` fails unless the union of the lists is exactly the set of non-generic units under `src/` (the specs that do not begin with `generic`), with no unit listed twice. It runs in `verify`, in every `prove` job before the proof, and in `make check`, so a new unit without a partition is caught on every push and locally.
- `make prove` and the pre-push hook keep proving the whole project in one run; the partitions are a property of the hosted runner only.
- Every proof, whole or partition, starts with `gnatprove --clean`, so that no result comes from a stale session.
- Branch protection requires the four checks `prove (p256)`, `prove (primitives)`, `prove (sumcheck)`, `prove (protocol)` in place of `prove`.

Measured locally at the close of stage 4, each from a clean session: `p256` 3656 checks in 357 s, `primitives` 456 in 154 s, `sumcheck` 2213 in 220 s, `protocol` 1485 in 216 s; the sum, 7810, is the count of the full proof. The partition lists are to be rebalanced from measured durations as units are added; `p256` is one unit and cannot be split.

## Alternatives considered

- **Raising the job limit.** Rejected: it buys one stage and makes every pull request wait for the whole proof; the wait was already the cost that ADR 0019 had tried to remove.
- **Caching the Why3 session across runs so that unchanged units are not re-proved.** Rejected: the stale-session failure mode of the Context would become a property of the gate, and a cached "proved" is exactly what a gate must not report; a cache would also hide the duration growth that this record responds to.
- **A self-hosted runner.** Deferred, as in ADR 0019 and ADR 0021; the partitions apply to it as well.
- **Partitioning by hand in the workflow file.** Rejected: the list would drift from `src/` silently; the single file and the completeness check make a missing unit a failure.
- **One job per unit.** Rejected: twenty-two jobs each paying the fixed cost of the first two phases and the toolchain setup; four partitions put the wall time at the heaviest unit, which is the best a per-unit split could do.

## Consequences

- The wall time of the hosted proof is bounded by the heaviest partition plus the setup, about the stage 2 duration for `p256`, instead of growing with the project; hosted minutes grow with the number of partitions (the fixed cost is paid once per job).
- The partitions must be kept complete: `partitions-check` enforces it, and a new unit means editing `scripts/prove-partitions.txt`.
- Four required checks on the pull request instead of one; a failure names the partition.
- The reports are four artifacts; the per-unit counts of a chapter's verification condition table come from the local full run, as before.
- ADR 0019 and ADR 0021 are amended by this record in their Status lines; their decisions otherwise stand.

## Verification impact

Nothing changes in what is proved: the union of the partitions is the whole project, the prover configuration and the treatment of unproved checks are unchanged, and `make prove` still proves everything in one run. A green set of `prove (...)` checks certifies what the single `prove` check certified. Tested: the completeness of the partitions, on every push. Trusted: that GNATprove's per-unit analysis with `-u` proves the same checks as the full run, which the equal counts confirm at this date and the per-unit lines of the reports let a reader confirm later.

## References

- [ADR 0018](0018-continuous-verification-gate.md), [ADR 0019](0019-proof-off-the-hosted-gate.md), [ADR 0020](0020-prover-configuration-step-budget.md), [ADR 0021](0021-proof-on-pull-requests.md).
- `scripts/prove-partitions.txt`, `scripts/check.sh` (`prove-partition`, `partitions-check`), `.github/workflows/prove.yml`.
- SPARK User's Guide, "Running GNATprove from the Command Line" (`-u`) and "Analysing generic units".
