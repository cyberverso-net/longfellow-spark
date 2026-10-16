# 0034 Proof on pull requests as information; harnesses in parallel

## Status

Accepted. Amended 2026-10-16 by [ADR 0041](0041-verification-cadence.md): the pre-push hook is withdrawn, the proof gate is `make check` by hand, and the harnesses have a slow set run weekly.

## Date

2026-10-15

## Context

With the partitions of [ADR 0033](0033-parallel-proof-partitions.md) the hosted proof took, on its first pull request, 7 minutes for `p256`, 6 for `primitives`, 12 for `sumcheck` and 12 for `protocol`, of which five to six are the fixed cost of a job (runner setup, build, the first two phases of GNATprove). The same pull request showed the other problem: `verify` took 16 minutes on the push and passed its 20-minute limit on the pull request, because its `test` step runs the four harnesses one after the other and two of them had grown: `sumcheck_kat` to about seven minutes locally (the stage 4 replay runs the core twice per recording), `transcript_kat` to about four, the latter for a defect of the code rather than of the gate (a quadratic loop invariant of `Fisher_Yates.Choose` executed by the assertion-enabled build on `choose (65535, 20)`; fixed with a ghost inverse of the array, linear, in the same change).

The repository has one developer, who proves every push locally through the pre-push hook of [ADR 0019](0019-proof-off-the-hosted-gate.md). The hosted proof therefore repeats a proof already made, on another platform; what it adds is independence (Linux, the pinned toolchain, a public record behind the badge) and a net under a skipped hook. [ADR 0021](0021-proof-on-pull-requests.md) made it a required check to close the week between an unproved merge and its detection; for a single developer who always runs the hook that week does not exist, and the required check only makes every merge wait for the slowest partition.

## Decision

- The `prove` workflow keeps its triggers (pull requests to `main`, the weekly schedule, manual dispatch) and its partitions, but its checks are no longer required for merging: branch protection requires `verify` alone. The badge keeps its meaning, the last hosted run of the full proof on the pinned toolchain; a red `prove` on a pull request is read and acted on, not waited for.
- `scripts/check.sh test` runs the four harnesses concurrently, each with its own log printed in a fixed order when all have finished, and fails if any failed; the step lasts as long as the slowest harness. `make check` and `verify` both use it.
- `verify` keeps its place as the required check, with a limit of 30 minutes (the measured sequential run plus margin; the concurrent run is expected under ten).
- Durations are recorded where they are measured, in the README's continuous integration section, and revisited when a stage changes them.

## Alternatives considered

- **Keeping the proof required and raising the limits.** Rejected: it makes every merge wait for the twelve minutes of the slowest partition to learn what the hook already established.
- **Dropping the hosted proof and `verify` altogether, local checks only.** Rejected: the badges are what a reader of a public repository can verify without trusting the author, and the Linux run has found platform-specific artefacts that the author's machine does not show; the cost of keeping them is the runner's time, which is free for a public repository and is not waited on.
- **A matrix of harnesses in `verify`, one job each.** Rejected: four jobs each paying the fixed setup for a step that fits in one job once the harnesses run concurrently.
- **Skipping the second core run of the stage 4 replay in `sumcheck_kat`.** Rejected: the "both ways" comparison of [ADR 0032](0032-transcript-vectors.md) is kept; it costs three minutes in parallel with the other harnesses.

## Consequences

- Merging waits for `verify` only, about eight to ten minutes expected on the hosted runner.
- An unproved check can reach `main` only if the hook was skipped or absent; the hosted proof reports it on the pull request and within a week, as information. The README says so where it states what the badges certify.
- ADR 0021 is amended by this record in its Status line (the proof is no longer a required check); ADR 0033 likewise (its four required checks are not required). Their decisions otherwise stand.
- The harness output is grouped by harness rather than interleaved; a hung harness holds the step until the job limit.

## Verification impact

Nothing changes in what is proved or tested: the hook proves every push, the hosted proof runs the same partitions, the harnesses run the same cases. What changes is which hosted check blocks a merge. Trusted: that the developer runs the hook, which `make hooks` installs and the README states as the definition of done.

## References

- [ADR 0018](0018-continuous-verification-gate.md), [ADR 0019](0019-proof-off-the-hosted-gate.md), [ADR 0021](0021-proof-on-pull-requests.md), [ADR 0033](0033-parallel-proof-partitions.md).
- `scripts/check.sh` (`test`), `.github/workflows/verify.yml`, `.github/workflows/prove.yml`, `src/fisher_yates.adb`.
