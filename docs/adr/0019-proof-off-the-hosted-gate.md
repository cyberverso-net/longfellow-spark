# 0019 Proof off the hosted gate

## Status

Accepted. Amended 2026-10-11 by [ADR 0021](0021-proof-on-pull-requests.md): the proof is again a required check on pull requests to `main`. Amended 2026-10-15 by [ADR 0033](0033-parallel-proof-partitions.md): the hosted proof runs as a matrix of partitions. Amended 2026-10-16 by [ADR 0041](0041-verification-cadence.md): the pre-push hook is withdrawn and the proof gate is `make check` by hand.

## Date

2026-10-11

## Context

[ADR 0018](0018-continuous-verification-gate.md) put the full proof on the hosted runner for every push and pull request, and set ten minutes as the job duration beyond which the cost would be reconsidered. The first three complete runs on the hosted Ubuntu runner measured the cost:

| run | Prove step | whole job |
|-----|------------|-----------|
| push, 2026-10-10 22:09 UTC | 14.5 min | 18 min |
| pull request, 2026-10-10 23:59 UTC | 22.5 min | 29 min |
| push to `main`, 2026-10-11 00:42 UTC | 22 min | 29 min |

The same proof takes about three minutes on the author's machine and on the hosted macOS runner. The remaining steps (build, harnesses, vectors, lint) take three to five minutes. The runner's speed varies by about half between runs, which also eats into the margin of the twenty-second safety timeout that ADR 0018 measured against the author's machine.

The repository is private. The free plan allows 2000 minutes a month on standard runners, with macOS minutes counted ten times; it offers no larger runners. At thirty minutes a push, the proof alone bounds the project to about sixty pushes a month, and the macOS leg on `main` costs about eighty minutes of budget per push.

## Decision

- The hosted gate (`verify`) runs build, both harnesses, the vector comparison and the lint on Ubuntu for every push and pull request. It no longer runs the proof and has no macOS leg. Branch protection requires `verify` only.
- The proof gates each push locally: `.githooks/pre-push` runs `scripts/check.sh prove` before anything leaves the developer's machine, with the same prover configuration and unproved checks treated as errors. `make hooks` installs it (`core.hooksPath`). `git push --no-verify` bypasses it, and that is the point at which discipline replaces the constraint of ADR 0018.
- The proof also runs on the hosted runner as the workflow `prove`, weekly (Monday 03:00 UTC) and on manual dispatch, with the GNATprove report uploaded as an artifact. It is not a required check. It is the independent record that the proof holds on the pinned toolchain, run by hand after a toolchain change or before a release, and it bounds to one week the time an unproved push can go unnoticed if the hook was skipped.
- `scripts/check.sh` remains the single definition of all the checks, and `make check` still runs all of them locally; the definition of done for a commit is unchanged.
- Everything else in ADR 0018 stands: the Alire-provisioned toolchain, the exact pin of `gnatprove`, the prover configuration in `package Prove`, the untracked lock file.

## Alternatives considered

- **Drop the harnesses from the hosted gate instead.** Rejected: they cost three to five minutes of a thirty-minute job and are the only check that exercises the compiled code against the reference vectors; the proof is the cost.
- **Proof on pull requests only, not on every push.** Viable, and the first step back towards ADR 0018 if the weekly run proves insufficient. Not taken now because a pull request still waits twenty to thirty minutes for a result the developer had in three.
- **Replay of recorded proof sessions (`--replay`).** Not taken: replay reports every check without a recorded proof as unproved, so each code change would require regenerated sessions committed with it, and sessions are tied to the GNATprove version. It changes the workflow more than it saves.
- **A self-hosted runner on the author's machine.** The strongest option for restoring the proof to the gate at local speed and no minute cost; deferred because it ties the gate to one machine being on. It is the intended route if the project gains a second contributor or the weekly run is not enough.
- **Larger hosted runners.** Unavailable on the free plan for a private repository.

## Consequences

- An unproved check can reach a branch and, if the hook is skipped, `main`; the weekly run reports it within a week, after merge. ADR 0018 rejected exactly this for being the most expensive point to attribute a regression. It is accepted now as a temporary cost, bounded by the hook and the weekly run.
- The `verify` job takes about five minutes and its badge certifies less than before: build, harnesses, vectors, lint on the pinned toolchain. What it certifies about the proof is nothing; the `prove` badge does that, as of its last run.
- Hosted minutes fall from about thirty per push to about five, plus thirty a week.
- The hook must be installed on every clone (`make hooks`); a fresh clone without it pushes unproved. The README says so where it states the definition of done.
- Returning the proof to the gate is a new record that supersedes this one, expected when a faster runner is available.

## Verification impact

What a green `verify` badge certifies: on the pinned toolchain, the library builds, the harnesses pass all known-answer cases, the committed vectors are exactly what the generators produce, and no tracked file contains forbidden content.

What a green `prove` badge certifies: on the pinned toolchain, at the time of its last scheduled or manual run, every SPARK check of the project was proved within the step budget with no unproved check and no justification. Between runs, the proof of the current `main` rests on the developer's pre-push hook.

- Provable: nothing new; the proof is unchanged, only where and when it runs.
- Tested: the harnesses and vector regeneration on every change, as before.
- Trusted: as ADR 0018, plus the developer's discipline not to bypass the hook.
- Constant time: no effect.

## References

- `.github/workflows/verify.yml`, `.github/workflows/prove.yml`, `.githooks/pre-push`, `Makefile` (`hooks`), `scripts/check.sh`.
- GitHub Actions run durations: the three runs listed in the Context, under the `verify` workflow's history.
- [ADR 0003](0003-proof-policy-and-trust-model.md), [ADR 0018](0018-continuous-verification-gate.md).
