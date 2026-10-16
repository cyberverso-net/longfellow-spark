# 0041 Verification cadence: the proof by hand, the slow harness cases weekly

## Status

Accepted (2026-10-16, after block 4 of stage 5). Amended 2026-10-16 by [ADR 0044](0044-field-contracts-at-proof-only-level.md): the slow set is folded into the default harness run; `make check-full`, `test-slow` and the workflow `full` are removed. Amended 2026-10-16 by [ADR 0045](0045-proof-gate-restored-through-partitions.md): the hosted proof is a required check again, per partition; the hook stays withdrawn.

## Date

2026-10-16

## Context

Two costs grew with stage 5. The proof of the `ligero` partition takes eleven minutes locally with ten provers, so the pre-push hook of [ADR 0019](0019-proof-off-the-hosted-gate.md), which proves the whole project before every push, would hold every push for the better part of an hour; the developer runs `make check` by hand before each commit anyway, so the hook proved what was already proved.

The other cost is in the harnesses. The test build has assertions on ([ADR 0010](0010-assertion-enabled-test-project.md)), so every executable contract runs, and the Gold contracts of `P256_Field` execute their chain of ghost lemmas on big integers: a multiplication costs 38 ms, an inversion 6 s. The Ligero verifier of Appendix B.3.2 makes 29 checked inversions (the denominators of the two Lagrange tables, [ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md)) and about five thousand multiplications: twelve minutes on the author's machine, against seconds on GF(2^128). `make check` went from 20 to 37 minutes; the `verify` job has a 30-minute limit on a slower runner; and block 5 adds the complete verifier end to end on the same proof and the negative cases of [ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md), each a run of the verifier on P-256.

Four options were considered for the P-256 cost: accept it; the batch inversion of ADR 0037's note, which saves three minutes of inversions and nothing of the multiplications; moving the lemma calls of `P256_Field` to a proof-only assertion level, which would make the test build fast but would no longer execute them; a separate, less frequent run of the slow cases. The author chose the last: nothing changes in what the test build executes, and the Linux run of every case is kept, less often.

## Decision

- The pre-push hook is withdrawn: `.githooks/pre-push` and `make hooks` go. The proof that gates a change is `make check`, run by hand before every commit; that is the definition of done, as the README states. The hosted proof (`prove`) keeps its triggers and its informational role ([ADR 0034](0034-proof-as-information-harnesses-in-parallel.md)).
- The harness cases are in two sets. The slow set is what the assertion-enabled build cannot afford on every push: today the P-256 Ligero verifier end to end in `sumcheck_kat`; in block 5 the P-256 complete verifier and the P-256 negative cases. `sumcheck_kat` runs them only with the argument `--slow` and otherwise reports them as skipped; GF(2^128) runs the same cases in the fast set, so that every path of the verifier is exercised on every push.
- `scripts/check.sh test` runs the fast set; `test-slow` runs the harnesses with the slow set; `all` (`make check`) uses the fast set and is the definition of done for a commit; `full` (`make check-full`) uses the slow set and runs before a pull request.
- A third workflow, `full`, runs build, the partitions check, `test-slow`, the vectors and the lint weekly and on manual dispatch, on the runner named by the repository variable `FULL_RUNNER` when set (a larger hosted runner, for its faster CPU: the harnesses are single-threaded) and on `ubuntu-latest` otherwise, with a limit of 180 minutes. `verify` is unchanged in its steps and keeps its place as the only required check.

## Alternatives considered

- **Keeping the hook and proving only the partition touched.** Rejected: which partition a change touches is not what a hook can decide, and a partial proof before a push is a false comfort.
- **The lemma calls of `P256_Field` at a proof-only level.** Not chosen now: it is the fastest option and it costs the proofs nothing, but it changes what the test build executes (ADR 0010, ADR 0014), and the author prefers to keep the executed contracts whole and move the cost in time rather than in content. It remains the fallback if the weekly run outgrows its runner.
- **The batch inversion.** Insufficient alone (three of twelve minutes); kept in the notes.
- **Removing the P-256 end-to-end run from the hosted checks altogether.** Rejected: the Linux run of every case on the pinned toolchain is what the badges certify.

## Consequences

- A push is proved only if the developer ran `make check`; the hosted `prove` on the pull request and the weekly runs are the net, as ADR 0034 already had it, with the hook no longer part of the net.
- `verify` stays within its limit: the fast set is bounded by `sumcheck_kat` without its slow cases, a few minutes.
- The slow set is run weekly and before each pull request (`make check-full`), so a regression on the P-256 end-to-end path is caught before merge by the developer and within a week by the runner.
- The README's definition of done, continuous integration section and branch model change accordingly; ADR 0019, 0021 and 0034 are amended in their Status lines.

## Verification impact

Nothing changes in what is proved or in what the harnesses check; what changes is when the slow cases run. Trusted: that the developer runs `make check` before every commit and `make check-full` before every pull request.

## References

- [ADR 0010](0010-assertion-enabled-test-project.md), [ADR 0019](0019-proof-off-the-hosted-gate.md), [ADR 0021](0021-proof-on-pull-requests.md), [ADR 0034](0034-proof-as-information-harnesses-in-parallel.md), [ADR 0037](0037-checked-inv-and-public-data-scope.md), [ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md).
- `scripts/check.sh` (`test`, `test-slow`, `all`, `full`), `Makefile`, `.github/workflows/full.yml`, `tests/src/sumcheck_kat.adb` (`--slow`).
