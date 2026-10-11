# 0020 Prover configuration by step budget

## Status

Accepted

## Date

2026-10-11

## Context

[ADR 0003](0003-proof-policy-and-trust-model.md) set the prover configuration as `gnatprove --level=2 --report=all`. `--level=2` is a preset: the provers CVC5, Z3 and Alt-Ergo, `--timeout=5` and `--steps=0`. A time limit makes the outcome depend on the machine. The first run of the hosted gate of [ADR 0018](0018-continuous-verification-gate.md) on an Ubuntu runner left five checks unproved with "provers reached time limit" that the author's machine proves in under five seconds: the postconditions of `Lemma_Shift_1`, `Lemma_Shift_2` and `Sub`, an assertion in `Lemma_Shift_3`, a predicate check in `From_Bytes`. The GNATprove user's guide states that `--level` is not reproducible across machines and recommends `--steps` for shared repositories.

Commit ef6122e moved the configuration into `package Prove` of the project file as the same three provers with `--steps=600000 --timeout=0`. That run never terminated: on the runner it was cancelled at the job limit, and on the author's machine two Alt-Ergo processes on goals of `Lemma_Solinas` ran for over seven hours at full CPU without reaching their step bound. Commit 3ad273e added `--timeout=20` as a safety net, four times the longest successful attempt then observed.

An experiment on 2026-10-11 (GNATprove 16.1.0, ten cores, `-j0`, every run from `gnatprove --clean`) measured the alternatives:

| run | provers | timeout | outcome | wall time |
|-----|---------|---------|---------|-----------|
| a | CVC5, Z3 | 0 | stopped by hand after 21 minutes: Z3 at full CPU on `Lemma_Split` (20 min) and `Lemma_Word_Split` (17 min), CVC5 on `Lemma_Regroup` (14 min), none at its step bound | over 21 min |
| a2 | CVC5, Z3 | 20 s | 15 checks unproved (8 assertions, 7 contracts) | 200 s |
| c | CVC5, Z3, Alt-Ergo | 20 s | all 3694 checks proved, max steps 429702 | 134 s |
| b | CVC5, Z3, Alt-Ergo | 120 s | all 3694 checks proved, max steps 429702 | 353 s |
| final | CVC5, Z3, Alt-Ergo | 120 s | `make prove` on the committed configuration: all 3694 checks proved, max steps 429702, longest successful attempt 10 s | 425 s |

Three facts follow. Alt-Ergo is necessary: the fifteen checks of run a2 are closed by no other prover (all in `p256_field.adb`: lines 40 and 41 in `Lemma_Sub128`, 93 in `Lemma_Add128`, 130 and 137 in `Lemma_Mul_Split`, 171 in `Lemma_Add_Step`, 422 in `Lemma_Row_Step`, 692 in `Product`, 923 in `Lemma_Word_Split`, 946 in `Lemma_Word_Sum`, the loop invariant at 969 in `Lemma_Word_Term`, 1046 and 1060 in `Term`, 1171 in `Lemma_Regroup`, 1194 in `Lemma_Solinas_Identity`; polynomial normalisation steps and the bridges between modular words and the integer model). The step budget alone is not a termination guarantee for any of the three provers: GNATprove maps 600000 steps to `rlimit 480450000` for Z3 and `--rlimit=21015000` for CVC5, and on a goal they cannot close both run for tens of minutes without reaching it; the attribution to Alt-Ergo in commit 3ad273e was incomplete. The longest successful attempt is 4 seconds on this machine in runs b and c and 10 seconds in the final run (the predicate check of `From_Bytes` at `p256_field.adb:1722`, an assertion of `Product`, the postcondition of `Sub` at `p256_field.ads:222`); the spread comes from the fifteen goals on which CVC5 and Z3 burn their whole timeout at full CPU while the other cores prove. The timeout of 20 seconds therefore left a factor of two to five here and below one on a hosted runner three to seven times slower, which is the regime in which the level 2 preset had already failed.

The per-prover percentages in the summary table are not a stable measurement: with `-j0` the first prover to answer is credited, and CVC5 and Z3 swap most of the checks between one run and the next (CVC5 86 per cent of the functional contracts in one run, Z3 88 per cent in another). Only the set of checks that need Alt-Ergo is meaningful.

## Decision

- The prover configuration is stated once, in `package Prove` of `longfellow_spark.gpr`:

  ```
  --prover=cvc5,z3,altergo --steps=600000 --timeout=120 --memlimit=1000 --report=all
  ```

  A plain `gnatprove -P longfellow_spark.gpr` and `scripts/check.sh prove` (which adds only `-j0 --checks-as-errors=on`) prove the same thing with the same bounds.
- The step budget is the bound. 600000 is about forty per cent above the 429702 steps of the hardest proof observed; a proof that fits it on one machine fits it on every machine with the same toolchain. Raising the budget is a recorded decision, as raising the level was under ADR 0003.
- The timeout is a guard against runs that do not terminate, not a bound. 120 seconds is twelve to thirty times the longest successful attempt on the author's machine and about two to ten times on a hosted runner three to seven times slower. A check reported as "time limit" therefore means a prover that could not close the goal, not a slow proof; if that margin is ever consumed, the proof is restructured, not the timeout raised.
- All three provers stay. Alt-Ergo closes fifteen checks that CVC5 and Z3 do not.
- `gnatprove` is pinned exactly (`gnatprove = "=16.1.0"` in `alire.toml`), because proof outcomes depend on the prover versions it bundles. Alire's lock file is not tracked (commit a5a4cf1): it stores the origin already resolved for the platform it was written on, a macOS arm64 archive, so committing it would make a Linux runner deploy the wrong binary; the exact version in the manifest is the pin.

## Alternatives considered

- **`--level=2` as before.** Rejected: its five-second timeout ties the result to the speed and load of the machine; the hosted runner turned the gate red with no change to the code or the toolchain.
- **A higher level.** Rejected: a higher level raises the timeout and adds provers, with the same dependence on the machine, and every proof already fits level 2's provers under a step budget.
- **Per-unit switches.** Rejected: nothing needs them, and a single configuration keeps "proved" meaning one thing across the project.
- **Session replay (`--replay`).** Rejected for now: replay reports every check without a recorded proof as unproved, so each code change would require regenerated sessions committed with it, and sessions are tied to the GNATprove version. It changes the workflow more than it saves.
- **CVC5 and Z3 only, no timeout.** Tried and rejected: fifteen checks unproved, and the run does not terminate.
- **Keeping `--timeout=20`.** Rejected: on a hosted runner the timeout, not the step budget, would be the binding limit for the slowest proofs.
- **`--timeout=300`.** Not run: the margin would be seventy-five times locally, but each of the fifteen checks that only Alt-Ergo closes costs CVC5 and Z3 the whole timeout first, so the local run would approach twelve minutes for no change in what is proved.

## Consequences

- The outcome of the proof is deterministic for a given prover version and input, up to the step budget; the machine affects only the wall time.
- Wall time rises from 134 to 353 and 425 seconds locally, and in proportion on the hosted runner, because CVC5 and Z3 spend the whole timeout on each of the fifteen checks before Alt-Ergo gets them, and those attempts also slow the proofs running on the other cores. This is the price of a timeout that never binds; it is paid only on checks a prover cannot close.
- A future check that proves only near the timeout is a signal to restructure the proof (smaller context, a lemma), not to raise the timeout; see the lessons in chapter 2 of the guide.
- The ten-core figure of 4 to 10 seconds for the longest successful attempt is the reference for the next measurement; a toolchain upgrade re-establishes it.

## Verification impact

- Provable: nothing new. What "proved" means changes in one respect: a check is proved if some prover of the set closes it within 600000 steps; the result is reproducible for the pinned toolchain on any machine on which that work takes less than 120 seconds.
- Tested: no change.
- Trusted: the three provers, as before ([ADR 0003](0003-proof-policy-and-trust-model.md)); the step accounting of each prover as a bound on the work done.
- Constant time: no effect.

## References

- `package Prove` in `longfellow_spark.gpr`, `scripts/check.sh`, `alire.toml`.
- The measurements above: runs a, a2, b, c of 2026-10-11, reports kept in the project notes.
- Commits ef6122e (step budget, `--timeout=0`) and 3ad273e (`--timeout=20`); a5a4cf1 (lock file untracked).
- GNATprove user's guide, "How to run GNATprove", on `--level`, `--steps`, `--timeout` and the recommendation of `--steps` for shared repositories.
- [ADR 0003](0003-proof-policy-and-trust-model.md), [ADR 0018](0018-continuous-verification-gate.md), [ADR 0019](0019-proof-off-the-hosted-gate.md).
