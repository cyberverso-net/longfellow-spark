# 0068 The release build without run-time checks in the proved units

## Status

Proposed (2026-10-22, milestone M2 of Phase D).

## Date

2026-10-22

## Context

The command-line programs (`cli/longfellow_verify.gpr`) were built at `-O2` with every run-time check on. The checks were a second barrier behind the proof: the proof says that no check can fail, and the check would stop the program if the proof were wrong.

ADR 0067 asks how far the Gold code goes. Three builds of the same commit (f6eee9e) were measured on the proving machine, v7 mDoc, three runs each, the median in seconds:

| Build | Hash prove | Hash verify | Signature prove | Signature verify | Round trip |
|---|---|---|---|---|---|
| `-O2`, every check | 11.91 | 6.45 | 6.23 | 2.80 | 27.4 |
| `-O3 -gnatn`, every check | 12.32 | 6.89 | 5.30 | 2.44 | 27.0 |
| as above, no checks in `src/` | 11.35 | 5.86 | 3.59 | 1.68 | 22.5 |

The proofs were identical byte for byte in all nine runs, and the spread between runs was under 1%.

The checks cost most in the loops of P-256 over word arrays, where they stop the compiler from unrolling. On the author's laptop (ARM) the three builds were within noise of each other. On x86 they are not.

At `-O3` the compiler also removes the finalisation of the big integers that ignored ghost code leaves behind. At `-O2` that costs P-256's `Add` 17 of its 38 ns.

## Decision

- **The default release build is `proved`.**
  - `-O3 -gnatn` everywhere.
  - `-gnatp`, no run-time checks, in the units of `src/`. Every one of them is SPARK, and GNATprove proves that none of their checks can fail (the Silver level, for all inputs).
  - The units of `cli/src/` keep their checks: the command-line programs, the random source, and the instances of the prover made for the command line. They are outside the proof.
- **The other two builds stay available** through `LONGFELLOW_CLI_BUILD`: `o2`, the build before this record, and `o3`. They are used for comparison and for diagnosis.
- **The obligation at the boundary.** A proof of absence of run-time errors holds under the preconditions of the unit. Without checks, a caller outside the proof that breaks a precondition no longer meets an exception. It meets undefined behaviour. So every call from `cli/src/` into `src/` must establish the callee's precondition in code:
  - `Circuit_Reader.Read`: the buffer starts at 0 (`Read_File`).
  - `Zk_Verifier.Verify`: the label fits the transcript, `Valid (Cfg)`, the public inputs and the proof start at 0.
  - `Zk_Prover.Prove`: the label fits the transcript, `Config_Fits (Cfg, C)`, at least one input, the inputs and the buffer start at 0, the buffer has `Max_Proof_Len` bytes.
  - The two programs check each of these before the call. The length of the label is now checked too (`label too long`), although no argument of a command line comes near the limit.
  - `interop_kat` is a test harness. It calls the same entry points with the upstream vectors, under the same obligation.
- **The instances of the prover for the command line** take `Cli_Random.Fill` as the formal `Fill` of `Sampling`. The generic body is proved for its instances in `src/`. Those proofs assume that `Fill` sets the whole buffer (`B` is `out`) and touches no state that the prover reads. `Cli_Random.Fill` keeps that assumption: it changes only the state of its own generator. The instances and `Cli_Random` stay compiled with checks.

## Alternatives considered

- **Keep every check.** That would keep the second barrier, at 18% of the round trip and 42% of the signature proof. The proof of absence of run-time errors is complete and is the project's first claim, so the barrier adds little that the proof does not give.
- **Suppress checks in the hot units only** (`P256_Field`, `GF2_128`, `Clmul64`, `Sha256`). That gains most of the speed. But it draws a line by profile, not by trust, and the line would move with every optimisation.
- **Suppress checks everywhere, the command line included.** Rejected: the units of `cli/src/` are not proved.

## Consequences

- `cli/longfellow_verify.gpr` gains the build kinds, with `proved` as the default and one object directory per kind.
- `make check` runs `interop_kat` and the byte identity of the prover on the `proved` build, the build that is delivered.
- The trust model states, under what is trusted, that the release build relies on the proof of absence of run-time errors instead of checking at run time, and lists the boundary obligations.
- Constant time is unaffected. The checks that go away branch only on values that the proof bounds.

## Verification impact

- None on the proofs. The release build changes, the proofs do not.
- The proof of absence of run-time errors for `src/` becomes a premise of the delivered binary, not only a property of the source.

## References

- [ADR 0006](0006-constant-time-discipline-and-scope.md), [ADR 0046](0046-phase-b-scope-lfc2-loader-and-interop.md), [ADR 0067](0067-performance-milestones-by-trust.md).
- GNAT User's Guide, `-gnatp` (suppress all checks); SPARK User's Guide, Absence of Run-Time Errors.
