# 0010 Test project compiling the library with assertions

## Status

Accepted

## Date

2026-10-08 (retroactive record, written 2026-10-09)

## Context

Known-answer tests should exercise not only the executable code but also the contracts: with assertions enabled, every call to `Mul` evaluates its postcondition, so `Mul_Ref` runs on the same inputs and a disagreement between code, contract and vector is detected at the point where it happens. In GNAT project files compiler switches apply only to the sources of the project that declares them, so a test project that merely depends on the library project would compile the library with the library's switches and leave its contracts inert.

## Decision

- `tests/longfellow_spark_tests.gpr` is a standalone executable project whose source directories are `tests/src` and `../src`: it compiles the library sources itself, with `-gnata` (assertions enabled), the same style checks as the library, and no optimisation.
- The harness `tests/src/gf2_128_kat.adb` is `SPARK_Mode (Off)` and is declared in the README as test code outside the proof perimeter. It reads the vector files with `Ada.Text_IO`, reports pass and fail counts and sets a non-zero exit status on any failure or when no case ran.
- Binaries built from `tests/` are declared not constant time (assertions execute ghost code, see [0006](0006-constant-time-discipline-and-scope.md)) and must never be measured or deployed.

## Alternatives considered

- Depend on the library project (`with "../longfellow_spark.gpr"`) and rely on the Alire validation profile for assertions. Rejected: the harness build would then depend on how the library was last built, and the point of the test build (contracts on) would be invisible in the project file.
- Write the harness in SPARK. Rejected: file parsing and reporting gain nothing from proof and would cost effort; the harness is not in the trust model.
- Call `Mul_Ref` directly from the harness. Not possible: ghost entities cannot be referenced from non-ghost code; the postcondition already runs it.

## Consequences

- Two builds of the same sources exist: the library build (constant time by discipline, assertions off in release) and the test build (assertions on). The README names both.
- The test build is slow by design: `Mul_Ref` runs inside every loop iteration of `Mul` (the loop invariant is an assertion); 209 cases take about two seconds at stage 1. Later stages may need a profile that keeps postconditions and drops loop invariants at run time.
- `tests/obj` and `tests/bin` are ignored by git.

## Verification impact

- Provable: nothing; the harness is outside SPARK.
- Tested: library contracts and ghost code execute on every vector; a postcondition violation is reported as a failure with the vector line.
- Trusted: nothing additional.
- Constant time: the test binary is explicitly excluded from the guarantee.

## References

- `tests/longfellow_spark_tests.gpr`, `tests/src/gf2_128_kat.adb`.
- README, "Testing".
- [0009](0009-known-answer-vectors.md).
