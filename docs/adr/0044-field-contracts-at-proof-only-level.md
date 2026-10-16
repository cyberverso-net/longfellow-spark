# 0044 Field contracts at proof-only level

## Status

Accepted (2026-10-16, consolidation after Phase A)

## Date

2026-10-16

## Context

The test project compiles the library with assertions enabled ([ADR 0010](0010-assertion-enabled-test-project.md)), so that every executable contract runs on every vector. For the two field packages that meant executing their Gold contracts: on P-256 the big-integer model of [ADR 0014](0014-p256-functional-specification-and-ghost-model.md) (`To_Int`, the lemmas, the loop invariants of every stage of the Solinas reduction), on GF(2^128) the Horner reference `Mul_Ref` inside the loop invariant of `Mul` ([ADR 0005](0005-mul-ref-as-proof-target.md)). Measured at stage 5: a P-256 multiplication cost 38 ms and an inversion 6.1 s; the Ligero verifier on the Appendix B.3.2 proof took twelve minutes, `p256_kat` three, and the harness set with the P-256 end-to-end cases about forty-five. [ADR 0041](0041-verification-cadence.md) moved those cases to a slow set run weekly, named this change as the fastest option and set it aside to keep the executed contracts whole.

Phase A is complete and the cost has become the shape of the project's cadence: two harness sets, a third workflow, a `make check-full` before each pull request. The question is what the executed field contracts buy. They are proved for all inputs by GNATprove; executing them on a vector re-checks, on that one input, a statement already established for every input. What they add is a guard against the proof and the compiled code disagreeing, which the known-answer vectors guard as well, since a vector compares the compiled result with an external value. Stage 5 already used the project's assertion level `Proof_Only` (`Proof_Levels`, depending on `Static`, never enabled in any build) for the structural contracts of `Lagrange`, `Ligero_Proof` and `Ligero_Verifier`, for the same reason.

## Decision

- The ghost model, the ghost lemmas, the assertions and loop invariants of the body, and every pre- and postcondition that mentions the model, of `P256_Field` are at the assertion level `Proof_Only`: `Ghost => Proof_Only` on the ghost entities, `(Proof_Only => ...)` on the contracts, `pragma Assert (Proof_Only => ...)` and `pragma Loop_Invariant (Proof_Only => ...)` in the body. The type predicate of `Element` (canonical form, [ADR 0015](0015-p256-canonical-form-and-conditional-subtraction.md)) stays executable: it is a four-limb subtraction, and it is what makes an `Element` safe to use; only its postcondition about the model moves. The contracts that do not mention the model (`Select_Limbs`, `From_Bytes`, `To_Bytes`, `Bytes_Of_Limbs`, `Of_Natural`, `Word`) stay executable.
- In `GF2_128`, `Bit`, `Mul_Ref` and `Inject_Ref` are at `Proof_Only`, with the postconditions of `Xtime`, `Mul`, `Square` and `Inject` and the two loop invariants that state them. The postconditions of `Add`, `Sub`, `Neg` and of the byte functions are limb-wise and cost nothing; they stay executable.
- The wrappers `Field_GF2_128` and `Field_P256` are unchanged: `Same` is the vocabulary of the protocol contracts, which stay executable ([ADR 0023](0023-gold-perimeter-for-protocol-code.md)); `Checked_Inv` keeps its postcondition, one multiplication.
- No proof changes: every check of the two packages is proved as before, and the counts are compared before and after.
- The slow set of ADR 0041 is folded into the default: `sumcheck_kat` runs its P-256 cases always, the argument `--slow` goes, `scripts/check.sh test-slow` and `full`, `make check-full` and `make test-slow` go, and the workflow `full` is deleted. `make check` is the one definition of done, before every commit and before every pull request.

Measured on the author's machine, before and after, assertions on:

| harness | before | after |
|---------|--------|-------|
| `p256_kat` (467 cases) | about 3 min | 0.4 s |
| `sumcheck_kat` with the P-256 end-to-end cases (333) | about 45 min | 1.6 s |
| `gf2_128_kat`, `ligero_kat`, `transcript_kat` | seconds | 0.3 s, 0.3 s, 3.6 s |

The full proof reports every check proved with the same count as before the change (10738) and the same maximum step count.

## Alternatives considered

- **Keeping the slow set weekly, as ADR 0041.** Rejected now: the two sets, the third workflow and the pre-pull-request run were the cost of keeping contracts executable that the proof already covers for all inputs; Phase B adds circuits of tens of thousands of inputs on P-256, on which the executed model would not finish.
- **A second test build without assertions for the slow cases.** Rejected: two binaries of the harness with different semantics, and the P-256 cases would then run with no contract at all, including the protocol-level ones that this record keeps.
- **Batch inversion and faster lemmas.** Insufficient, as ADR 0041 found: the cost was in every multiplication, not in the inversions.
- **Moving only the lemma calls, leaving the postconditions executable.** Rejected: a postcondition that mentions the model cannot be at a lower level than the model, and executing `To_Int` on every result was the larger part of the cost.

## Consequences

- The trade-off, stated plainly: the functional contracts of the two fields are proved for all inputs by GNATprove and are no longer re-checked at run time by the harnesses. What the harnesses check of the fields is the compiled result against the known-answer vectors of [ADR 0009](0009-known-answer-vectors.md) and [ADR 0017](0017-p256-test-anchors.md), and every protocol-level contract on top of them. A divergence between proof and compiled code in the fields would now show as a wrong vector, not as a failed postcondition.
- `make check` runs the whole harness set in about a minute of tests instead of forty-five; the harnesses are no longer a factor in the cadence.
- ADR 0010, 0014 and 0041 are amended in their Status lines; the README's testing and continuous integration sections, the guide's chapters 1 and 2 and the package headers say what executes.
- The constant-time scope of [ADR 0006](0006-constant-time-discipline-and-scope.md) is unchanged: builds with assertions enabled still execute the contracts that remain executable, and are still excluded from the guarantee.

## Verification impact

- Provable: unchanged; the same checks, proved at the same level.
- Tested: the fields by their vectors only; the protocol by its vectors and its executed contracts, as before.
- Trusted: nothing new. The item "GNATprove and the compiler agree on the field code" was never listed because the vectors cover it; they still do.
- Constant time: no effect.

## References

- [ADR 0005](0005-mul-ref-as-proof-target.md), [ADR 0006](0006-constant-time-discipline-and-scope.md), [ADR 0009](0009-known-answer-vectors.md), [ADR 0010](0010-assertion-enabled-test-project.md), [ADR 0014](0014-p256-functional-specification-and-ghost-model.md), [ADR 0015](0015-p256-canonical-form-and-conditional-subtraction.md), [ADR 0017](0017-p256-test-anchors.md), [ADR 0023](0023-gold-perimeter-for-protocol-code.md), [ADR 0041](0041-verification-cadence.md).
- `src/proof_levels.ads`, `src/p256_field.ads`, `src/p256_field.adb`, `src/gf2_128.ads`, `src/gf2_128.adb`; `tests/longfellow_spark_tests.gpr`; `scripts/check.sh`.
- SPARK User's Guide, "Assertion levels" (`pragma Assertion_Level`); GNAT Reference Manual, "Pragma Assertion_Level".
