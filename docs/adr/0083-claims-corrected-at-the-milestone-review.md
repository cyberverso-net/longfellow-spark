# 0083 Claims corrected at the milestone review of the memory milestone

## Status

Proposed (2026-11-06, at the milestone review of the memory milestone, #63).

## Date

2026-11-06

## Context

The memory milestone ends with a review of the whole repository ([docs/process.md](../process.md), "Milestones"; #63): the documents against each other and against the code, the proofs against what the headers and the records claim. Three claims of the records and the package headers said more than the contracts or the code establish. Each is a statement an evaluator would rely on, so each is corrected here, and the records that made the claim carry a note pointing to this one, as [ADR 0042](0042-status-amendments.md) prescribes.

1. **The writers' proved statement.** [ADR 0052](0052-gold-perimeter-for-the-prover.md) and the header of `Proof_Writer` said that the bytes each writer produces are the element-wise serialisation of the record, as a proved layout. The contracts state less: `Write_Sumcheck_Proof` has no postcondition; `Write_Ligero_Proof` is proved to leave the bytes before its offset unchanged and to produce a columns part that satisfies the reader's rules, `Well_Coded`; `Write_Proof` is proved to write the root first and exactly `Proof_Len` bytes. The element-wise correspondence is proved for each write (`Put_Element`, `Put_Slot`, `Put_32`, `Put_Size_4`), and no loop invariant composes those writes into a statement about the whole string. The guide's chapter 7 and the trust model claimed only the lengths, the root and `Well_Coded`, which is what the contracts say.
2. **The satisfiability check.** [ADR 0051](0051-constant-time-in-the-prover.md), the header of `Zk_Prover` and chapter 7 described the two checks on witness-derived values, the satisfiability check and the subfield check, as "a fixed loop accumulating a mask and one branch on the result". The subfield check is written so. The satisfiability check, `Packed_Eval.Eval_Circuit`, tested each assertion product and each output wire with an `if` and set its result to False inside: one branch per term and per output on a value derived from the witness. What such a branch could reveal is which assertion fails on inputs that do not satisfy the circuit, not the witness of inputs that do; the declared discipline was still not followed.
3. **The ULEB128 reader.** The header of `Uleb128` said that `Read` is proved to fail exactly when no terminating byte lies within four bytes of the position. Its postcondition said what holds on success and that nothing moves on failure; it did not say when failure occurs, nor what `Long` means.

## Decision

- **The writers: narrow the claim.** The header of `Proof_Writer` says what is proved (the lengths, the root, `Well_Coded`, and the correspondence of each write) and what is tested (`Read (Write (P)) = P`, on every proof of the repository, `writer_kat`). ADR 0052 carries a note to this record. The composition into a postcondition of the writers, which would make the original claim true, is an issue of the certification block (#113), not done here: it needs a frame over the string in every loop of the Ligero writer, whose invariant already carries the `Well_Coded` chain.
- **The satisfiability check: follow the rule.** Both tests of `Eval_Circuit` accumulate into the result with a Boolean `and` on the comparison with zero, `OK := OK and (X = Zero)`, a value operation and not a branch; the one branch on the result stays the prover's decision whether to produce a proof. The Gold contract against `Z_Ref` is unchanged, since the two forms are the same Boolean. The output test reads the wire into a local constant first: with the record compared straight from memory, the compiler short-circuited the four limbs of a P-256 element with a branch per limb; with the local, it ors the limbs and compares once. The binary of the four sites (two instances, two tests) is inspected on arm64 and x86-64 in the release build, as the correction of `Inject` was ([ADR 0051](0051-constant-time-in-the-prover.md), amended 30 October), and the pull request of the change records what the inspection found. This is an inspection, not a timing experiment, and no timing claim is made; the automatic check of the generated code is #70. ADR 0051 carries a note to this record when the code is merged.
- **The ULEB128 reader: prove the claim.** The postcondition of `Read` states the whole behaviour: success exactly when a byte without the continuation bit lies within four bytes of the position; on success, the bytes consumed are those up to and including the first such byte, every earlier byte continuing, and the value is their payload; on failure, the position is unchanged, the value is zero and `Long` is True exactly when four bytes were available, so that the loader's `Truncated` and `Bad_Integer` are tied to their causes. A strengthening of an existing contract, approved by the maintainer; nothing is weakened.
- **The texts.** The guide's chapters 1, 5, 6 and 7, the Lean correspondence and the trusted base register are corrected where the review found them behind the code or ahead of the proofs: the release build without run-time checks in the proved units (ADR 0068) where chapter 6 said the checks stay on; the heap working sets (ADR 0047) and the linear input constraint (ADR 0056) where chapters 5 and 6 kept the stack and its limits; the parity part of the encoded rows proved only with the Lagrange encoder and tested with the FFTs (ADR 0057), and the round evaluations proved at P2 for the true claim, where chapter 7 claimed both without the condition; the MAC-key condition of upstream's end-to-end statement, missing from the Lean correspondence; the subfield sampler, which serves the prover's random rows and no challenge of the verifier; the sumcheck messages, which are sums of products of wires and not linear in them; the header of `Sha256`, which forbade every use on secret data while the prover hashes the leaves of its commitment under ADR 0051; and two rows of the register, the Silver units whose agreement with the reference is tested and the completeness of the prover, which the trust model listed and the register did not.

## Alternatives considered

- **Prove the writers' claim now.** Rejected for this review: a proof of one or two partition runs and a gate, for a statement the trust model never relied on. It is recorded as #113 so that the stronger claim can be made when it is proved.
- **A byte mask for the satisfiability check**, as the subfield check does. Rejected: `To_Bytes` is a formal of the field signature without a contract, so the generic could not prove that the mask is zero exactly when the product is, and the Gold link to `Z_Ref` would be lost; a weaker contract needs a decision this record does not take.
- **Narrow the ULEB128 header** instead of proving it. Kept as the fallback if the proof resists.

## Consequences

- Amends [ADR 0052](0052-gold-perimeter-for-the-prover.md): the proved statement of the writers is the lengths, the root, `Well_Coded` and the correspondence of each write; the element-wise serialisation of the whole string is tested.
- Amends [ADR 0051](0051-constant-time-in-the-prover.md), when the code is merged: the satisfiability check accumulates without a branch on the values, as the record's rule requires.
- The contract of `Uleb128.Read` is stronger; chapter 6 said what it now proves.
- The milestone review becomes a source of corrections with its own record when a claim changes, rather than silent edits of headers.

## Verification impact

- `Packed_Eval`: the bodies change, the contracts do not; the partition `packed_hquad` is proved again. `Uleb128`: the postcondition of `Read` and two loop invariants; the partition `circuits` is proved again. No level changes, no prover setting changes.
- The binary inspection of the four sites of `Eval_Circuit` on arm64 and x86-64 is evidence of the change, recorded in the pull request; it is not a proof and not a timing measurement.
- No test changes: the vectors and the harnesses pass unchanged, which is what the unchanged contracts predict.

## References

- [docs/process.md](../process.md), the milestone review.
- The trust model, [docs/guide/trust-model.md](../guide/trust-model.md), and the register, [docs/guide/trusted-base.md](../guide/trusted-base.md).
- [ADR 0006](0006-constant-time-discipline-and-scope.md), [ADR 0042](0042-status-amendments.md), [ADR 0051](0051-constant-time-in-the-prover.md), [ADR 0052](0052-gold-perimeter-for-the-prover.md), [ADR 0068](0068-release-build-without-run-time-checks.md).
- Issues #63 (the review), #113 (the proof of the writers' serialisation), #70 (the check of the generated code), #66 (the mDoc layer, for the MAC-key condition).
