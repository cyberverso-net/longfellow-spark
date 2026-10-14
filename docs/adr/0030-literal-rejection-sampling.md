# 0030 Literal rejection sampling and declared non-termination

## Status

Accepted (2026-10-14, at the close of stage 4)

## Date

2026-10-13

## Context

Two extractions of draft Section 3.4 loop until a draw is accepted. `nat (n)` masks l bytes to the smallest all-ones value covering n and retries while the result is not below n; the P-256 sampler of Section 3.4.3 reads 32 bytes and retries while the value is not below p. Each attempt consumes fresh bytes, so the sequence of accepted values depends on the number of rejected attempts: an implementation that bounded the loop and returned something else on exhaustion would produce a different transcript from the reference whenever the bound was hit. The reference implementation (`transcript.rs`, `algebra/p256.rs`) has no bound.

Termination of these loops is probabilistic: the mask of `nat` is below 2 n, so an attempt fails with probability at most one half (exactly one half when n is a power of two, as for n = 256 in B.2.4); for P-256, 2^256 - p is below 2^224, so an attempt fails with probability below 2^-32. Neither fact is expressible to GNATprove, which proves termination by loop variants over well-founded measures. GNATprove 16 treats every subprogram as carrying an implicit `Always_Terminates` and reports it as a check; a procedure may carry `Always_Terminates => False`, or a Boolean condition, to say that termination is not claimed, and a function may not (functions must terminate in SPARK, since a non-terminating function would be an unsound axiom). A call to a procedure that may not terminate makes the caller's termination unprovable in turn.

## Decision

- `Nat` and `Sample` are literal transcriptions of Section 3.4 and of the reference: no attempt cap, no fallback value, no status. `Nat` returns a value below n and the mask of n itself (2^bitlen(n) - 1, so 0x1FF for n = 256), reading l bytes little-endian, where l is the byte length of n; the B.2.4 vectors depend on both details. The P-256 sampler draws 32 fresh bytes per attempt. The only status of the stage, `Exhausted` ([ADR 0028](0028-stage-4-scope-and-challenge-replay.md)), is not a cap on attempts: it is raised by the generator after 2^40 blocks, where the reference panics, and the loops do not test it; once it is raised the generator returns zero bytes, so `Nat` accepts 0 and the P-256 sampler accepts the zero element, and the replay reports the status instead of the challenges.
- Both are procedures, since the aspect cannot be put on a function. `Nat` carries `Always_Terminates => False`. `Sample` of the generic glue carries `Always_Terminates => not F.Sampling_Rejects`: the GF(2^128) instance is proved terminating (its `From_Bytes` accepts every string, and the glue states that as a precondition-free fact through the constant), the P-256 instance is declared possibly non-terminating.
- The aspect propagates to every caller: `Choose`, `Begin_Circuit`, `Begin_Layer`, `Round_Poly`, `Replay_Challenges`, each with the same condition `not F.Sampling_Rejects` where the field is in scope; `Choose` calls `Nat` and carries `Always_Terminates => False`. For the P-256 instance, `Replay_Challenges` is therefore declared possibly non-terminating; for GF(2^128) it is proved terminating.
- Everything else in the stage is proved terminating: `Sha256`, `Aes256`, the codec, `Get_Random_Bytes` and `FsPrf`, the proof reader, with loop variants where a loop bound is not a static range.
- The ADR, the headers and chapter 4 state the probabilistic argument in words; the trust model lists "termination of `Nat` and of the P-256 sampler" as a probabilistic property, not a proved one.

## Alternatives considered

- **A cap of consecutive failures with a status.** Considered in detail and rejected. A cap of 256 attempts for `Nat` and 8 for the P-256 sampler would make the probability of deviating from the reference below 2^-256 per call, and every subprogram would be proved terminating. Rejected because the status would have to propagate to the verifier as a third outcome that neither the draft nor the reference has, and because the transcript would then be a documented approximation of the specification rather than the specification; literal conformance to the draft and to upstream was preferred over provable termination of two loops whose non-termination has probability zero in practice.
- **Terminating the loop by `pragma Assume` or by an unproved loop variant.** Excluded by the project's proof policy: a proof failure is a design decision, not something to work around by weakening the contract ([ADR 0003](0003-proof-policy-and-trust-model.md)); no `pragma Assume` and no lemma with a null body ([ADR 0014](0014-p256-functional-specification-and-ghost-model.md)); no justification ([ADR 0018](0018-continuous-verification-gate.md)).
- **Drawing a wider value and reducing modulo n or modulo p instead of rejecting.** Rejected: a different distribution and a different transcript; the reference rejects.
- **Keeping `Nat` and `Sample` as functions and hiding the loop in a body outside SPARK.** Rejected: it would move the two most spec-sensitive loops of the stage out of the proof perimeter to satisfy a termination check that is honestly stated by the aspect.

## Consequences

- Two subprograms and their callers carry an explicit `Always_Terminates` condition; a reader of the headers sees at once which instance is proved terminating and which is declared.
- `Nat`, `Sample` and `Choose` are procedures, so the glue and the replay are written in procedural style; the test harness reads the same.
- If a later GNATprove release changes the default or the syntax of the aspect, the change is a toolchain migration recorded with it.

## Verification impact

- Provable: termination of every subprogram of the stage except `Nat`, the P-256 `Sample` and their callers in the P-256 instance; absence of run-time errors everywhere, including inside the unbounded loops (each iteration is proved safe; only the number of iterations is unbounded); the Gold properties of `Nat`, `Choose` and `Sample` of [ADR 0031](0031-transcript-gold-perimeter.md), which hold on exit whenever the loop exits.
- Tested: the accepted values and the byte consumption of rejected attempts against B.2.4 and B.2.5, whose values depend on the number of rejected attempts, and the P-256 challenges against the recorded upstream runs.
- Trusted: termination of `Nat` and of the P-256 sampler, by the probabilistic argument above.
- Constant time: not applicable ([ADR 0029](0029-sha256-and-aes256-in-spark.md)).

## References

- draft-google-cfrg-libzk-03, Sections 3.4.1, 3.4.2, 3.4.3, Appendix B.2.4 and B.2.5.
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/transcript.rs` (`nat`, `choose`), `algebra/p256.rs` (`sample_p256`).
- SPARK User's Guide, "Subprogram termination" (aspect `Always_Terminates`, implicit on every subprogram in GNATprove 16; conditional form).
- [ADR 0003](0003-proof-policy-and-trust-model.md), [ADR 0014](0014-p256-functional-specification-and-ghost-model.md), [ADR 0018](0018-continuous-verification-gate.md), [ADR 0028](0028-stage-4-scope-and-challenge-replay.md).
