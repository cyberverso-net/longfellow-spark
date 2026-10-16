# 0039 Sizes, allocation and the status enumeration

## Status

Accepted (2026-10-15, before block 2 of stage 5). Amended 2026-10-16 by [ADR 0043](0043-exhausted-status-and-streaming-slice.md): the enumeration gains `Exhausted`, `Write_Element_Slice` has its streaming form, and `Fisher_Yates.Max_N` is not raised.

## Date

2026-10-15

## Context

Stage 3 learned that records on the stack scale badly: the input constraint of `Verifier_Core` costs about 120 bytes per private input and overflowed the default 8 MiB stack of macOS at 32768 inputs ([chapter 3](../guide/03-sumcheck.md), Section 3.5). Ligero adds objects whose size comes from the configuration and the circuit at run time: the opened columns (NROW times NREQ elements), the Lagrange tables ([ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md)), the constraint vector of the linear test (NQW times WR elements), the path. With the profile of Section 5.1 (NREQ 132, rate 7) and real circuits these are megabytes.

The transcript of stage 4 bounds two operations that Ligero stretches: `Choose` takes n at most 2^16 (`Fisher_Yates.Max_N`, the shuffle's array on the stack) with n = NCOL - DBLOCK here, and `Write_Element_Slice` takes at most 4096 elements, serialised into one stack array, with BLOCK and DBLOCK elements to absorb here.

The reference reports errors as an enumeration (`VerificationError`, `ZkVerificationError`, the I/O errors of the readers); this project reports errors as a status and never raises ([ADR 0022](0022-stage-3-scope-and-challenges-as-input.md), [ADR 0028](0028-stage-4-scope-and-challenge-replay.md)).

## Decision

- Sizes come from the configuration and the circuit at run time; the records are unconstrained arrays with preconditions stating their lengths from the geometry, as in stage 3.
- The large objects of the verifier (the opened columns, the two Lagrange tables, the constraint vector and the per-row encodings of the linear test, the path) live in one allocation sized by the geometry and passed by reference to the four tests; the chapter states the supported scale on a default stack and what a larger scale requires (phase B, together with the input constraint of stage 3).
- `Write_Element_Slice` gains a streaming form: the tag and the count absorbed, then one element at a time, with the ghost frame stated by recursion on the elements as `Publics_Frame` does, so that no serialised copy of the slice exists; the bound of 4096 elements goes. `Fisher_Yates.Max_N` is raised to what the supported scale needs, with the shuffle's arrays in the same allocation discipline.
- Errors are the enumeration `Ok, Public_Input_Length, Queried_Columns_Length, Polynomial_Lengths, Merkle_Failed, LDT_Failed, Linear_Failed, Linear_Sum_Failed, Quadratic_Failed, Proof_Encoding, Matrix_Failed`, one value per cause the code can produce, with postconditions tying the status to the failed test where the structure allows; no exceptions. The reference's three shape errors on the sumcheck proof (layer, round, evaluation count mismatch) have no counterpart: the stage 4 reader produces a record of the shape the circuit fixes, which `Verifier_Core` takes as a proved precondition, and a byte string of the wrong length is `Proof_Encoding`; an enumeration value that no path produces would make its postcondition vacuous.
- The readers return `Proof_Encoding` on: a non-canonical element, a run-length violation, a run beyond 2^25 elements, a count that does not fit, bytes missing, trailing bytes after the complete proof.

## Alternatives considered

- **Keeping the reference's status names one for one**, including the shape errors. Rejected, as above: the enumeration lists what can happen here.
- **Exceptions for the readers.** Rejected, as in every stage: a verifier that raises on attacker-controlled input has a second failure path to reason about.
- **Fixed maximum sizes as constants** (as `Max_Wires`, `Max_Logw` in stage 3). Kept where a bound is inherent (NREQ, the run length); rejected for NCOL and NROW, which the configuration and the circuit set.

## Consequences

- Chapter 5 carries a table of the memory of the verifier per parameter, and the supported scale.
- The transcript's `Write_Element_Slice` changes shape; its Gold statement is restated by recursion and its callers in stage 4 (`End_Layer`) are unchanged in meaning.
- One enumeration for the whole verifier, the readers included.

## Verification impact

- Provable: every array access in range from the geometry's postconditions; the statuses' postconditions.
- Tested: each status by a negative case ([ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md)).
- Trusted: that the supported scale is respected by the caller (stack exhaustion is outside the proofs, SPARK User's Guide, "Dealing with Storage_Error").
- Constant time: not applicable (ADR 0037).

## References

- [ADR 0022](0022-stage-3-scope-and-challenges-as-input.md), [ADR 0026](0026-sparse-expression.md), [ADR 0028](0028-stage-4-scope-and-challenge-replay.md), [ADR 0031](0031-transcript-gold-perimeter.md), chapter 3 Section 3.5.
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/ligero/verifier.rs` (`VerificationError`), `zk/verifier.rs` (`ZkVerificationError`), `ligero/proof.rs` (the I/O errors).
