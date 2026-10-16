# 0043 Exhausted status and streaming slice

## Status

Accepted (2026-10-16; decided in blocks 4 and 5 of stage 5 and recorded in the Status line of [ADR 0039](0039-sizes-allocation-and-status.md) until this record, written the same day under [ADR 0042](0042-status-amendments.md))

## Date

2026-10-16

## Context

[ADR 0039](0039-sizes-allocation-and-status.md) fixed the status enumeration of the verifier before block 2 of stage 5 and foresaw two changes to the transcript for Ligero: a streaming form of `Write_Element_Slice`, whose stage 4 form serialised the whole slice into one stack array bounded at 4096 elements, and a raise of `Fisher_Yates.Max_N`, the bound of 2^16 on the n of `Choose`.

Block 4 brought the first point the enumeration had missed. The Ligero verifier draws challenges of its own (u_ldt, alphal, alphaq, u_quad, the chosen columns), so it can meet the condition that [ADR 0028](0028-stage-4-scope-and-challenge-replay.md) already renders as a status in `Replay_Challenges`: the generator `FsPrf` past its bound of 2^40 blocks, where the reference panics and this project sets a sticky flag and returns zero bytes ([ADR 0030](0030-literal-rejection-sampling.md)). An enumeration without a value for it would have forced the Ligero verifier either to raise or to report a wrong cause.

Block 5 brought the polynomials to absorb (BLOCK and DBLOCK elements, Section 4.5) and the question of how large the one `choose` of the verifier can be.

## Decision

- `Verifier_Status` gains `Exhausted`, between the length statuses and the test verdicts: the transcript's generator passed its bound during the verifier's own draws. `Ligero_Verifier.Verify` gives it only in that case, and its postcondition ties it to the generator (a test verdict implies live challenges); `Zk_Verifier.Verify` reports the same value when `Replay_Challenges` reports its own `Exhausted`. No negative case reaches it: a draw takes at most three blocks and the flag needs 2^40 ([ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md)).
- `Write_Element_Slice` has its streaming form: `Transcript.Begin_Slice` absorbs the tag 0x02 and the eight little-endian count bytes, `Slice_Element` absorbs one serialised element, and the glue of `Sumcheck_Transcript` absorbs a slice one element at a time. The ghost frame is stated by recursion on the elements, `Elements_Frame (Slice_Header (S, Count), Es, Count)`, hidden and unhidden in the one loop that steps it, as `Publics_Frame` is ([ADR 0031](0031-transcript-gold-perimeter.md)); `End_Layer` and `Absorb_Polynomials` restate their frames in that form. `Serialise` and the bound `Max_Slice` of 4096 are removed; no serialised copy of a slice exists.
- `Fisher_Yates.Max_N` stays at 2^16: the only `choose` of the verifier draws NREQ columns below NCOL - DBLOCK, and NCOL is at most `Ligero_Geometry.Max_Encoded_Len` = 2^16, the range of the Reed-Solomon evaluation points on GF(2^128); the geometry's postcondition discharges the precondition of `Choose` without a run-time check.

## Alternatives considered

- **A cap on the verifier's draws instead of a status.** Rejected, as in ADR 0030: the loops are literal transcriptions of Section 3.4 and do not test the flag; the status is the reference's panic rendered as an outcome.
- **Reporting the generator's exhaustion as `Proof_Encoding`.** Rejected: an enumeration value is one cause, and this cause is not in the proof string.
- **Keeping the 4096 bound and sizing it to the largest configuration.** Rejected: the bound was an artefact of the serialised copy, and the copy cost stack space that ADR 0039 was removing elsewhere.
- **Raising `Max_N` in advance, as ADR 0039 foresaw.** Not needed: the geometry bound discharges the precondition, and a larger shuffle array would cost stack for nothing.

## Consequences

- ADR 0039 is amended by this record on the three points above; its Status line points here.
- The enumeration of ADR 0039 reads `Ok, Public_Input_Length, Queried_Columns_Length, Polynomial_Lengths, Exhausted, Merkle_Failed, Matrix_Failed, LDT_Failed, Linear_Failed, Linear_Sum_Failed, Quadratic_Failed, Proof_Encoding`.
- Chapter 5, Section 3.6, describes the streaming slice and the bound of `Choose`.

## Verification impact

- Provable: the postcondition of `Ligero_Verifier.Verify` tying `Exhausted` to the generator; the slice frames by recursion, structural Gold as the other frames of ADR 0031; the precondition of `Choose` from the geometry.
- Tested: nothing reaches `Exhausted` on the vectors, by construction; the slices absorbed by the streaming form give the challenges the upstream recordings show (ADR 0040).
- Trusted: unchanged.
- Constant time: not applicable, as ADR 0037.

## References

- draft-google-cfrg-libzk-03, Sections 3.1.1, 3.2, 3.4.2, 4.5.
- [ADR 0028](0028-stage-4-scope-and-challenge-replay.md), [ADR 0030](0030-literal-rejection-sampling.md), [ADR 0031](0031-transcript-gold-perimeter.md), [ADR 0039](0039-sizes-allocation-and-status.md), [ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md).
- `src/verifier_status.ads`, `src/transcript.ads` (`Begin_Slice`, `Slice_Element`, `Slice_Header`), `src/sumcheck_transcript.ads` (`Elements_Frame`), `src/fisher_yates.ads` (`Max_N`), `src/ligero_geometry.ads` (`Max_Encoded_Len`); `docs/guide/05-ligero.md`, Section 3.6.
