# 0042 Status amendments

## Status

Accepted (2026-10-16, consolidation after Phase A)

## Date

2026-10-16

## Context

[ADR 0001](0001-record-architecture-decisions.md) makes an Accepted record immutable except for its Status line, which is one of Proposed, Accepted or Superseded by NNNN. Practice since stage 2 added a kind of change that 0001 does not name: a later record changes one point of an earlier one without replacing it (the proof gate of [ADR 0019](0019-proof-off-the-hosted-gate.md), amended in turn by 0021, 0033, 0034 and 0041; the status enumeration of [ADR 0039](0039-sizes-allocation-and-status.md), amended in blocks 4 and 5 of stage 5), and the earlier record's Status line carries a note saying so.

The notes drifted in two ways. The wording varied from record to record ("superseded in part by", "amended by ... on", "Amended 2026-10-16, block 4:"), so a reader cannot scan the Status lines for one shape. And the notes of 0039 and 0040 grew to several sentences that state decisions found nowhere else (the `Exhausted` status, the streaming slice, the bound of `Choose` left in place), which is what 0001 set out to prevent: a decision whose only record is a Status line.

## Decision

- An Accepted record's Status line may carry amendment notes, each of the form `Amended YYYY-MM-DD by [ADR NNNN](file): one sentence saying what changed.`, after `Accepted` and its parenthesis, in chronological order. The body stays immutable; the note names the amending record and the reader follows the link for the rationale.
- A note longer than two sentences means a record was due: the content goes into a new Accepted record, dated when the decision was taken and saying where it was recorded until then, and the note becomes a pointer to it.
- The amending record says in its Consequences which records it amends; the two sides agree.
- The index `docs/adr/README.md` shows the state as `Accepted` or `Accepted, amended by NNNN` (several numbers when several records amend), never the note itself.
- The existing notes (0003, 0018, 0019, 0021, 0033, 0034, 0039, 0040) are normalised to this form at this date. The note of 0039 becomes [ADR 0043](0043-exhausted-status-and-streaming-slice.md); the note of 0040, a finding of the tests rather than a decision, is shortened to two sentences and stays.

## Alternatives considered

- **A superseding record for every amendment.** Rejected: a record superseded on one point loses the reader its other points, which still stand; the gate records 0019, 0021, 0033 and 0034 each stand on everything but the point the next one changed.
- **Dated markers in the body.** Rejected: the body would no longer be what was decided on its date, and 0001's immutability is what makes a record citable.
- **Free-form notes, as until now.** Rejected: 0039 shows where that leads.

## Consequences

- ADR 0001 carries the first note in this form, pointing here; its body is unchanged.
- Eight Status lines change shape and lose no information: what a long note said is in ADR 0043 or in the amending record.
- A reviewer of a future amendment checks two things: the note fits the form, and the amending record lists the amended one.

## Verification impact

None on the code. The traceability of the trust model that ADR 0001 claims is kept: every decision has a record of its own, and a Status line only points.

## References

- [ADR 0001](0001-record-architecture-decisions.md), [ADR 0039](0039-sizes-allocation-and-status.md), [ADR 0040](0040-ligero-vectors-and-upstream-instrumentation.md), [ADR 0043](0043-exhausted-status-and-streaming-slice.md).
- `docs/adr/README.md`, the index.
