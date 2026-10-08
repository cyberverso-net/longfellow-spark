# 0001 Record architecture decisions

## Status

Accepted

## Date

2026-10-09

## Context

This repository aims at a complete, formally verified reimplementation of Longfellow ZK, built over several phases by a small team, with a reader in mind who is new to SPARK. Decisions about representations, proof targets, trust boundaries and test anchors shape every later stage, and the reasons behind them are easily lost once the code works. Stage 1 (GF(2^128)) was completed before any decision record existed; its decisions are reconstructed from the package headers, the README and the git history in the records that follow this one.

## Decision

Every non-trivial decision is recorded as an Architecture Decision Record (ADR) under `docs/adr/`, one file per decision, named `NNNN-kebab-title.md` with a four-digit sequence number that is never reused.

Each record has the sections Status, Date, Context, Decision, Alternatives considered, Consequences, Verification impact and References, in that order. Verification impact states what the decision makes provable, what it leaves to tests and what it leaves trusted, and its effect on constant-time execution. References cite specification sections by number and upstream files by path and commit; specification text is not reproduced.

Status is one of Proposed, Accepted or Superseded by NNNN. An Accepted record is immutable except for its Status line: a change of mind is a new record that supersedes the old one. A Proposed record may be edited freely until it is accepted or withdrawn.

Records are one to two pages. Rationale is never invented after the fact: a retroactive record reconstructs reasons only from the package headers, the README, the git history and the project notes, and says "Rationale not recorded at the time" where none survives, together with what is known.

Package headers cite the records they implement. `docs/adr/README.md` holds the index.

## Alternatives considered

- Keep rationale in package headers only. Rejected: headers must stay short and cannot hold alternatives and their verification impact; a decision that spans packages (proof policy, test strategy) has no natural header.
- A single running design document. Rejected: it drifts, and an edited document hides when a decision changed.

## Consequences

- A stage is not complete until its decisions are recorded and its guide chapter cites them.
- Reviewers can challenge a decision by proposing a superseding record rather than by editing history.
- Retroactive records are explicitly marked as such and are honest about missing rationale.

## Verification impact

None on the code. The Verification impact section of each record makes the trust model of the README traceable decision by decision.

## References

- `docs/adr/README.md`, the index.
- `docs/guide/README.md`, the reading order of the guide.
