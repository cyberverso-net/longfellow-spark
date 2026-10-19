# 0061 The README as a front page, the trust model in the guide

## Status

Accepted

## Date

2026-10-19

## Context

[ADR 0003](0003-proof-policy-and-trust-model.md) put the trust model in the README, and every stage since has added its entries there. By Phase C the README had grown to about 4600 words. The trust model alone was four paragraphs of up to 1500 words each, with a status table whose cells ran to several lines. A reader opening the repository could not tell in a minute what the project is, how far it has got, or what it guarantees. The detail was all correct, but it was hard to read and hard to maintain.

## Decision

- The full trust model moves to `docs/guide/trust-model.md`. It keeps the four groups of ADR 0003: proved, tested, trusted, and outside the proofs with what covers them. Within each group the entries are arranged by part of the system rather than by stage, as short bullets. A table maps each vector file to its generator and harness.
- The README becomes a front page. It says what the project is, which phases are done, what a reader can rely on in six bullets, and how to build, prove, test, verify and prove from the command line. For the rest it links to the guide and to the records.
- Texts are written to be read: short sentences, one idea each, lists for parallel items, and a record cited where it explains a choice rather than in every clause.

## Alternatives considered

- **Keep the trust model in the README and only rewrite it.** Rejected: even with shorter sentences, the full list is several pages, and a front page that long buries its summary.
- **One trust model page per chapter.** Rejected: the chapters already carry their own proved, tested and trusted sections. The value of the trust model is one list for the whole project.

## Consequences

- ADR 0003 is amended: the trust model is kept in the guide, and the README summarises it.
- The guide index lists the trust model second, after the verification approach. The verification approach and the guide's conventions link to it.
- Earlier records that say "the README trust model" describe where it was at the time and are not changed.
- Each stage that changes what is proved, tested or trusted updates `docs/guide/trust-model.md`, and the README summary only when a headline changes.

## Verification impact

None on the code. No entry of the trust model was added, removed or changed in meaning by the move.

## References

- [ADR 0003](0003-proof-policy-and-trust-model.md), [ADR 0042](0042-status-amendments.md).
- `README.md`, `docs/guide/trust-model.md`, `docs/guide/README.md`.
