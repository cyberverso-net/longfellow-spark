# 0079 The specification migrated to draft-irtf-cfrg-longfellow-00, and upstream's new home

## Status

Proposed (2026-10-29, between M2 and the memory milestone of Phase D).

## Date

2026-10-29

## Context

[ADR 0002](0002-pin-the-specification.md) pins the project to IETF draft-google-cfrg-libzk-03 (23 September 2026). It adopts a later draft only by an explicit migration: a record of the divergences, their effect on the proofs and the vectors, and the version pinned from then on.

Two things changed upstream:

- **The draft was adopted by the CFRG.** On 22 October 2026 it was posted as draft-irtf-cfrg-longfellow-00, in the IRTF stream. The datatracker marks draft-google-cfrg-libzk as replaced by it. The title and the authors are the same.
- **The repository moved.** github.com/google/longfellow-zk now redirects to github.com/longfellow-zk/longfellow-zk. The commits are the same; our pin d5e6be7 is in its history.

The comparison of the two drafts, text against text (the notes of 29 October):

- The 58 section headings are identical, with the same numbers.
- The technical text is identical, word for word.
- The differences are the boilerplate: the stream and its working group, the expiry date, and the Revised BSD clause on code components, which -00 drops.
- **One defect of -00:** Appendix B.3 gives no hexadecimal vectors. The items "Sumcheck Proof (hex)" and "Complete Proof Serialization (hex)" are empty in its XML, HTML and text forms. In -03 the text form carries them.

## Decision

**The project follows draft-irtf-cfrg-longfellow-00 from 29 October 2026.**

- No divergence: the section numbers the package headers cite stay valid, and no code, contract or proof changes.
- The vectors of Appendix B.3 (`zk_proof_gf2_128_b3_3.txt`, `zk_proof_p256_b3_2.txt` and the transcript vectors that replay them) keep their source, the text form of -03. The defect of -00 is logged in the notes, as ADR 0002 asks.
- Where the living documents cite the pinned draft, they name -00: the README, the guide, the trust model and the headers of `src/`.
- Where a record of what was done cites -03, it stays: the bodies of the records (ADR 0001 and ADR 0042), and the provenance lines of the vector files and their generators, which say where the data came from.

**Upstream's new home.** The living documents and the headers of `src/` name longfellow-zk/longfellow-zk. The bodies of the records and the provenance lines of the vectors keep google/longfellow-zk, which redirects, with the same commits.

**The Lean reference** moves from d9d8d6a to 7bf8a6b (26 October 2026), upstream's main at this date: [the Lean correspondence](../guide/lean-correspondence.md) is rewritten for it, with the 116-bit headline. The code and interop pin stays d5e6be7: upstream's v1 is frozen and reproduces its saved proofs bit for bit.

## Alternatives considered

- **Stay on -03.** Possible, since the technical text is the same. Rejected: -03 is replaced, and an evaluator looks for the current CFRG document.
- **Rewrite every citation of -03 and of the old repository.** Rejected: it would change the record of what was done, against ADR 0042, and the vector files, which `make check` regenerates and compares byte for byte.

## Consequences

- ADR 0002 points here in its Status line.
- The README, the guide, the trust model and the headers of `src/` name -00 and longfellow-zk/longfellow-zk.
- [The Lean correspondence](../guide/lean-correspondence.md) follows 7bf8a6b. The trust model states the 116-bit result. ADR 0064 gets a Status note for the path of upstream's `ConcreteCircuit.lean`.

## Verification impact

- None: the text the proofs and the vectors follow is unchanged.

## References

- draft-irtf-cfrg-longfellow-00 (22 October 2026), draft-google-cfrg-libzk-03 (23 September 2026), https://datatracker.ietf.org/doc/draft-irtf-cfrg-longfellow/.
- longfellow-zk/longfellow-zk at 7bf8a6b: `formal/README.md`, `formal/AUDIT.md`, `formal/lfzk-v1/README.md`.
- [ADR 0002](0002-pin-the-specification.md), [ADR 0042](0042-status-amendments.md), [ADR 0064](0064-lean-circuit-premises.md).
