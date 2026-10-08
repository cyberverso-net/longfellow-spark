# 0002 Pin the specification to draft-google-cfrg-libzk-03

## Status

Accepted

## Date

2026-10-06 (retroactive record, written 2026-10-09)

## Context

Longfellow ZK is specified by an IETF draft that is under security review and changes between versions. The reference implementation (google/longfellow-zk) evolves alongside it. A verified implementation needs a fixed target: a proof of fidelity to "the current draft" is meaningless if the draft moves under it, and interoperability vectors are only valid for one version of the serialisation and challenge derivation.

## Decision

The project is pinned to IETF draft-google-cfrg-libzk-03 (23 September 2026). Every package header cites the sections it implements by number. A later draft is adopted only as an explicit migration: a record that lists the divergences, their effect on proofs and vectors, and the version pinned from then on.

Known defects of the pinned draft are logged in the project notes and are not silently corrected in code; where the draft is ambiguous or wrong, the upstream reference implementation at a pinned commit (see [0009](0009-known-answer-vectors.md)) is the tie-breaker, and the choice is recorded.

## Alternatives considered

- Track the latest draft continuously. Rejected: proofs and vectors would have to be redone without a record of what changed, and the trust model would have no fixed referent.
- Pin to the reference implementation instead of the draft. Rejected as the primary anchor: the implementation is not the normative text; it is used as a secondary anchor where the draft gives no vectors.

## Consequences

- Expected rework between later phases if challenge derivation or serialisation changes in a later draft (noted as a risk in the project plan).
- Defects found in the draft are documented, not acted on; three are logged as of stage 1: the Field IDs of Appendix B.3 contradict Table 1, the Fiat-Shamir vectors of Appendix B.2 use the secp256k1 prime rather than P-256, and the draft contains no direct GF(2^128) arithmetic vectors.

## Verification impact

- Provable: fidelity claims in headers refer to a fixed text, so "implements Section 2.2.2" has one meaning.
- Tested: interoperability vectors are valid for this version only.
- Trusted: the pinned specification itself (listed in the README trust model).
- Constant time: no effect.

## References

- IETF draft-google-cfrg-libzk-03, Section 2.2.2 (GF(2^128) field definition), Section 3.4.3 (byte to coefficient mapping), Section 7.2.1 (serialisation), Table 1 (field identifiers).
- README, "Status" and "Trust model".
