# 0082 The order after the memory milestone

## Status

Proposed (2026-10-30, during the memory milestone of Phase D).

## Date

2026-10-30

## Context

- [ADR 0080](0080-milestone-memory.md) put a memory milestone before the certification block and M3. What comes after it was still the order of 26 October: the certification block, then M3, with the mDoc layer of Phase D (blocks 5 and 6, [ADR 0058](0058-mdoc-layer.md)) not yet placed.
- The object of a certification is the proof of age from an mDoc, not the generic prover. Most of the trusted entries come from the mDoc layer: the CBOR parse, the MACs, the ECDSA witness, the constant-time account of ADR 0058.
- [ADR 0081](0081-audience-certification-evaluators.md) sets the audience of the repository and asks for a revision of the guide before the certification documents are written.
- Three software optimisations were recorded after M2 ([ADR 0078](0078-milestone-m2-closed.md)): a scalar GF(2^128) product with fewer multiplications, the P-256 sum and difference in a faster form, a carry idiom suited to GCC. All three change kernel bodies, not contracts. None serves an open criterion.

## Decision

**After the memory milestone, in this order:**

1. **The mDoc layer**, Phase D blocks 5 and 6 (ADR 0058). Its chapters are written for the audience of ADR 0081 from the start.
2. **The guide for the evaluator**, a milestone of its own (ADR 0081).
3. **The certification block**: traceability matrix, trusted base register, coverage, release evidence, the link to upstream's Lean development stated as it is.
4. **M3**, opened by a step in Gold, **M3a**: the three optimisations above, each with its record and its measurement, before the tested build with hardware instructions ([ADR 0067](0067-performance-milestones-by-trust.md)).

**Releases:**

- **0.4.0** at the close of the memory milestone: Phase D, performance and memory. The first review of the whole repository falls there.
- **0.5.0** at the close of the mDoc layer: Phase D complete, the criterion of [ADR 0055](0055-phase-d-scope-mdoc-scale.md).
- The first release with the full evidence bundle comes after the certification block.

**One item moves earlier:** the trusted base register starts at the close of the memory milestone, as a living document. Each mDoc block adds the trusted entries it introduces.

## Alternatives considered

- **The certification block before the mDoc layer.** Rejected: its documents would describe a system nobody deploys, and would be rewritten when the mDoc layer brings most of the trusted entries.
- **The optimisations before the certification block.** Rejected: they serve no open criterion. Placed at the start of M3, they make its comparison honest: the hardware variant is measured against the best Gold build, so no gain available in software is credited to the hardware.
- **M3 before the certification block.** Rejected: M3 has the least structural impact. The Gold build stays the reference, and M3 adds a delta to the trust model and a differential harness.

## Consequences

- The README's table of phases shows two releases for Phase D.
- ADR 0055 and ADR 0080 point here for the order.
- The memory milestone ends with the trusted base register, the review of the whole repository and release 0.4.0.

## Verification impact

None: no code and no contract changes.

## References

- [ADR 0055](0055-phase-d-scope-mdoc-scale.md), [ADR 0058](0058-mdoc-layer.md), [ADR 0067](0067-performance-milestones-by-trust.md), [ADR 0078](0078-milestone-m2-closed.md), [ADR 0080](0080-milestone-memory.md), [ADR 0081](0081-audience-certification-evaluators.md).
