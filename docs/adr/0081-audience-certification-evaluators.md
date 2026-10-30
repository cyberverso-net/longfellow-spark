# 0081 The audience: evaluators in a certification laboratory

## Status

Proposed (2026-10-30, during the memory milestone of Phase D).

## Date

2026-10-30

## Context

- The project exists to make it easier to certify solutions built on Longfellow ZK, as far as the implementation is concerned. An evaluator must be able to follow the evidence from the specification and upstream's Lean proofs down to the code, with every property proved, tested or trusted, each listed.
- The guide was written for "a reader who knows some cryptography and little or no SPARK". The chapters assume the background of the drafts: finite fields, multilinear extensions, the sumcheck protocol, Reed-Solomon codes, Ligero, Merkle trees, Fiat-Shamir.
- The people who certify such a system in a laboratory are experts in certification. They are not, as a rule, experts in cryptography or in SPARK.
- Zero-knowledge proofs for identity credentials are new to most of the people who will deploy, assess or rely on them. Understanding how they work is part of trusting them.

## Decision

**The repository is written for evaluators in a certification laboratory**, and more broadly for anyone who wants to understand how such a system works.

- Every step needed to understand the algorithm, its implementation and the evidence is explained, well enough to certify it.
- No expertise in cryptography or in SPARK is assumed. The cryptography and the mathematics are explained from first principles; the specification is cited, not reproduced.
- This governs every chapter of the guide, every record and the README from now on.

How the existing guide reaches this audience:

- the introduction of the guide states the audience and the current state of the chapters;
- the chapters of the mDoc layer (Phase D, blocks 5 and 6) are written for it from the start;
- a milestone of its own revises the guide, after the mDoc layer and before the certification block ([ADR 0082](0082-order-after-the-memory-milestone.md)): a primer on the cryptography, a primer on the Ada/SPARK constructs, a glossary, a reading path for an evaluator, and every chapter checked against the audience.

## Alternatives considered

- **Keep the reader who knows some cryptography.** Rejected: it leaves out the people who certify the system, who are the reason the project exists.
- **Change only the introduction now.** Rejected: it would promise what the chapters do not yet give.
- **Revise the guide inside the certification block.** Rejected: that block already has eight items, and this would be the one to slip. The certification documents also read better with a glossary and a primer already in place.

## Consequences

- The introduction of the guide says whom it is for and that the chapters are being revised.
- The milestone review of the whole repository judges the documentation against this audience.
- The guide milestone gets its own plan, chapter by chapter, when the mDoc layer closes.

## Verification impact

None: no code and no contract changes.

## References

- [ADR 0055](0055-phase-d-scope-mdoc-scale.md), [ADR 0058](0058-mdoc-layer.md), [ADR 0082](0082-order-after-the-memory-milestone.md).
- [The guide](../guide/README.md), [the trust model](../guide/trust-model.md), [the Lean correspondence](../guide/lean-correspondence.md).
