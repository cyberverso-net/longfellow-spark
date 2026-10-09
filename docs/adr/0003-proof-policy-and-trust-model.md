# 0003 Proof policy and trust model

## Status

Accepted

## Date

2026-10-06 (retroactive record, written 2026-10-09)

## Context

SPARK offers graded assurance: Stone (valid SPARK subset), Bronze (flow analysis), Silver (absence of run-time errors), Gold (proved functional contracts), Platinum (full functional correctness). Proof effort grows steeply with the level, and SMT solvers struggle with non-linear arithmetic. A zero-knowledge proof system has three kinds of properties: those SPARK can prove (memory safety, arithmetic correctness against a model), those that are probabilistic protocol properties (soundness, zero knowledge) and those that are about the execution rather than the result (constant time). A uniform target would either be unreachable or would understate what is actually guaranteed.

## Decision

- Silver on every line of SPARK code in the project, without exception: absence of run-time errors for all inputs, since proofs and circuits are attacker-controlled input.
- Gold only where functional correctness buys real security, declared kernel by kernel in the package header: field arithmetic (GF(2^128) and P-256), Merkle path verification, circuit evaluation semantics.
- Everything else is covered by known-answer tests, interoperability vectors and spec-derived checklists.
- Platinum over the whole system is explicitly not a goal.
- The README keeps a trust model in which every claim is one of proved, tested or trusted, maintained from the first commit and reduced over time.
- Default prover configuration: `gnatprove --level=2 --report=all`. A higher level is used only with a recorded rationale. Amended by [ADR 0018](0018-continuous-verification-gate.md) on 2026-10-09: the configuration is now stated in `package Prove` of the project file as the provers of level 2 with a step budget (`--steps=600000 --timeout=0`), because a timeout makes the outcome depend on the machine; raising the budget needs the same recorded rationale as raising the level did.

## Alternatives considered

- Gold everywhere. Rejected: unreachable for parsers and protocol glue at reasonable cost, and it would blur the line between what is proved and what is not.
- Silver only, with tests for everything else. Rejected: a reduction bug in field arithmetic breaks soundness silently and would not be caught by samples; this is where proofs have the highest value per line.
- Platinum on the field arithmetic. Not pursued: Gold against a ghost reference already gives "for all inputs" correctness relative to that reference; the remaining gap (reference versus specification) is closed by vectors, see [0005](0005-mul-ref-as-proof-target.md) and [0009](0009-known-answer-vectors.md).

## Consequences

- Package headers state, subprogram by subprogram, what is proved, what is tested and what is trusted.
- Proof failures are treated as design decisions, not as obstacles to be worked around by weakening contracts silently.
- Rationale for the choice of level 2 as the default: not recorded at the time beyond "default loop" in the project plan; it is the level at which stage 1 was fully discharged.

## Verification impact

This record defines the vocabulary used by every other record's Verification impact section.

## References

- README, "Trust model" and "Building and proving".
- SPARK User's Guide, "Levels of software assurance" (for the level names).
- [0006](0006-constant-time-discipline-and-scope.md) for the scope of the constant-time claim.
