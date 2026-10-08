# 0011 Circuits are data

## Status

Accepted

## Date

2026-10-06 (retroactive record, written 2026-10-09; the decision is in the project plan that predates the first commit)

## Context

The upstream C++ codebase has three parts of very different size: the verifier (compact, security-critical), the prover (large, performance-dominated) and the circuit compiler, which turns SHA-256, ECDSA verification and CBOR/mDoc parsing into circuit representations and is the largest part. The compiler's output is a serialised circuit. A reimplementation that started with the compiler would reach a working proof system last.

## Decision

Circuits are treated as data. The SPARK verifier and prover consume circuits produced by the upstream compiler (or shipped with the specification), parsed and validated by a SPARK loader that proves absence of run-time errors on arbitrary bytes and checks well-formedness (gate arity, wire indices in range, topological order). The circuit format fixed by the pinned draft is a first-class interface of the project. The compiler is reimplemented in the final phase; until then upstream-generated circuits are a declared trusted input in the README.

The phases are: A, foundations (field arithmetic, sumcheck verifier, transcript); B, complete verifier; C, prover; D, circuit compiler. Each phase is a standalone deliverable.

## Alternatives considered

- Reimplement the compiler first. Rejected: it is the largest block and the least security-critical; it would delay a verified verifier, which has independent value for relying parties.
- Never reimplement the compiler. Not chosen: the trusted input is to be reduced over time, and the final phase removes it.

## Consequences

- The loader is a Silver target over adversarial input from day one.
- Interoperability with upstream proofs is the exit criterion of phase B.
- The README trust model lists upstream-generated circuit files as trusted until phase D.

## Verification impact

- Provable: loader safety and well-formedness checks; evaluator semantics (Gold target in phase B).
- Tested: interoperability on real upstream proofs and circuits.
- Trusted: upstream circuit files until phase D.
- Constant time: no effect at this level; the verifier handles public data.

## References

- README, "Trust model".
- draft-google-cfrg-libzk-03 (circuit format sections are cited when the loader is written).
- `docs/guide/verification-approach.md`.
