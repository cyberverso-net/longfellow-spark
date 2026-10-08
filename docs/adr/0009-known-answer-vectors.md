# 0009 Known-answer vectors: notation, tiers, anchors

## Status

Accepted

## Date

2026-10-08 (retroactive record, written 2026-10-09)

## Context

The proof of `Mul` establishes equality with the ghost reference `Mul_Ref` ([0005](0005-mul-ref-as-proof-target.md)), not with the draft. The draft gives no GF(2^128) arithmetic vectors, and GCM vectors use a reflected bit order. Something external to this repository must anchor the convention, and random self-consistency tests cannot do that: a reference that agrees with itself proves nothing about the encoding.

## Decision

- Vector files live in `tests/vectors/`, plain text, one case per line, `op operands expected`, values as 32 hex digits, big-endian, of the 128-bit integer whose bit i is the coefficient of x^i. This is the notation of the upstream literals, so anchors are copied verbatim.
- Three tiers, labelled in the file: (a) external anchors, (b) structural cases from the definition, (c) random cases with a fixed seed.
- The external anchors are the sixteen subfield basis constants beta_i = g^i, g = x^((2^128 - 1) / (2^16 - 1)), copied from google/longfellow-zk at commit d5e6be77336933d50bf7f25a954f8ec273eb51ce, and the known x^-1. They are genuinely external: a wrong polynomial, a wrong bit order or a wrong reduction constant changes g, and therefore every beta_i, and the upstream constants were produced by independent code (C++ and Rust, which agree with each other).
- The generator `gen_gf2_128_vectors.py` is a reference written from scratch with a structure different from `Mul_Ref` and from the upstream Rust: schoolbook carry-less product to 255 bits, then long division by Q(x); exponentiation by square-and-multiply on top. It recomputes the anchors and aborts with a non-zero status on any mismatch with the embedded upstream constants. For inversion it computes every expected value twice, by Fermat and by extended Euclid, and requires agreement.
- Seed and case counts are fixed in the script; output is deterministic and committed.

## Alternatives considered

- Import GCM vectors. Rejected: reflected bit order; they would encode different elements.
- Extract vectors by instrumenting the upstream C++. Not needed at stage 1 since the basis constants already anchor the convention; it remains the plan for intermediate protocol states in later phases.
- A reference with the same Horner structure as `Mul_Ref`. Rejected: a shared structural bug would go unnoticed.

## Consequences

- The README trust model moves "Mul_Ref matches the draft's convention" from claimed to tested, with the file named.
- 209 cases at stage 1 (105 mul, 48 square, 56 inv).
- Upstream is cloned read-only outside the repository; only constants, paths and the commit hash enter it.

## Verification impact

- Provable: nothing; vectors are tests.
- Tested: the encoding convention and the reduction constant against upstream; squaring and inversion against two independent references.
- Trusted: that the upstream constants are themselves correct for the draft (two upstream implementations agree, and an independent recomputation agrees).
- Constant time: no effect.

## References

- draft-google-cfrg-libzk-03, Sections 2.2.2, 3.4.3, 7.2.1.
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/algebra/gf2_128.rs` (`SUBFIELD_BASIS`), `lib/gf2k/gf2_128_test.cc` (test Beta).
- `tests/vectors/gen_gf2_128_vectors.py`, `tests/vectors/gf2_128_{mul,square,inv}.txt`.
