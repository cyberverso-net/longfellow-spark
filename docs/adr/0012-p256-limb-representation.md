# 0012 P-256 base field: limb representation

## Status

Accepted (2026-10-09, after review)

## Date

2026-10-09

## Context

Stage 2 implements arithmetic in F_p for the NIST P-256 base field prime p = 2^256 - 2^224 + 2^192 + 2^96 - 1 (draft-03 Table 1, FieldID 0x01; serialised as 32 bytes little-endian, Section 7.2.1). A 256-bit integer must be split into machine words, and the split decides three things at once: how many verification conditions the proofs generate, how products and carries are bounded, and how serialisation and equality are implemented.

Facts established for this record:

- Upstream C++ (`lib/algebra/fp_p256.h` at d5e6be7) uses four 64-bit limbs, little-endian limb order (`kModulus = {FFFFFFFFFFFFFFFF, FFFFFFFF, 0, FFFFFFFF00000001}`), with a 32-bit variant for targets without 64-bit multiply. The Rust reference (`docs/specs/rust/src/algebra/p256.rs`) stores 32 little-endian bytes and computes with a big-integer library.
- GNAT 16 provides `Interfaces.Unsigned_128` on this target and GNATprove accepts it: a feasibility experiment proved the postcondition of a 64x64 to 128-bit product and the range checks of its high and low halves at level 2.
- SPARKNaCl (Curve25519, 16 limbs of 16 bits held in 64-bit signed integers) makes bound propagation provable with limb subtypes and `Dynamic_Predicate` (`Normal_GF`, `Product_GF`, `Seminormal_GF`), but states no functional property against a mathematical value; its proofs are type safety plus bound properties (README and `sparknacl.ads`, read 2026-10-09).

## Decision

Four 64-bit limbs, saturated (each limb holds a full 64 bits of the value), little-endian limb order: `Limbs (0)` is the least significant word, so `To_Int (E) = sum of Limbs (i) * 2^(64 i)`. Partial products are formed in `Unsigned_128` and split into halves. This is the upstream C++ layout, and serialisation to the 32 bytes of Section 7.2.1 is a byte copy of the limbs in order.

## Alternatives considered

- **Eight 32-bit limbs, saturated, 64-bit products.** Portable to 32-bit targets without `Unsigned_128`. Twice the limbs: twice the loop iterations to specify, four times the partial products in multiplication (64 instead of 16), proportionally more verification conditions and longer invariants. Rejected for now; the 32-bit C++ variant shows the reduction is expressible this way if portability ever forces it.
- **Unsaturated radix (for example five limbs of 52 bits, or nine of 29 bits).** Delays carries, which is excellent for performance and for bounding sums (the SPARKNaCl technique). But values have many representations, so equality and serialisation need a normalisation step with its own proof, the canonical-form invariant ([0015](0015-p256-canonical-form-and-conditional-subtraction.md)) becomes a relation rather than a comparison, and the Solinas reduction ([0013](0013-p256-reduction-strategy.md)) does not line up with the limb boundaries. Rejected for a verifier reference where clarity of the model matters more than speed.
- **SPARKNaCl-style sixteen 16-bit limbs in signed 64-bit words.** Bound proofs are easy and well documented, but the technique was developed for a pseudo-Mersenne prime (2^255 - 19) whose reduction is a multiply by 38; P-256 has no such shape, and SPARKNaCl did not pursue a value-level model, which is the whole point here. Rejected.

## Consequences

- The ghost model is a four-term sum; the experiment proved limb addition with carry against it at level 2 with one hand-written lemma (the 128-bit split lemma, proved by assertions, no axiom).
- Multiplication produces sixteen 128-bit partial products accumulated into eight 64-bit words plus carries; its proof is the main risk of the stage and is treated in [0014](0014-p256-functional-specification-and-ghost-model.md).
- `Unsigned_128` ties the library to 64-bit targets. Recorded as an accepted limitation.

## Verification impact

- Provable: representation-to-value correspondence is a direct ghost function; equality of elements is equality of limbs once canonical form holds.
- Tested: serialisation round trips against the Python reference and the Rust byte layout.
- Trusted: GNAT's implementation of 128-bit arithmetic (part of the already trusted compiler).
- Constant time: fixed-width word operations; no effect beyond [0006](0006-constant-time-discipline-and-scope.md).

## References

- draft-google-cfrg-libzk-03, Table 1, Section 7.2.1.
- google/longfellow-zk at d5e6be7: `lib/algebra/fp_p256.h`, `lib/algebra/fp_generic.h`, `lib/algebra/nat.h` (`of_bytes`, little-endian), `docs/specs/rust/src/algebra/p256.rs`.
- SPARKNaCl, `src/sparknacl.ads` and README (rod-chapman/SPARKNaCl, master, read 2026-10-09).
