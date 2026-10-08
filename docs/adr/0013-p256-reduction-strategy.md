# 0013 P-256 base field: reduction strategy

## Status

Proposed

## Date

2026-10-09

## Context

The product of two 256-bit values has 512 bits and must be reduced modulo p. Three families exist: Montgomery multiplication, which keeps elements in the form a * R mod p (R = 2^256) and reduces word by word; the Solinas (NIST) reduction, which exploits p = 2^256 - 2^224 + 2^192 + 2^96 - 1 to fold the high words onto the low ones with a fixed pattern of additions and subtractions; and Barrett reduction, which estimates the quotient with a precomputed reciprocal.

Upstream C++ (`fp_generic.h`, `fp_p256.h`) uses Montgomery form with a P-256-specific reduction step; for this prime the Montgomery constant m' = -p^-1 mod 2^64 equals 1 (checked), so each step adds a0 * p shifted, which the C++ writes out as a handful of word adds and subtracts. The Rust reference reduces with a big-integer library and stores canonical values. Serialisation (Section 7.2.1) is the canonical integer, little-endian; the Rust `from_bytes` rejects values >= p.

## Decision (proposed)

Direct (non-Montgomery) representation with Solinas reduction, structured in proof-sized steps:

1. Schoolbook product into eight 64-bit words (value equality, no modulus).
2. Fold: rewrite the high 256 bits using 2^256 = 2^224 - 2^192 - 2^96 + 1 (mod p). Each fold is a fixed linear combination of the high words added to the low words, with signed terms handled as additions of p-multiples so that intermediate values stay non-negative; the postcondition of each fold is "same value mod p, bounded by a stated multiple of p".
3. A fixed number of constant-time conditional subtractions of p to reach canonical form ([0015](0015-p256-canonical-form-and-conditional-subtraction.md)).

Each step has its own ghost specification against the big-integer model ([0014](0014-p256-functional-specification-and-ghost-model.md)), so the proof of `Mul` is a composition of three smaller proofs.

## Alternatives considered

- **Montgomery, as upstream C++.** Fastest in practice and the natural choice for a prover. For proofs it has two costs: the representation invariant involves R^-1 mod p, so the model of an element is `To_Int (E) * R_Inv mod p`, and every statement carries a modular inverse that SMT solvers handle poorly; and serialisation requires a conversion out of Montgomery form, which must itself be proved to keep the trust model honest. Interoperability does not require Montgomery form: bytes are canonical integers either way. Not chosen for the verifier; it may return as a prover-side optimisation behind the same contracts.
- **Barrett.** Generic, one 512-by-256 estimate and two corrections; no use of the special form of p, so no simpler than Solinas and with a harder bound argument. Rejected.
- **Solinas with the classical nine-term 32-bit formulation (FIPS 186-4 style).** Correct and well known, but written over 32-bit words it produces a result in a wide range requiring several corrections, and the sign handling is intricate. The two-fold formulation over 64-bit words proposed here has fewer terms per step and a cleaner bound; the exact fold equations and bounds are to be derived and checked numerically before coding, and recorded in the chapter.

## Consequences

- The model statement for every operation is the plain one, `To_Int (Op (A, B)) = f (To_Int (A), To_Int (B)) mod p`, and `From_Bytes` is a copy plus a comparison.
- Performance is secondary and accepted as such; the folds cost a few dozen word operations.
- The exact fold identities and intermediate bounds are a design input to the chapter and must be fixed before implementation.

## Verification impact

- Provable: steps 1 and 2 are linear identities over the model once the split lemma and the fold identity are available as lemmas; step 3 is the conditional subtraction lemma. Level 2 is the target, with staged fallback per [0014](0014-p256-functional-specification-and-ghost-model.md).
- Tested: random products against the Python reference; the fold identity itself checked numerically in the generator.
- Trusted: nothing new.
- Constant time: fixed fold pattern and masked conditional subtractions; no data-dependent control flow.

## References

- draft-google-cfrg-libzk-03, Table 1, Section 7.2.1.
- google/longfellow-zk at d5e6be7: `lib/algebra/fp_generic.h` (Montgomery form, `reduction_step`, `from_montgomery`), `lib/algebra/fp_p256.h` (`Fp256Reduce`, m' = 1), `docs/specs/rust/src/algebra/p256.rs` (`from_bytes`, canonical check).
- NIST SP 800-186 (P-256 parameters) and SEC 2 v2.0 Section 2.4.2 for p; FIPS 186-4 Appendix D.2.3 for the classical reduction formulation (the section number is to be confirmed against the published text before the chapter cites it).
