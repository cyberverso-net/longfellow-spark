# 0017 P-256 base field: test anchors

## Status

Proposed

## Date

2026-10-09

## Context

As in stage 1, the proofs relate the implementation to a model (here the integer value), and vectors must anchor the model and the encoding to the outside world. What is available was checked against the clone at d5e6be7 and the draft text on 2026-10-09:

- The draft gives no P-256 field arithmetic vectors. Appendix B.2 (Fiat-Shamir) states its prime explicitly, and it is 2^256 - 2^32 - 977, the secp256k1 prime, not p; all sixteen values of B.2.2 happen to be below both primes, so the vectors themselves cannot tell the fields apart, and they are challenge-derivation vectors in any case. Appendix B.3.2 calls its field "P-256 Scalar Field (Field ID 2)", contradicting Table 1 (FieldID 0x01, base field), but the order it prints is the base field prime p. These are protocol-level vectors, not field vectors, and are logged as spec issues.
- Upstream C++ `lib/algebra/fp_test.cc` has property tests (commutativity, inverses, Montgomery round trips) and fixed values for other field sizes, no fixed P-256 field vectors. The Rust reference anchors behaviour: `from_bytes` rejects values >= p, `sumcheck_eval_points` are 0, 1, 2, sampling is by rejection.
- The NIST P-256 curve parameters are public constants: the base point G = (Gx, Gy) satisfies Gy^2 = Gx^3 - 3 Gx + b mod p. Checked locally with Python on 2026-10-09 with the values as commonly published; the constants are to be re-read from the published text (SEC 2 v2.0 Section 2.4.2; NIST SP 800-186) before they enter the vector file, and the file cites the source.

## Decision (proposed)

- Vector files `tests/vectors/p256_*.txt`, same conventions as [0009](0009-known-answer-vectors.md): one case per line, values as 64 hex digits of the integer (big-endian notation for readability), plus a byte-encoding file in the 32-byte little-endian form of Section 7.2.1 for `From_Bytes` and `To_Bytes`.
- Tier (a), external anchors: the curve equation at the base point, which exercises `Mul`, `Square`, `Add`, `Sub` and the constant b in one identity (`Mul (Gy, Gy) = Sub (Sub (Mul (Mul (Gx, Gx), Gx), Mul (Three, Gx)), Neg (b))` arranged as separate cases with the intermediate values); `Inv` on the coordinates; the identities (p - 1)^2 = 1, 2^256 mod p = 2^224 - 2^192 - 2^96 + 1 (the fold identity), (p + 1) / 2 as the inverse of two.
- Tier (b), structural: zero, one, p - 1, 2^64, 2^128, 2^192, 2^255, boundary products whose 512-bit result has specific fold patterns, `From_Bytes` acceptance at p - 1, p, p + 1, all-ones.
- Tier (c), random cases from an independent Python reference (plain integer arithmetic with `%`, nothing limb-wise), fixed seed; for inversion, Fermat and extended Euclid must agree.
- The generator recomputes every anchor and aborts on mismatch; it also checks the fold identities and the inversion chain exponent used by the implementation.

## Alternatives considered

- **Instrument the upstream C++ to emit field vectors.** Unnecessary at the field level; planned for protocol-level intermediate states in later phases.
- **Use Appendix B.3.2 proof vectors as field anchors.** Rejected: they test the whole protocol, and their field labelling is inconsistent; they return as end-to-end vectors in phase B.
- **Use the curve group law (scalar multiplication) as an anchor.** Out of scope: the project needs the base field, not curve arithmetic; the single curve equation suffices as an external identity.

## Consequences

- The vector generator is the second independent implementation of the field, in Python integers.
- The spec issues above are recorded in the project notes and reported upstream when the draft is next revised.

## Verification impact

- Provable: nothing (tests).
- Tested: encoding, canonical acceptance, the model against public constants, inversion.
- Trusted: the published curve constants.
- Constant time: no effect.

## References

- draft-google-cfrg-libzk-03, Table 1, Sections 3.4.3, 7.2.1, Appendix B.2 and B.3.2.
- google/longfellow-zk at d5e6be7: `lib/algebra/fp_test.cc`, `docs/specs/rust/src/algebra/p256.rs`.
- SEC 2 v2.0, Section 2.4.2 (secp256r1 parameters); NIST SP 800-186 (P-256).
