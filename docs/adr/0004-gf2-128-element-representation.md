# 0004 GF(2^128) element representation

## Status

Accepted

## Date

2026-10-06 (retroactive record, written 2026-10-09)

## Context

Elements of GF(2^128) are polynomials of degree below 128 over GF(2). The draft defines the field as GF(2)[x] / Q(x) with Q(x) = x^128 + x^7 + x^2 + x + 1 and reads 16 bytes as polynomial coefficients (Section 3.4.3), serialised little-endian (Section 7.2.1). The upstream Rust reference holds an element as a `u128` whose bit i is the coefficient of x^i and serialises it with `to_le_bytes`. GHASH/GCM uses the same polynomial with a reflected bit order, so GCM test vectors are not reusable without re-encoding.

## Decision

An element is a record holding an array of two `Unsigned_64` limbs in little-endian limb order: `Limbs (0)` holds bits 0 to 63, `Limbs (1)` holds bits 64 to 127, and bit i is the coefficient of x^i. The constant `Reduction_Low = 16#87#` encodes x^128 mod Q(x) = x^7 + x^2 + x + 1. The ghost function `Bit (E, I)` defines the coefficient of x^I and is the vocabulary of every contract.

This is bit-for-bit the layout of the upstream `u128`, so upstream constants are usable as literals without conversion: the 32 hex digits of a `u128` literal are, in order, `Limbs (1)` then `Limbs (0)`.

## Alternatives considered

- A single 128-bit modular type. Rationale not recorded at the time. What is known: two 64-bit limbs are portable across GNAT targets and match the limb-wise structure of the upstream C++ (`std::array<uint64_t, 2>` in `lib/gf2k/gf2_128_test.cc`); a 128-bit type was not evaluated in writing.
- GCM reflected bit order. Rejected explicitly in the package header: the draft uses coefficient order, and reflected vectors would silently encode a different element.
- Sixteen bytes. Not considered in writing; it would make `Xtime` and masking byte-wise and slower with no gain for proofs.

## Consequences

- `Xtime` is a shift by one across the two limbs with the carry folded onto `Reduction_Low`.
- Vectors are written in upstream notation, see [0009](0009-known-answer-vectors.md).
- The GF(2^16) subfield basis (beta_i = g^i with g = x^((2^128 - 1) / (2^16 - 1))) is not represented specially; the tower is to be modelled explicitly when the sumcheck and Ligero layers need it.

## Verification impact

- Provable: the representation is fixed, so bit-level contracts (`Xtime`, `Add`) are exact statements about limbs; predicates and loop invariants speak in terms of `Bit`.
- Tested: that this layout is the draft's convention (not just the upstream one) is anchored by the subfield basis vectors, see [0009](0009-known-answer-vectors.md).
- Trusted: nothing additional.
- Constant time: limb operations are fixed-width shifts, ands and xors; no effect beyond [0006](0006-constant-time-discipline-and-scope.md).

## References

- draft-google-cfrg-libzk-03, Sections 2.2.2, 3.4.3, 7.2.1.
- google/longfellow-zk at d5e6be77336933d50bf7f25a954f8ec273eb51ce: `docs/specs/rust/src/algebra/gf2_128.rs` (`u128`, `to_le_bytes`, reduction by `0x87`), `lib/gf2k/gf2_128_test.cc` (two-limb literal in test Beta).
- `src/gf2_128.ads`, types `Limb_Index`, `Limb_Array`, `Element`, function `Bit`.
