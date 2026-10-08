#!/usr/bin/env python3
"""Generator for the GF(2^128) known-answer vectors:
  gf2_128_mul.txt     mul <a> <b> <expected>
  gf2_128_square.txt  square <a> <expected>
  gf2_128_inv.txt     inv <a> <expected>

Independent reference implementation of multiplication in
GF(2)[x] / Q(x), Q(x) = x^128 + x^7 + x^2 + x + 1 (IETF
draft-google-cfrg-libzk-03, Section 2.2.2). Elements are Python integers
with bit i holding the coefficient of x^i (draft-03 Section 3.4.3; the
upstream Rust reference uses a u128 with the same convention).

The structure is deliberately different from the SPARK ghost reference
Mul_Ref (MSB-first Horner with interleaved reduction): here the full
255-bit carry-less schoolbook product is formed first, then reduced by
long division. Exponentiation is square-and-multiply on top of it.

Tier (a) anchors are checked against constants copied verbatim from the
upstream reference implementation, google/longfellow-zk at commit
d5e6be77336933d50bf7f25a954f8ec273eb51ce (2026-09-30):
  docs/specs/rust/src/algebra/gf2_128.rs  (SUBFIELD_BASIS, 16 values)
  lib/gf2k/gf2_128_test.cc                (test Beta, beta_1 as two limbs)
Any mismatch aborts generation with a non-zero exit status.

Usage: python3 -I gen_gf2_128_vectors.py [output-directory]
Output is deterministic (fixed seed, no timestamps).
"""

import random
import sys
from pathlib import Path

# Q(x) = x^128 + x^7 + x^2 + x + 1
Q = (1 << 128) | 0x87
MASK128 = (1 << 128) - 1
X = 2  # the element x

SEED = 20261008
RANDOM_CASES = 64
RANDOM_SQUARE_CASES = 32
RANDOM_INV_CASES = 32

# docs/specs/rust/src/algebra/gf2_128.rs, const SUBFIELD_BASIS, verbatim.
UPSTREAM_SUBFIELD_BASIS = [
    0x1,
    0x5c5971877501d4b8f1871e01b64fda4c,
    0x8bb99658eaf2cae0a6e310fb6e176ea8,
    0xb61e08da12f9665c3f8de8a2f9ff7eed,
    0xa76c2e634c6483ae9ba3282087a3f827,
    0x54944ff4a5269cedf7af4e93629f689e,
    0x5439ecfd75a950d8d0765f1873309b88,
    0x49ecdfbe06777b02e566f9fc3d9b58a2,
    0x97a401b733e66a9319af205497f8e2d0,
    0x789fd7793ce7523860e4dbdce9777814,
    0xaa440b2d4b546256c0f157187adbc05b,
    0x79f2cadb70b6115d222f207d0d8ad9f9,
    0xae72af7894ce037df6d1f84fb66c52b8,
    0xd6f226d783d454db4af94ef056d28a30,
    0x057d918d494925fc0f37a0a4d91b4220,
    0x18d4bbb6833c5ae8b683012350e55753,
]

# lib/gf2k/gf2_128_test.cc, TEST(GF2_128, Beta):
#   std::array<uint64_t, 2> want = {0xF1871E01B64FDA4Cull, 0x5C5971877501D4B8ull};
# limb 0 holds bits 0..63, limb 1 holds bits 64..127.
UPSTREAM_CC_BETA_1_LIMBS = (0xF1871E01B64FDA4C, 0x5C5971877501D4B8)

# x^-1, verified in the previous session; x * x^-1 = 1 is checked below.
X_INV = 0x80000000000000000000000000000043


def clmul(a: int, b: int) -> int:
    """Carry-less schoolbook product of two 128-bit polynomials (255 bits)."""
    assert 0 <= a <= MASK128 and 0 <= b <= MASK128
    p = 0
    for i in range(128):
        if (b >> i) & 1:
            p ^= a << i
    return p


def reduce(p: int) -> int:
    """Long division of a polynomial of degree < 256 by Q(x); the remainder."""
    assert 0 <= p < (1 << 256)
    for i in range(255, 127, -1):
        if (p >> i) & 1:
            p ^= Q << (i - 128)
    assert p <= MASK128
    return p


def mul(a: int, b: int) -> int:
    return reduce(clmul(a, b))


def power(a: int, e: int) -> int:
    """Square-and-multiply, MSB first."""
    assert e >= 0
    r = 1
    for i in range(e.bit_length() - 1, -1, -1):
        r = mul(r, r)
        if (e >> i) & 1:
            r = mul(r, a)
    return r


def inv_fermat(a: int) -> int:
    return power(a, 2**128 - 2)


def inv_euclid(a: int) -> int:
    """Extended Euclid on polynomials over GF(2); independent of Fermat."""
    assert 1 <= a <= MASK128
    r0, r1 = Q, a
    s0, s1 = 0, 1
    while r1 != 1:
        # q, rem = divmod(r0, r1) over GF(2)[x]
        q = 0
        rem = r0
        while rem.bit_length() >= r1.bit_length():
            shift = rem.bit_length() - r1.bit_length()
            q ^= 1 << shift
            rem ^= r1 << shift
        r0, r1 = r1, rem
        s0, s1 = s1, s0 ^ reduce(clmul(q, s1))
        assert r1 != 0, "a is not invertible (zero or divisor of Q)"
    return s1


def hx(v: int) -> str:
    return f"{v:032x}"


def fail(msg: str) -> None:
    print(f"gen_gf2_128_vectors: FAILED: {msg}", file=sys.stderr)
    sys.exit(1)


def main() -> None:
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent

    # ---- Tier (a): external anchors ------------------------------------
    assert (2**128 - 1) % (2**16 - 1) == 0
    e = (2**128 - 1) // (2**16 - 1)
    g = power(X, e)
    if g == 1:
        fail("g = x^e is 1; x would not generate the multiplicative group")
    if power(g, 2**16 - 1) != 1:
        fail("g^(2^16 - 1) /= 1; g does not lie in GF(2^16)")

    beta = [power(g, i) for i in range(16)]
    for i in range(16):
        if beta[i] != UPSTREAM_SUBFIELD_BASIS[i]:
            fail(f"beta_{i} = {hx(beta[i])} but upstream Rust has "
                 f"{hx(UPSTREAM_SUBFIELD_BASIS[i])}")
    lo, hi = UPSTREAM_CC_BETA_1_LIMBS
    if beta[1] != (hi << 64) | lo:
        fail("beta_1 does not match the C++ test Beta limbs")
    if mul(X, X_INV) != 1:
        fail(f"x * x^-1 = {hx(mul(X, X_INV))}, expected 1")

    tier_a = []
    for i in range(15):
        tier_a.append((beta[i], g, beta[i + 1]))          # beta_i * g = beta_(i+1)
    for i, j in ((1, 1), (2, 3), (4, 4), (7, 8), (3, 12)):
        tier_a.append((beta[i], beta[j], beta[i + j]))    # beta_i * beta_j = beta_(i+j)
    tier_a.append((X, X_INV, 1))
    tier_a.append((X_INV, X, 1))

    # ---- Tier (b): structural cases from the definition ---------------
    all_ones = MASK128
    tier_b = [
        (1, 1, 1),
        (1, beta[1], beta[1]),
        (beta[1], 1, beta[1]),
        (0, beta[1], 0),
        (beta[1], 0, 0),
        (0, 0, 0),
        (1 << 127, X, 0x87),                    # x^127 * x = x^128 = x^7 + x^2 + x + 1
        (X, 1 << 127, 0x87),
        (1 << 127, 1 << 1, 0x87),               # same, operand order and width
        (1 << 126, 1 << 2, 0x87),
        (1 << 64, 1 << 64, 0x87),               # limb boundary
        (1 << 63, 1 << 1, 1 << 64),             # cross-limb carry, no reduction
        (1 << 127, 1 << 2, 0x87 << 1),          # x^129
        (1 << 127, 1 << 127, mul(1 << 127, 1 << 127)),  # x^254, two reduction rounds
        ((1 << 127) | 1, X, 0x87 ^ X),          # (x^127 + 1) * x
        (X_INV, X_INV, mul(X_INV, X_INV)),      # x^-2
        (all_ones, all_ones, mul(all_ones, all_ones)),
        (all_ones, X, mul(all_ones, X)),
        (all_ones, 1 << 127, mul(all_ones, 1 << 127)),
    ]
    # Cross-check the computed structural results by an independent route.
    assert mul(1 << 127, 1 << 127) == power(X, 254)
    assert mul(mul(X_INV, X_INV), mul(X, X)) == 1

    # ---- Tier (c): random cases ---------------------------------------
    rng = random.Random(SEED)
    tier_c = []
    for _ in range(RANDOM_CASES):
        a = rng.getrandbits(128)
        b = rng.getrandbits(128)
        tier_c.append((a, b, mul(a, b)))

    # ---- Emit ---------------------------------------------------------
    lines = []
    w = lines.append
    w("# Known-answer vectors for GF(2^128) multiplication, Longfellow ZK.")
    w("# Generated by gen_gf2_128_vectors.py (this directory); do not edit by hand.")
    w("#")
    w("# Field: GF(2)[x] / Q(x), Q(x) = x^128 + x^7 + x^2 + x + 1")
    w("#   (IETF draft-google-cfrg-libzk-03, Section 2.2.2).")
    w("# Encoding: each value is the 128-bit integer whose bit i is the")
    w("#   coefficient of x^i (Section 3.4.3), written as 32 hex digits,")
    w("#   big-endian, the notation of the upstream literals. The byte")
    w("#   serialisation of Section 7.2.1 (little-endian) is not used here.")
    w("# Format: one case per line:  mul <a> <b> <expected>  with a * b = expected.")
    w("#")
    w("# Section A: external anchors. g = x^((2^128 - 1) / (2^16 - 1)) and")
    w("#   beta_i = g^i, i = 0 .. 15, were recomputed by the generator and")
    w("#   checked against SUBFIELD_BASIS in docs/specs/rust/src/algebra/gf2_128.rs")
    w("#   and test Beta in lib/gf2k/gf2_128_test.cc of google/longfellow-zk,")
    w("#   commit d5e6be77336933d50bf7f25a954f8ec273eb51ce (2026-09-30).")
    w("#   Cases: beta_i * g = beta_(i+1); beta_i * beta_j = beta_(i+j);")
    w("#   x * x^-1 = 1 with x^-1 = 0x80000000000000000000000000000043.")
    w(f"# g = {hx(g)}")
    for i in range(16):
        w(f"# beta_{i:<2} = {hx(beta[i])}")
    for a, b, r in tier_a:
        w(f"mul {hx(a)} {hx(b)} {hx(r)}")
    w("#")
    w("# Section B: structural cases from the definition. Identity, zero,")
    w("#   x^127 * x = x^128 = 0x87, limb boundary (x^64 * x^64), cross-limb")
    w("#   carry without reduction, two reduction rounds (x^254), all-ones.")
    for a, b, r in tier_b:
        w(f"mul {hx(a)} {hx(b)} {hx(r)}")
    w("#")
    w(f"# Section C: {RANDOM_CASES} random cases from the generator's")
    w("#   schoolbook-then-long-division reference, Python random.Random")
    w(f"#   with seed {SEED}, operands drawn as getrandbits(128) in order a, b.")
    for a, b, r in tier_c:
        w(f"mul {hx(a)} {hx(b)} {hx(r)}")

    mul_path = out_dir / "gf2_128_mul.txt"
    mul_path.write_text("\n".join(lines) + "\n")
    print(f"wrote {mul_path}: {len(tier_a)} anchor, {len(tier_b)} structural, "
          f"{len(tier_c)} random cases; upstream anchors verified")

    # ---- Squaring ------------------------------------------------------
    # Anchors: beta_i^2 = beta_(2i) for i = 0 .. 7, all upstream constants.
    sq_a = [(beta[i], beta[2 * i]) for i in range(8)]
    sq_b = [
        (0, 0),
        (1, 1),
        (X, 1 << 2),
        (1 << 63, 1 << 126),                    # no reduction, crosses the limb boundary
        (1 << 64, 0x87),                        # x^128
        (1 << 127, mul(1 << 127, 1 << 127)),    # x^254
        (X_INV, mul(X_INV, X_INV)),             # x^-2
        (all_ones, mul(all_ones, all_ones)),
    ]
    sq_c = []
    for _ in range(RANDOM_SQUARE_CASES):
        a = rng.getrandbits(128)
        sq_c.append((a, mul(a, a)))
    # Squaring is linear in characteristic 2 (Frobenius); check the
    # reference against that property on the random cases.
    for (a, _), (b, _) in zip(sq_c, sq_c[1:]):
        if mul(a ^ b, a ^ b) != mul(a, a) ^ mul(b, b):
            fail("squaring is not additive in the reference")

    lines = []
    w = lines.append
    w("# Known-answer vectors for GF(2^128) squaring, Longfellow ZK.")
    w("# Generated by gen_gf2_128_vectors.py (this directory); do not edit by hand.")
    w("# Field, encoding and provenance: see gf2_128_mul.txt.")
    w("# Format: one case per line:  square <a> <expected>  with a * a = expected.")
    w("#")
    w("# Section A: external anchors, beta_i^2 = beta_(2i), i = 0 .. 7, every")
    w("#   value an upstream SUBFIELD_BASIS constant (commit d5e6be7).")
    for a, r in sq_a:
        w(f"square {hx(a)} {hx(r)}")
    w("#")
    w("# Section B: structural cases: zero, one, x, x^63, x^64 (x^128 = 0x87),")
    w("#   x^127 (x^254), x^-1, all-ones.")
    for a, r in sq_b:
        w(f"square {hx(a)} {hx(r)}")
    w("#")
    w(f"# Section C: {RANDOM_SQUARE_CASES} random cases, same generator state")
    w("#   continued after the mul cases; additivity of squaring checked.")
    for a, r in sq_c:
        w(f"square {hx(a)} {hx(r)}")
    sq_path = out_dir / "gf2_128_square.txt"
    sq_path.write_text("\n".join(lines) + "\n")
    print(f"wrote {sq_path}: {len(sq_a)} anchor, {len(sq_b)} structural, "
          f"{len(sq_c)} random cases")

    # ---- Inversion -----------------------------------------------------
    def inv_checked(a: int) -> int:
        f = inv_fermat(a)
        e = inv_euclid(a)
        if f != e:
            fail(f"Fermat and Euclid inverses differ for {hx(a)}")
        if mul(a, f) != 1:
            fail(f"a * inv(a) /= 1 for {hx(a)}")
        return f

    if inv_checked(X) != X_INV:
        fail("inv(x) does not match the known x^-1")
    # Anchors: inv(x) = x^-1; inv(beta_i) for i = 1 .. 15 lies in the
    # subfield, so it equals g^(65535 - i); checked against a * inv(a) = 1.
    inv_a = [(X, X_INV), (X_INV, X)]
    for i in range(1, 16):
        r = inv_checked(beta[i])
        if r != power(g, 65535 - i):
            fail(f"inv(beta_{i}) is not g^(65535 - {i})")
        inv_a.append((beta[i], r))
    # Structural: inv(0) = 0 by the design decision (Fermat chain on zero),
    # inv(1) = 1, x^2, x^64, x^127, all-ones, x + 1.
    inv_b = [(0, 0), (1, 1)]
    for a in (1 << 2, 1 << 64, 1 << 127, all_ones, X ^ 1):
        inv_b.append((a, inv_checked(a)))
    if inv_fermat(0) != 0:
        fail("Fermat chain on zero is not zero")
    inv_c = []
    for _ in range(RANDOM_INV_CASES):
        a = rng.getrandbits(128)
        inv_c.append((a, inv_checked(a)))

    lines = []
    w = lines.append
    w("# Known-answer vectors for GF(2^128) inversion, Longfellow ZK.")
    w("# Generated by gen_gf2_128_vectors.py (this directory); do not edit by hand.")
    w("# Field, encoding and provenance: see gf2_128_mul.txt.")
    w("# Format: one case per line:  inv <a> <expected>  with a * expected = 1,")
    w("#   except inv 0 = 0 (total function, documented design decision).")
    w("# Every expected value was computed by Fermat (a^(2^128 - 2)) and by")
    w("#   extended Euclid on GF(2)[x] independently; both agree and a * inv = 1.")
    w("#")
    w("# Section A: anchors: inv(x) = x^-1 and back; inv(beta_i), i = 1 .. 15,")
    w("#   each equal to g^(65535 - i) with beta_i an upstream constant.")
    for a, r in inv_a:
        w(f"inv {hx(a)} {hx(r)}")
    w("#")
    w("# Section B: structural: zero (= 0), one, x^2, x^64, x^127, all-ones, x + 1.")
    for a, r in inv_b:
        w(f"inv {hx(a)} {hx(r)}")
    w("#")
    w(f"# Section C: {RANDOM_INV_CASES} random cases, generator state continued")
    w("#   after the square cases.")
    for a, r in inv_c:
        w(f"inv {hx(a)} {hx(r)}")
    inv_path = out_dir / "gf2_128_inv.txt"
    inv_path.write_text("\n".join(lines) + "\n")
    print(f"wrote {inv_path}: {len(inv_a)} anchor, {len(inv_b)} structural, "
          f"{len(inv_c)} random cases; Fermat and Euclid agree")


if __name__ == "__main__":
    main()
