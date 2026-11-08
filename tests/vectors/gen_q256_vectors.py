#!/usr/bin/env python3
"""Generator for the P-256 scalar field known-answer vectors (block 6 of
Phase D, ADR 0086):
  q256_field.txt  add <a> <b> <expected>, sub <a> <b> <expected>, neg <a> <expected>,
                  mul <a> <b> <expected>, square <a> <expected>, inv <a> <expected>,
                  frombytes <32 bytes as 64 hex digits in memory order> <ok> <value>

Field: integers modulo q, the order of the group of NIST P-256,
q = FFFFFFFF 00000000 FFFFFFFF FFFFFFFF BCE6FAAD A7179E84 F3B9CAC2 FC632551
(RFC 5903 Section 3.1, printed there as n; Q256Field upstream). Elements
are serialised as 32 bytes little-endian, as the base field's; encodings
of values at or above q are rejected.

Values in the vector files are written as 64 hex digits of the integer,
most significant digit first; the bytes cases additionally give the 32
serialised bytes in memory order.

Independent reference: plain Python integers with %, nothing limb-wise.
Inversion is computed by Fermat (a^(q - 2)) and by extended Euclid; both
must agree.

External anchors: the order q and the base point of P-256 as printed in
RFC 5903 Section 3.1; the generator checks that q G is the point at
infinity with a plain double-and-add over affine coordinates, and aborts
otherwise.

This script also checks the constants of Q256_Field (the Montgomery form,
ADR 0069): One = 2^256 mod q, R_Inv = 2^-256 mod q with 2^256 R_Inv = 1 +
K q, R2 = 2^512 mod q with R2 R_Inv = 2^256 + K2 q, q' = -q^-1 mod 2^64
with q' q_0 = K_Q 2^64 + 2^64 - 1, and the 64 nibbles of the window chain
of Inv, which must read q - 2.

Usage: python3 -I gen_q256_vectors.py [output-directory]
Output is deterministic (fixed seed, no timestamps).
"""

import random
import sys
from pathlib import Path

Q = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
P = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
MASK256 = 2**256 - 1
W64 = 2**64

SEED = 20261108
RANDOM_CASES = 64
RANDOM_INV_CASES = 32

# RFC 5903, Section 3.1, verbatim (spaces removed).
RFC5903_N  = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
RFC5903_B  = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
RFC5903_GX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
RFC5903_GY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5

# The constants of src/q256_field.ads and .adb, as limbs least significant first.
ONE_LIMBS = [0x0C46353D039CDAAF, 0x4319055258E8617B, 0x0000000000000000, 0x00000000FFFFFFFF]
RI_LIMBS = [0xCE1BC8F79C197C79, 0xBADEF3E243566FAF, 0x07F8B6041E607725, 0x60D066334905C1E9]
K_LIMBS = [0xCCD1C8AAEE00BC4F, 0x48C944087D74D2E4, 0x50FE77ECC588C6F6, 0x60D06633A9D6281C]
R2_LIMBS = [0x83244C95BE79EEA2, 0x4699799C49BD6FA6, 0x2845B2392B6BEC59, 0x66E12D94F3D95620]
K2_LIMBS = [0xCE77C306C4F23CF2, 0x7C28A324CCA7670F, 0x35A309B37D79869D, 0x26E8311F5FBDC629]
Q_PRIME = 0xCCD1C8AAEE00BC4F
K_Q = 0xC2FFC74DCCAF771F
EXPONENT_NIBBLES = [0xF] * 8 + [0] * 8 + [0xF] * 16 + [
    0xB, 0xC, 0xE, 6, 0xF, 0xA, 0xA, 0xD, 0xA, 7, 1, 7, 9, 0xE, 8, 4,
    0xF, 3, 0xB, 9, 0xC, 0xA, 0xC, 2, 0xF, 0xC, 6, 3, 2, 5, 4, 0xF]


def fail(msg: str) -> None:
    print(f"gen_q256_vectors: FAILED: {msg}", file=sys.stderr)
    sys.exit(1)


def hx(v: int) -> str:
    assert 0 <= v < 2**256
    return f"{v:064x}"


def to_bytes_le(v: int) -> bytes:
    return v.to_bytes(32, "little")


def of_limbs(limbs) -> int:
    return sum(l << (64 * i) for i, l in enumerate(limbs))


def add(a, b): return (a + b) % Q
def sub(a, b): return (a - b) % Q
def neg(a): return (-a) % Q
def mul(a, b): return (a * b) % Q


def inv_fermat(a: int) -> int:
    return pow(a, Q - 2, Q)


def inv_euclid(a: int) -> int:
    assert 1 <= a < Q
    r0, r1, s0, s1 = Q, a, 0, 1
    while r1 != 1:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
        assert r1 != 0
    return s1 % Q


def inv_checked(a: int) -> int:
    f = inv_fermat(a)
    if f != inv_euclid(a):
        fail(f"Fermat and Euclid inverses differ for {hx(a)}")
    if mul(a, f) != 1:
        fail(f"a * inv(a) /= 1 for {hx(a)}")
    return f


# ---- The order, checked on the curve over affine coordinates ------------
def ec_add_affine(p1, p2):
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    (x1, y1), (x2, y2) = p1, p2
    if x1 == x2 and (y1 + y2) % P == 0:
        return None
    if p1 == p2:
        lam = (3 * x1 * x1 - 3) * pow(2 * y1, P - 2, P) % P
    else:
        lam = (y2 - y1) * pow(x2 - x1, P - 2, P) % P
    x3 = (lam * lam - x1 - x2) % P
    return (x3, (lam * (x1 - x3) - y1) % P)


def ec_mul_affine(k, pt):
    res = None
    while k:
        if k & 1:
            res = ec_add_affine(res, pt)
        pt = ec_add_affine(pt, pt)
        k >>= 1
    return res


def check_constants() -> None:
    if Q != RFC5903_N:
        fail("q does not match RFC 5903")
    if ec_mul_affine(Q, (RFC5903_GX, RFC5903_GY)) is not None:
        fail("q G is not the point at infinity")
    if ec_mul_affine(Q - 1, (RFC5903_GX, RFC5903_GY)) != (RFC5903_GX, (-RFC5903_GY) % P):
        fail("(q - 1) G is not -G")
    r = 2**256
    if of_limbs(ONE_LIMBS) != r % Q or r % Q != r - Q:
        fail("One")
    ri = of_limbs(RI_LIMBS)
    if (ri * r) % Q != 1:
        fail("R_Inv")
    if r * ri != 1 + of_limbs(K_LIMBS) * Q:
        fail("K")
    r2 = of_limbs(R2_LIMBS)
    if r2 != (r * r) % Q:
        fail("R2")
    if r2 * ri != r + of_limbs(K2_LIMBS) * Q:
        fail("K2")
    q0 = Q & (W64 - 1)
    if (Q_PRIME * q0) % W64 != W64 - 1:
        fail("q' is not -q^-1 mod 2^64")
    if Q_PRIME * q0 != K_Q * W64 + W64 - 1:
        fail("K_Q")
    e = 0
    for nib in EXPONENT_NIBBLES:
        e = (e << 4) | nib
    if len(EXPONENT_NIBBLES) != 64 or e != Q - 2:
        fail("the window chain of Inv does not read q - 2")
    print("constants: q G = O, One, R_Inv, K, R2, K2, q', K_Q verified;"
          " inversion chain: 252 squarings, 77 multiplications, exponent q - 2 verified")


def main() -> None:
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent
    check_constants()
    rng = random.Random(SEED)
    gx, gy, b = RFC5903_GX, RFC5903_GY, RFC5903_B
    half = inv_checked(2)
    if half != (Q + 1) // 2:
        fail("inverse of two")

    lines = []
    w = lines.append
    w("# Known-answer vectors for the P-256 scalar field (the order q of the group).")
    w("# Generated by gen_q256_vectors.py (this directory); do not edit by hand.")
    w("# Field: integers mod q = FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551")
    w("#   (RFC 5903 Section 3.1, printed there as n).")
    w("# Values: 64 hex digits of the integer, most significant first.")
    w("# Format: add <a> <b> <a+b>;  sub <a> <b> <a-b>;  neg <a> <-a>;")
    w("#   mul <a> <b> <ab>;  square <a> <a^2>;  inv <a> <a^-1> (inv 0 = 0);")
    w("#   frombytes <32 bytes as 64 hex digits in memory order> <ok> <value>.")
    w("#")
    w("# Section A: anchors: the coordinates of G and b of RFC 5903 reduced mod q,")
    w("#   the inverse of two, q - 1.")
    anchors = (gx % Q, gy % Q, b % Q, half, Q - 1)
    for a_, b_ in ((gx % Q, gy % Q), (gx % Q, b % Q), (Q - 1, 1), (Q - 1, Q - 1), (half, half)):
        w(f"add {hx(a_)} {hx(b_)} {hx(add(a_, b_))}")
    for a_, b_ in ((gx % Q, gy % Q), (gy % Q, gx % Q), (0, 1), (0, gx % Q), (1, Q - 1)):
        w(f"sub {hx(a_)} {hx(b_)} {hx(sub(a_, b_))}")
    for a_ in (0, 1, gx % Q, Q - 1, half):
        w(f"neg {hx(a_)} {hx(neg(a_))}")
    for a_, b_ in ((gx % Q, gy % Q), (half, 2), (Q - 1, Q - 1), (2**255 % Q, 2**255 % Q)):
        w(f"mul {hx(a_)} {hx(b_)} {hx(mul(a_, b_))}")
    for a_ in anchors:
        w(f"square {hx(a_)} {hx(mul(a_, a_))}")
    w("#")
    w("# Section B: structural: carries across every limb boundary, the wrap at q,")
    w("#   values just below q, the limbs of q themselves.")
    for a_, b_ in ((2**64 - 1, 1), (2**128 - 1, 1), (2**192 - 1, 1), (2**255, 2**255),
                   (Q - 1, 2), (Q - 2**64, 2**64), (2**256 - Q, Q - (2**256 - Q))):
        w(f"add {hx(a_ % Q)} {hx(b_ % Q)} {hx(add(a_ % Q, b_ % Q))}")
    for a_, b_ in ((2**64 - 1, 2**64 - 1), (2**128 - 1, 2**128 - 1), (Q - 1, 2), (Q - 1, 2**192)):
        w(f"mul {hx(a_)} {hx(b_)} {hx(mul(a_, b_))}")
    w("#")
    w("# Section C: inverses: 0 (total: 0), 1, 2, q - 1, G's coordinates, and random values;")
    w("#   each checked by Fermat and by Euclid in the generator.")
    w(f"inv {hx(0)} {hx(0)}")
    for a_ in (1, 2, Q - 1, gx % Q, gy % Q):
        w(f"inv {hx(a_)} {hx(inv_checked(a_))}")
    for _ in range(RANDOM_INV_CASES):
        a_ = 1 + rng.getrandbits(256) % (Q - 1)
        w(f"inv {hx(a_)} {hx(inv_checked(a_))}")
    w("#")
    w(f"# Section D: {RANDOM_CASES} random cases of each operation.")
    for _ in range(RANDOM_CASES):
        a_, b_ = rng.getrandbits(256) % Q, rng.getrandbits(256) % Q
        w(f"add {hx(a_)} {hx(b_)} {hx(add(a_, b_))}")
        w(f"sub {hx(a_)} {hx(b_)} {hx(sub(a_, b_))}")
        w(f"mul {hx(a_)} {hx(b_)} {hx(mul(a_, b_))}")
    w("#")
    w("# Section E: encodings: 32 bytes, least significant byte first; values at or")
    w("#   above q rejected (ok = 0, value 0).")

    def fb(v: int, ok: bool):
        w(f"frombytes {to_bytes_le(v).hex()} {1 if ok else 0} {hx(v if ok else 0)}")
    for v in (0, 1, Q - 1, half, gx % Q):
        fb(v, True)
    for v in (Q, Q + 1, MASK256, P, Q + 2**64, (0xFFFFFFFF00000000 << 192) | (2**192 - 1)):
        fb(v, False)
    for _ in range(RANDOM_CASES // 2):
        fb(rng.getrandbits(256) % Q, True)
    for _ in range(RANDOM_CASES // 4):
        fb(Q + rng.getrandbits(256) % (2**256 - Q), False)
    (out_dir / "q256_field.txt").write_text("\n".join(lines) + "\n")
    n = sum(1 for l in lines if l and not l.startswith("#"))
    print(f"wrote {out_dir / 'q256_field.txt'}: {n} cases")


if __name__ == "__main__":
    main()
