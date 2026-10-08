#!/usr/bin/env python3
"""Generator for the P-256 base field known-answer vectors:
  p256_add.txt    add <a> <b> <expected>, sub <a> <b> <expected>, neg <a> <expected>
  p256_mul.txt    mul <a> <b> <expected>, square <a> <expected>
  p256_inv.txt    inv <a> <expected>
  p256_bytes.txt  frombytes <32 bytes as 64 hex digits in memory order> <ok> <value>

Field: integers modulo p = 2^256 - 2^224 + 2^192 + 2^96 - 1, the base field
of NIST P-256 (draft-google-cfrg-libzk-03, Table 1, FieldID 0x01). Elements
are serialised as 32 bytes little-endian (Section 7.2.1); non-canonical
encodings (value >= p) are rejected, as in the upstream Rust reference.

Values in the vector files are written as 64 hex digits of the integer,
most significant digit first; the bytes file additionally gives the 32
serialised bytes in memory order.

Independent reference: plain Python integers with %, nothing limb-wise.
Inversion is computed by Fermat (a^(p - 2)) and by extended Euclid; both
must agree.

External anchors: the curve parameters b, Gx, Gy of P-256 as printed in
RFC 5903 Section 3.1 (identical to SEC 2 v2.0 Section 2.4.2 and NIST SP
800-186). The base point satisfies Gy^2 = Gx^3 - 3 Gx + b mod p; the
generator checks this and aborts otherwise.

Reduction table: this script also derives and checks the Solinas reduction
used by the implementation (ADR 0013): for a 512-bit product split into
32-bit words c0 .. c15, X = T + 2 S1 + 2 S2 + S3 + S4 - D1 - D2 - D3 - D4
+ Q * p exactly, with Q a fixed linear combination of c8 .. c15. The
quotient coefficients and the intermediate bounds are printed for the
chapter and verified on random inputs.

Usage: python3 -I gen_p256_vectors.py [output-directory]
Output is deterministic (fixed seed, no timestamps).
"""

import random
import sys
from pathlib import Path

P = 2**256 - 2**224 + 2**192 + 2**96 - 1
C = 2**256 - P          # 2^256 mod p = 2^224 - 2^192 - 2^96 + 1
MASK256 = 2**256 - 1

SEED = 20261009
RANDOM_CASES = 64
RANDOM_INV_CASES = 32

# RFC 5903, Section 3.1, verbatim (spaces removed).
RFC5903_P  = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
RFC5903_B  = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
RFC5903_GX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
RFC5903_GY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
# Table 1 of draft-03 prints p in decimal.
TABLE1_P_DECIMAL = 115792089210356248762697446949407573530086143415290314195533631308867097853951


def fail(msg: str) -> None:
    print(f"gen_p256_vectors: FAILED: {msg}", file=sys.stderr)
    sys.exit(1)


def hx(v: int) -> str:
    assert 0 <= v < 2**256
    return f"{v:064x}"


def to_bytes_le(v: int) -> bytes:
    return v.to_bytes(32, "little")


def add(a, b): return (a + b) % P
def sub(a, b): return (a - b) % P
def neg(a): return (-a) % P
def mul(a, b): return (a * b) % P


def inv_fermat(a: int) -> int:
    return pow(a, P - 2, P)


def inv_euclid(a: int) -> int:
    assert 1 <= a < P
    r0, r1, s0, s1 = P, a, 0, 1
    while r1 != 1:
        q = r0 // r1
        r0, r1 = r1, r0 - q * r1
        s0, s1 = s1, s0 - q * s1
        assert r1 != 0
    return s1 % P


def inv_checked(a: int) -> int:
    f = inv_fermat(a)
    if f != inv_euclid(a):
        fail(f"Fermat and Euclid inverses differ for {hx(a)}")
    if mul(a, f) != 1:
        fail(f"a * inv(a) /= 1 for {hx(a)}")
    return f


# ---- Solinas reduction table (FIPS 186-4 style, 32-bit words) ----------
# Each row lists the word indices, most significant first, of an 8-word
# 256-bit term; None is a zero word.
TERMS = {
    "T":  (1, (7, 6, 5, 4, 3, 2, 1, 0)),
    "S1": (2, (15, 14, 13, 12, 11, None, None, None)),
    "S2": (2, (None, 15, 14, 13, 12, None, None, None)),
    "S3": (1, (15, 14, None, None, None, 10, 9, 8)),
    "S4": (1, (8, 13, 15, 14, 13, 11, 10, 9)),
    "D1": (-1, (10, 8, None, None, None, 13, 12, 11)),
    "D2": (-1, (11, 9, None, None, 15, 14, 13, 12)),
    "D3": (-1, (12, None, 10, 9, 8, 15, 14, 13)),
    "D4": (-1, (13, None, 11, 10, 9, None, 15, 14)),
}


def words32(x: int) -> list:
    return [(x >> (32 * i)) & 0xFFFFFFFF for i in range(16)]


def term_value(words, idxs) -> int:
    v = 0
    for pos, idx in enumerate(reversed(idxs)):   # pos 0 = least significant
        if idx is not None:
            v += words[idx] << (32 * pos)
    return v


def solinas_signed(x: int):
    """Returns (positive sum S, negative sum N) with X = S - N (mod p)."""
    w = words32(x)
    s = n = 0
    for coef, idxs in TERMS.values():
        v = term_value(w, idxs)
        if coef > 0:
            s += coef * v
        else:
            n += v
    return s, n


def derive_reduction():
    # Quotient coefficients: for word j >= 8 alone set to 1, X - (S - N) = q_j * p.
    q = {}
    for j in range(8, 16):
        x = 1 << (32 * j)
        s, n = solinas_signed(x)
        diff = x - (s - n)
        if diff % P != 0:
            fail(f"reduction table wrong for word {j}")
        q[j] = diff // P
    # Low words must pass through unchanged.
    for j in range(8):
        x = 1 << (32 * j)
        s, n = solinas_signed(x)
        if s - n != x:
            fail(f"reduction table alters low word {j}")
    # Exact identity on random inputs.
    rng = random.Random(1)
    for _ in range(2000):
        x = rng.getrandbits(512)
        s, n = solinas_signed(x)
        w = words32(x)
        qq = sum(q[j] * w[j] for j in range(8, 16))
        if x != (s - n) + qq * P:
            fail("exact reduction identity fails on random input")
    # Bounds with all words maximal.
    full = [0xFFFFFFFF] * 16
    s_max = sum(coef * term_value(full, idxs) for coef, idxs in TERMS.values() if coef > 0)
    n_max = sum(term_value(full, idxs) for coef, idxs in TERMS.values() if coef < 0)
    k = -(-n_max // P)                 # smallest k with k p >= N_max
    v_max = s_max + k * P              # V = S - N + k p, 0 <= V <= v_max
    v4_max = v_max >> 256
    w_max = MASK256 + v4_max * C       # W = V mod 2^256 + V_hi * C
    if not (w_max < 2 * P):
        fail("final fold bound does not allow a single conditional subtraction")
    # The exact identity also holds for the largest product (p - 1)^2.
    s, n = solinas_signed((P - 1) ** 2)
    assert (s - n) % P == 1
    return q, k, s_max, n_max, v_max, v4_max, w_max


def main() -> None:
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent

    # ---- Anchors -------------------------------------------------------
    if P != RFC5903_P or P != TABLE1_P_DECIMAL:
        fail("p does not match RFC 5903 / Table 1")
    b, gx, gy = RFC5903_B, RFC5903_GX, RFC5903_GY
    if (gy * gy - (gx**3 - 3 * gx + b)) % P != 0:
        fail("base point is not on the curve")
    if C != 2**224 - 2**192 - 2**96 + 1:
        fail("fold constant")
    half = inv_checked(2)
    if half != (P + 1) // 2:
        fail("inverse of two")

    q, k, s_max, n_max, v_max, v4_max, w_max = derive_reduction()
    print("reduction: quotient coefficients q_j (X = S - N + sum_j q_j c_j * p):")
    for j in range(8, 16):
        print(f"  q_{j} = {q[j]}")
    print(f"  S_max  = {s_max} (bits {s_max.bit_length()})")
    print(f"  N_max  = {n_max} (bits {n_max.bit_length()}), k = {k}")
    print(f"  V_max  = {v_max} (bits {v_max.bit_length()}), V_hi <= {v4_max}")
    print(f"  W_max  = {w_max} (bits {w_max.bit_length()}), W_max < 2p: {w_max < 2 * P}")

    rng = random.Random(SEED)

    # ---- Addition, subtraction, negation -----------------------------
    lines = []
    w = lines.append
    w("# Known-answer vectors for the P-256 base field: addition, subtraction, negation.")
    w("# Generated by gen_p256_vectors.py (this directory); do not edit by hand.")
    w("# Field: integers mod p = 2^256 - 2^224 + 2^192 + 2^96 - 1 (draft-03 Table 1).")
    w("# Values: 64 hex digits of the integer, most significant first.")
    w("# Format: add <a> <b> <a+b>;  sub <a> <b> <a-b>;  neg <a> <-a>.")
    w("#")
    w("# Section A: anchors from RFC 5903 Section 3.1 (P-256 b, Gx, Gy).")
    w(f"# b  = {hx(b)}")
    w(f"# Gx = {hx(gx)}")
    w(f"# Gy = {hx(gy)}")
    for a_, b_ in ((gx, gy), (gx, b), (gy, b), (P - 1, 1), (P - 1, P - 1), (half, half)):
        w(f"add {hx(a_)} {hx(b_)} {hx(add(a_, b_))}")
    for a_, b_ in ((gx, gy), (gy, gx), (0, 1), (0, gx), (1, P - 1)):
        w(f"sub {hx(a_)} {hx(b_)} {hx(sub(a_, b_))}")
    for a_ in (0, 1, gx, gy, P - 1, half):
        w(f"neg {hx(a_)} {hx(neg(a_))}")
    w("#")
    w("# Section B: structural: carries across every limb boundary, wrap at p.")
    for a_, b_ in ((2**64 - 1, 1), (2**128 - 1, 1), (2**192 - 1, 1), (2**255, 2**255),
                   (P - 1, 2), (MASK256 - C, C), (P - 2**64, 2**64), (C, P - C)):
        w(f"add {hx(a_ % P)} {hx(b_ % P)} {hx(add(a_ % P, b_ % P))}")
    for a_, b_ in ((0, 2**64), (2**64, 2**64 + 1), (2**128, 1), (2**192, 2**64)):
        w(f"sub {hx(a_)} {hx(b_)} {hx(sub(a_, b_))}")
    w("#")
    w(f"# Section C: {RANDOM_CASES} random cases, Python random.Random seed {SEED},")
    w("#   operands drawn as getrandbits(256) mod p, in order a, b; one add, one")
    w("#   sub and one neg per draw.")
    for _ in range(RANDOM_CASES):
        a_ = rng.getrandbits(256) % P
        b_ = rng.getrandbits(256) % P
        w(f"add {hx(a_)} {hx(b_)} {hx(add(a_, b_))}")
        w(f"sub {hx(a_)} {hx(b_)} {hx(sub(a_, b_))}")
        w(f"neg {hx(a_)} {hx(neg(a_))}")
    (out_dir / "p256_add.txt").write_text("\n".join(lines) + "\n")

    # ---- Multiplication and squaring ---------------------------------
    lines = []
    w = lines.append
    w("# Known-answer vectors for the P-256 base field: multiplication, squaring.")
    w("# Generated by gen_p256_vectors.py (this directory); do not edit by hand.")
    w("# Field: integers mod p = 2^256 - 2^224 + 2^192 + 2^96 - 1 (draft-03 Table 1).")
    w("# Values: 64 hex digits of the integer, most significant first.")
    w("# Format: mul <a> <b> <a*b>;  square <a> <a*a>.")
    w("#")
    w("# Section A: anchors. The P-256 base point (RFC 5903 Section 3.1)")
    w("#   satisfies Gy^2 = Gx^3 - 3 Gx + b: the intermediate products below")
    w("#   compose to that identity (checked by the generator). Also")
    w("#   (p - 1)^2 = 1 and 2^128 * 2^128 = 2^256 mod p = 2^224 - 2^192 - 2^96 + 1.")
    gx2 = mul(gx, gx); gx3 = mul(gx2, gx); gy2 = mul(gy, gy); three_gx = mul(3, gx)
    if sub(sub(gx3, three_gx), neg(b)) != gy2:
        fail("curve identity composition")
    for a_, b_ in ((gx, gx), (gx2, gx), (3, gx), (gy, gy), (P - 1, P - 1),
                   (2**128, 2**128), (half, 2), (gx, gy), (gy, gx)):
        w(f"mul {hx(a_)} {hx(b_)} {hx(mul(a_, b_))}")
    for a_ in (gx, gy, b, P - 1, half):
        w(f"square {hx(a_)} {hx(mul(a_, a_))}")
    w("#")
    w("# Section B: structural. Zero, one, each 32-bit word position of the")
    w("#   512-bit product (2^a * 2^b with a + b = 32 j, j = 8 .. 15), the")
    w("#   largest product (p - 1)^2, products with all-ones limbs, and")
    w("#   products whose reduction reaches the final conditional subtraction.")
    for a_, b_ in ((0, gx), (gx, 0), (1, gx), (gx, 1), (0, 0), (1, 1)):
        w(f"mul {hx(a_)} {hx(b_)} {hx(mul(a_, b_))}")
    for j in range(8, 16):
        a_ = 2**(32 * j - 255); b_ = 2**255
        w(f"mul {hx(a_)} {hx(b_)} {hx(mul(a_, b_))}")
    for a_, b_ in ((P - 1, 2), (P - 1, P - 2), (MASK256 - C, MASK256 - C),
                   (2**255, 2**255), (2**255 + 1, 2**255 + 1), (2**64 - 1, 2**64 - 1),
                   (2**192 + 2**128 + 2**64 + 1, 2**192 + 2**128 + 2**64 + 1),
                   (P - 1, 2**255)):
        w(f"mul {hx(a_ % P)} {hx(b_ % P)} {hx(mul(a_ % P, b_ % P))}")
    for a_ in (0, 1, 2, 2**128, 2**255, P - 1, MASK256 - C):
        w(f"square {hx(a_ % P)} {hx(mul(a_ % P, a_ % P))}")
    w("#")
    w(f"# Section C: {RANDOM_CASES} random mul cases and {RANDOM_CASES // 2} random")
    w("#   square cases, generator state continued after the add file.")
    for _ in range(RANDOM_CASES):
        a_ = rng.getrandbits(256) % P
        b_ = rng.getrandbits(256) % P
        w(f"mul {hx(a_)} {hx(b_)} {hx(mul(a_, b_))}")
    for _ in range(RANDOM_CASES // 2):
        a_ = rng.getrandbits(256) % P
        w(f"square {hx(a_)} {hx(mul(a_, a_))}")
    (out_dir / "p256_mul.txt").write_text("\n".join(lines) + "\n")

    # ---- Inversion -----------------------------------------------------
    lines = []
    w = lines.append
    w("# Known-answer vectors for the P-256 base field: inversion.")
    w("# Generated by gen_p256_vectors.py (this directory); do not edit by hand.")
    w("# Field: integers mod p = 2^256 - 2^224 + 2^192 + 2^96 - 1 (draft-03 Table 1).")
    w("# Values: 64 hex digits of the integer, most significant first.")
    w("# Format: inv <a> <expected> with a * expected = 1, except inv 0 = 0")
    w("#   (total function, ADR 0016). Every expected value was computed by")
    w("#   Fermat and by extended Euclid independently; both agree.")
    w("#")
    w("# Section A: anchors: inv 1, inv 2 = (p + 1) / 2, inv (p - 1) = p - 1,")
    w("#   inverses of Gx, Gy, b (RFC 5903 Section 3.1).")
    for a_ in (1, 2, P - 1, gx, gy, b):
        w(f"inv {hx(a_)} {hx(inv_checked(a_))}")
    w("#")
    w("# Section B: structural: zero (= 0), powers of two at limb boundaries,")
    w("#   2^256 mod p, all-ones below p.")
    w(f"inv {hx(0)} {hx(0)}")
    for a_ in (2**64, 2**128, 2**192, 2**255, C, P - 2, MASK256 - C):
        w(f"inv {hx(a_)} {hx(inv_checked(a_))}")
    w("#")
    w(f"# Section C: {RANDOM_INV_CASES} random cases, generator state continued.")
    for _ in range(RANDOM_INV_CASES):
        a_ = rng.getrandbits(256) % P
        if a_ == 0:
            continue
        w(f"inv {hx(a_)} {hx(inv_checked(a_))}")
    (out_dir / "p256_inv.txt").write_text("\n".join(lines) + "\n")

    # ---- Byte encoding -------------------------------------------------
    lines = []
    w = lines.append
    w("# Known-answer vectors for the P-256 base field: 32-byte little-endian encoding.")
    w("# Generated by gen_p256_vectors.py (this directory); do not edit by hand.")
    w("# draft-03 Section 7.2.1: an element is serialised as 32 bytes starting")
    w("#   with the least significant byte; encodings of values >= p are not")
    w("#   canonical and are rejected (upstream Rust from_bytes, ValueOutOfRange).")
    w("# Format: frombytes <32 bytes as 64 hex digits in memory order> <ok> <value>")
    w("#   ok = 1: accepted, value = the element (also the expected to_bytes input);")
    w("#   ok = 0: rejected, value = 0.")
    w("#")
    w("# Section A: anchors: b, Gx, Gy (RFC 5903 Section 3.1), the inverse of two.")
    def fb(v: int, ok: bool):
        w(f"frombytes {to_bytes_le(v).hex()} {1 if ok else 0} {hx(v if ok else 0)}")
    for v in (b, gx, gy, half):
        fb(v, True)
    w("#")
    w("# Section B: acceptance boundary: 0, 1, p - 1 accepted; p, p + 1, 2^256 - 1,")
    w("#   p + 2^96, 2^256 - 2^64, and p with the top limb only, rejected.")
    for v in (0, 1, P - 1):
        fb(v, True)
    for v in (P, P + 1, MASK256, P + 2**96, MASK256 - 2**64, 0xFFFFFFFF00000001 << 192):
        fb(v, False)
    w("#")
    w(f"# Section C: {RANDOM_CASES // 2} random encodings below p, and")
    w(f"#   {RANDOM_CASES // 4} random values in [p, 2^256) that must be rejected.")
    for _ in range(RANDOM_CASES // 2):
        fb(rng.getrandbits(256) % P, True)
    for _ in range(RANDOM_CASES // 4):
        fb(P + rng.getrandbits(256) % (2**256 - P), False)
    (out_dir / "p256_bytes.txt").write_text("\n".join(lines) + "\n")

    for name in ("p256_add.txt", "p256_mul.txt", "p256_inv.txt", "p256_bytes.txt"):
        n = sum(1 for l in (out_dir / name).read_text().splitlines() if l and not l.startswith("#"))
        print(f"wrote {out_dir / name}: {n} cases")


if __name__ == "__main__":
    main()
