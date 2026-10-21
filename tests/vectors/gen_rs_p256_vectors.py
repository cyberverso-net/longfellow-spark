#!/usr/bin/env python3
"""Generator for the P-256 Reed-Solomon extension vectors (Phase D, block
4, ADR 0057):
  rs_p256.txt
    root_p256 <re> <im>              the root of unity of order 2^31 in
                                     F_p^2 of the reference
    extend_p256 <n> <m> <y_0 .. y_n-1> <c_n .. c_m-1>
                                     the extension of the n values at the
                                     points 0 .. n - 1 to the points
                                     n .. m - 1 (Section 2.2.1)

The extension is computed twice and the two must agree, or generation
aborts:
  - as the production prover computes it (google/longfellow-zk at
    d5e6be7, rust/runtime/algebra/src/reed_solomon.rs, ReedSolomon::new
    and interpolate): p(k) = (-1)^d (k - d) C(k, d) times the sum over
    j of x_j / (k - j), x_j = (-1)^j C(d, j) p(j), d = n - 1; the sum is a
    middle product, a cyclic convolution of size next_power_of_two(m),
    by the real FFT over F_p^2 of rfft.rs (half-complex storage, radix 4),
    transcribed with the reference's root of unity;
  - by Lagrange interpolation on the points 0 .. n - 1, with no transform.
F_p has no root of unity of order 4: p - 1 = 2 q with q odd. The roots
live in F_p^2, since p + 1 = 2^96 q'; the generator checks both facts and
the order of the reference's root.

Usage: python3 -I gen_rs_p256_vectors.py [output-directory]
Output is deterministic (fixed seed, no timestamps).
"""

import importlib.util
import random
import sys
from pathlib import Path

HERE = Path(__file__).parent
SEED = 20261021
LOG_ROOT = 31


def fail(msg: str) -> None:
    print(f"gen_rs_p256_vectors: FAILED: {msg}", file=sys.stderr)
    sys.exit(1)


def load_sibling(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


PV = load_sibling("gen_p256_vectors")
P = PV.P


def mul(a, b):
    return a * b % P


def inv(a):
    r = pow(a, P - 2, P)
    if mul(a, r) != 1:
        fail(f"no inverse for {a}")
    return r


# The root of unity of the reference, google/longfellow-zk at d5e6be7,
# rust/runtime/algebra/src/p256/mod.rs, P256_ROOT_OF_UNITY_RE and _IM,
# verbatim (four little-endian 64-bit words each): an element of
# F_p^2 = F_p[i] / (i^2 + 1) of order 2^31 on the unit circle.
ROOT_RE_WORDS = [0x985a65324b242562, 0x9fc9563b382a4a4c,
                 0x5cfc85c67990e337, 0xf90d338ebd84f566]
ROOT_IM_WORDS = [0xdbf4174f60a43eac, 0x84738a6474d232c6,
                 0xa04fc2e20106e340, 0xb9e81e42bc97cc4d]


def words(w):
    return sum(x << (64 * i) for i, x in enumerate(w))


def cm(x, y):
    return ((x[0] * y[0] - x[1] * y[1]) % P, (x[0] * y[1] + x[1] * y[0]) % P)


def check_root():
    if (P - 1) % 4 == 0 or P % 8 != 7:
        fail("p is not 7 modulo 8")
    two = 0
    q = P + 1
    while q % 2 == 0:
        q //= 2
        two += 1
    if two != 96 or (P - 1) % 4 == 0:
        fail("p + 1 should have 2-adicity 96 and p - 1 2-adicity 1")
    w = (words(ROOT_RE_WORDS), words(ROOT_IM_WORDS))
    if w[0] >= P or w[1] >= P or (w[0] * w[0] + w[1] * w[1]) % P != 1:
        fail("the root is not on the unit circle")
    x = w
    for _ in range(LOG_ROOT - 1):
        x = cm(x, x)
    if x != (P - 1, 0):
        fail("the root does not have order 2^31")
    return w


ROOT = check_root()


# ---- The real FFT of rfft.rs, transcribed ----------------------------------

def cmul(xr, xi, br, bi):
    a01 = (xr + xi) % P
    b01 = (br + bi) % P
    p1 = mul(xi, bi)
    xr2 = mul(xr, br)
    a01 = (mul(a01, b01) - xr2 - p1) % P
    return (xr2 - p1) % P, a01


def cmul_conj(xr, xi, br, bi):
    a01 = (xr + xi) % P
    b01 = (br - bi) % P
    p1 = mul(xi, bi)
    xr2 = mul(xr, br)
    a01 = (mul(a01, b01) - xr2 + p1) % P
    return (xr2 + p1) % P, a01


def reroot(n):
    w, r = ROOT, n
    while r < 2 ** LOG_ROOT:
        w = cm(w, w)
        r += r
    return w


def roots(n):
    w = reroot(n)
    out, cur = [], (1, 0)
    for _ in range(n // 2):
        out.append(cur)
        cur = cm(cur, w)
    return out


def bitrev(a):
    n = len(a)
    revi = 0
    for i in range(n - 1):
        if i < revi:
            a[i], a[revi] = a[revi], a[i]
        bit = n
        while True:
            bit >>= 1
            revi ^= bit
            if revi & bit:
                break


def r2hc_i_2(a, i, s):
    t = a[i + s]
    a[i + s] = (a[i] - t) % P
    a[i] = (a[i] + t) % P


def r2hc_i_4(a, i, s):
    x1, x3 = a[i + s], a[i + 3 * s]
    a[i + s] = (a[i] - x1) % P
    a[i] = (a[i] + x1) % P
    x2 = a[i + 2 * s]
    a[i + 3 * s] = (x3 - x2) % P
    a[i + 2 * s] = (x2 + x3) % P
    z1 = a[i + 2 * s]
    a[i + 2 * s] = (a[i] - z1) % P
    a[i] = (a[i] + z1) % P


def r2hc_ii_4(a, i, s, w8):
    x1, x2, x3 = a[i + s], a[i + 2 * s], a[i + 3 * s]
    z0 = mul((x2 + x3) % P, w8[1])
    z1 = mul((x2 - x3) % P, w8[0])
    x0 = a[i]
    a[i + s] = (x0 - z1) % P
    a[i] = (x0 + z1) % P
    a[i + 3 * s] = (-(x1 + z0)) % P
    a[i + 2 * s] = (x1 - z0) % P


def hc2hc_f_4(a, ir, ii, s, tw1, tw2, tw3):
    x0r, x0i = a[ir], a[ii]
    x1r, x1i = cmul_conj(a[ir + s], a[ii + s], tw2[0], tw2[1])
    x2r, x2i = cmul_conj(a[ir + 2 * s], a[ii + 2 * s], tw1[0], tw1[1])
    x3r, x3i = cmul_conj(a[ir + 3 * s], a[ii + 3 * s], tw3[0], tw3[1])
    y0r, y0i = (x0r + x1r) % P, (x0i + x1i) % P
    y1r, y1i = (x0r - x1r) % P, (x0i - x1i) % P
    y2r, y3r = (x3r + x2r) % P, (x3r - x2r) % P
    y2i, y3i = (x2i + x3i) % P, (x2i - x3i) % P
    a[ir] = (y0r + y2r) % P
    a[ii + s] = (y0r - y2r) % P
    a[ir + s] = (y1r + y3i) % P
    a[ii] = (y1r - y3i) % P
    a[ii + 3 * s] = (y2i + y0i) % P
    a[ir + 2 * s] = (y2i - y0i) % P
    a[ii + 2 * s] = (y3r + y1i) % P
    a[ir + 3 * s] = (y3r - y1i) % P


def hc2r_i_2(a, i, s):
    r2hc_i_2(a, i, s)


def hc2r_i_4(a, i, s):
    y0 = (a[i] + a[i + 2 * s]) % P
    y1 = (a[i] - a[i + 2 * s]) % P
    y2 = (a[i + s] + a[i + s]) % P
    y3 = (a[i + 3 * s] + a[i + 3 * s]) % P
    a[i] = (y0 + y2) % P
    a[i + s] = (y0 - y2) % P
    a[i + 2 * s] = (y1 - y3) % P
    a[i + 3 * s] = (y1 + y3) % P


def hc2r_iii_4(a, i, s, w8):
    x0, x1 = 2 * a[i] % P, 2 * a[i + s] % P
    x2, x3 = 2 * a[i + 2 * s] % P, 2 * a[i + 3 * s] % P
    a0 = (x0 + x1) % P
    as_ = (x2 - x3) % P
    z0 = mul((x0 - x1) % P, w8[0])
    z1 = mul((x3 + x2) % P, w8[1])
    a[i] = a0
    a[i + s] = as_
    a[i + 2 * s] = (z0 - z1) % P
    a[i + 3 * s] = (-(z0 + z1)) % P


def hc2hc_b_4(a, ir, ii, s, tw1, tw2, tw3):
    x0r, x0i, x1r, x1i = a[ir], a[ii], a[ir + s], a[ii + s]
    x2r, x2i, x3r, x3i = a[ir + 2 * s], a[ii + 2 * s], a[ir + 3 * s], a[ii + 3 * s]
    z0, z1 = (x0r + x1i) % P, (x0r - x1i) % P
    z2, z3 = (x1r + x0i) % P, (x1r - x0i) % P
    z4, z5 = (x3i + x2r) % P, (x3i - x2r) % P
    z6, z7 = (x2i + x3r) % P, (x2i - x3r) % P
    o0r, o0i = (z0 + z2) % P, (z5 + z7) % P
    o1r, o1i = cmul((z0 - z2) % P, (z5 - z7) % P, tw2[0], tw2[1])
    o2r, o2i = cmul((z1 - z6) % P, (z4 + z3) % P, tw1[0], tw1[1])
    o3r, o3i = cmul((z1 + z6) % P, (z4 - z3) % P, tw3[0], tw3[1])
    a[ir], a[ii] = o0r, o0i
    a[ir + s], a[ii + s] = o1r, o1i
    a[ir + 2 * s], a[ii + 2 * s] = o2r, o2i
    a[ir + 3 * s], a[ii + 3 * s] = o3r, o3i


def leaf_size(n):
    m = n
    while m > 4:
        m //= 4
    return m


def r2hc(a):
    n = len(a)
    if n == 2:
        r2hc_i_2(a, 0, 1)
        return
    w = roots(n)
    bitrev(a)
    m = leaf_size(n)
    for c in range(0, n, m):
        (r2hc_i_2 if m == 2 else r2hc_i_4)(a, c, 1)
    cur = m
    while cur < n:
        ws = n // (4 * cur)
        for c in range(0, n, 4 * cur):
            r2hc_i_4(a, c, cur)
            for j in range(1, cur // 2):
                hc2hc_f_4(a, c + j, c + cur - j, cur,
                          w[j * ws], w[2 * j * ws], w[3 * j * ws])
            r2hc_ii_4(a, c + cur // 2, cur, w[(cur // 2) * ws])
        cur *= 4


def hc2r(a):
    n = len(a)
    if n == 2:
        hc2r_i_2(a, 0, 1)
        return
    w = roots(n)
    m = n
    while m > 4:
        m //= 4
        ws = n // (4 * m)
        for c in range(0, n, 4 * m):
            hc2r_i_4(a, c, m)
            for j in range(1, m // 2):
                hc2hc_b_4(a, c + j, c + m - j, m,
                          w[j * ws], w[2 * j * ws], w[3 * j * ws])
            hc2r_iii_4(a, c + m // 2, m, w[(m // 2) * ws])
    for c in range(0, n, m):
        (hc2r_i_2 if m == 2 else hc2r_i_4)(a, c, 1)
    bitrev(a)


def middle_product(x, y, n, m):
    """FFTExtMiddleProduct: z[n - 1 .. m - 1] of the product of x with y."""
    size = 1
    while size < m:
        size *= 2
    yf = list(y) + [0] * (size - m)
    r2hc(yf)
    inv_n = inv(size)
    yf = [mul(v, inv_n) for v in yf]
    xf = list(x) + [0] * (size - n)
    r2hc(xf)
    xf[0] = mul(xf[0], yf[0])
    ny = size // 2
    for k in range(1, ny):
        xr, xi = cmul(xf[k], xf[size - k], yf[k], yf[size - k])
        xf[k], xf[size - k] = xr, xi
    xf[ny] = mul(xf[ny], yf[ny])
    hc2r(xf)
    return xf[:m]


def extend_middle_product(y, n, m):
    """ReedSolomon::new and interpolate of reed_solomon.rs."""
    d = n - 1
    out = list(y[:n]) + [0] * (m - n)
    if m == n:
        return out
    inverses = [0] + [inv(t) for t in range(1, m)]
    lead = [0] * (m - n + 1)
    lead[0] = 1
    deg = (d + 1) % P
    for i in range(1, m - n + 1):
        lead[i] = mul(lead[i - 1], mul(deg, inverses[i]))
        deg = (deg + 1) % P
    fac = 0
    for k in range(d, m):
        idx = k - d
        lead[idx] = mul(lead[idx], fac)
        if d % 2 == 1:
            lead[idx] = (-lead[idx]) % P
        fac = (fac + 1) % P
    binom = [0] * n
    binom[0] = 1
    bv = d % P
    for i in range(1, n):
        binom[i] = mul(binom[i - 1], mul(bv, inverses[i]))
        bv = (bv - 1) % P
    for i in range(1, n, 2):
        binom[i] = (-binom[i]) % P
    x = [mul(binom[i], y[i]) for i in range(n)]
    t = middle_product(x, inverses, n, max(m, 2))
    for k in range(n, m):
        out[k] = mul(lead[k - d], t[k])
    return out


def extend_lagrange(y, n, m):
    out = list(y[:n]) + [0] * (m - n)
    for k in range(n, m):
        acc = 0
        for i in range(n):
            num, den = 1, 1
            for j in range(n):
                if j != i:
                    num = mul(num, (k - j) % P)
                    den = mul(den, (i - j) % P)
            acc = (acc + mul(y[i], mul(num, inv(den)))) % P
        out[k] = acc
    return out


CASES = [(1, 1), (1, 2), (1, 5), (2, 3), (2, 8), (3, 4), (3, 9), (4, 4),
         (4, 16), (5, 17), (7, 30), (8, 64), (13, 50), (16, 100), (21, 64),
         (33, 128), (64, 300), (20, 1024), (5, 2048)]


def hx(v: int) -> str:
    return f"{v:064x}"


def main() -> None:
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE
    rng = random.Random(SEED)
    lines = ["# P-256 Reed-Solomon extension vectors (ADR 0057), generated by "
             "gen_rs_p256_vectors.py", f"root_p256 {hx(ROOT[0])} {hx(ROOT[1])}"]
    for n, m in CASES:
        y = [rng.randrange(P) for _ in range(n)]
        a = extend_middle_product(y, n, m)
        b = extend_lagrange(y, n, m)
        if a != b:
            first = next(j for j in range(m) if a[j] != b[j])
            fail(f"middle product and Lagrange disagree for n={n} m={m} at {first}")
        lines.append(f"extend_p256 {n} {m} " + " ".join(hx(v) for v in y)
                     + (" " if m > n else "") + " ".join(hx(v) for v in a[n:]))
    (out_dir / "rs_p256.txt").write_text("\n".join(lines) + "\n")
    print(f"gen_rs_p256_vectors: rs_p256.txt with the root and {len(CASES)} "
          f"extension cases; the middle product equals Lagrange on every case")


if __name__ == "__main__":
    main()
