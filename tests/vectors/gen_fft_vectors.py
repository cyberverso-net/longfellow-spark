#!/usr/bin/env python3
"""Generator for the additive FFT vectors (Phase D, block 3, ADR 0057):
  fft.txt
    what <i> <j> <value>                 the normalised W_i (beta_j), 16 x 16
    twiddle <i> <u> <value>              sample twiddle factors
    extend <n> <m> <y_0 .. y_n-1> <c_n .. c_m-1>
                                         the Reed-Solomon extension of the n
                                         values at inj (0 .. n - 1) to the
                                         points inj (n .. m - 1)

The extension is computed twice and the two must agree, or generation
aborts:
  - by a transcription of the production algorithm of google/longfellow-zk
    at d5e6be7, rust/runtime/algebra/src/lch14.rs (the novel basis of Lin,
    Chung and Han 2014 following Diamond and Posen 2024, Algorithm 2, and
    the bidirectional FFT after van der Hoeven) and lch14_reed_solomon.rs
    (interpolate: the bidirectional FFT on the first 2^l points, l the
    smallest with 2^l >= n, then one forward FFT per coset up to m);
  - by Lagrange interpolation in barycentric form on the points
    inj (i) = XOR of beta_j over the set bits j of i (draft-03 Section
    2.2.2), with no FFT at all.
The field arithmetic and the subfield basis come from
gen_gf2_128_vectors.py, which checks the basis against upstream.

Usage: python3 -I gen_fft_vectors.py [output-directory]
Output is deterministic (fixed seed, no timestamps).
"""

import importlib.util
import random
import sys
from pathlib import Path

HERE = Path(__file__).parent
SEED = 20261020
DIM = 16


def fail(msg: str) -> None:
    print(f"gen_fft_vectors: FAILED: {msg}", file=sys.stderr)
    sys.exit(1)


def load_sibling(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


GF = load_sibling("gen_gf2_128_vectors")
mul = GF.mul
inv = GF.inv_euclid
BETA = GF.UPSTREAM_SUBFIELD_BASIS


def inj(i: int) -> int:
    v = 0
    for j in range(DIM):
        if (i >> j) & 1:
            v ^= BETA[j]
    return v


# ---- LCH14, transcribed from lch14.rs -----------------------------------

def make_w_hat():
    w = [[0] * DIM for _ in range(DIM)]
    w[0] = list(BETA)                      # W_0 (X) = X
    for i in range(DIM - 1):               # W_i+1 = W_i (W_i + W_i (beta_i))
        wb = w[i][i]
        for j in range(DIM):
            w[i + 1][j] = mul(w[i][j], w[i][j] ^ wb)
    for i in range(DIM):                   # normalise by W_i (beta_i)
        s = inv(w[i][i])
        for j in range(DIM):
            w[i][j] = mul(w[i][j], s)
    return w


W_HAT = make_w_hat()


def twiddle(i: int, u: int) -> int:
    t, k = 0, 0
    while u:
        if u & 1:
            t ^= W_HAT[i][k]
        k += 1
        u >>= 1
    return t


# In characteristic 2, add and sub are both XOR.
def fwd(b, x, y, t):
    b[x] ^= mul(b[y], t)
    b[y] ^= b[x]


def bwd(b, x, y, t):
    b[y] ^= b[x]
    b[x] ^= mul(b[y], t)


def diag(b, x, y, t):
    b1 = b[y]
    b[y] ^= b[x]
    b[x] ^= mul(b1, t)


def fft(l, coset, b, off=0):
    for i in reversed(range(l)):
        s = 1 << i
        for c in range(1 << (l - 1 - i)):
            t = twiddle(i, coset + (c << (i + 1)))
            base = off + c * 2 * s
            for v in range(s):
                fwd(b, base + v, base + v + s, t)


def ifft(l, coset, b, off=0):
    for i in range(l):
        s = 1 << i
        for c in range(1 << (l - 1 - i)):
            t = twiddle(i, coset + (c << (i + 1)))
            base = off + c * 2 * s
            for v in range(s):
                bwd(b, base + v, base + v + s, t)


def bidir(i, coset, k, b, off=0):
    if i == 0:
        return
    i -= 1
    s = 1 << i
    t = twiddle(i, coset)
    if k < s:
        for v in range(k, s):
            fwd(b, off + v, off + v + s, t)
        bidir(i, coset, k, b, off)
        for v in range(k):
            diag(b, off + v, off + v + s, t)
        fft(i, coset + s, b, off + s)
    else:
        ifft(i, coset, b, off)
        ks = k - s
        for v in range(ks, s):
            diag(b, off + v, off + v + s, t)
        bidir(i, coset + s, ks, b, off + s)
        for v in range(ks):
            bwd(b, off + v, off + v + s, t)


def extend_lch14(y, n, m):
    fftn = 1
    while fftn < n:
        fftn *= 2
    l = fftn.bit_length() - 1
    c = list(y[:n]) + [0] * (fftn - n)
    bidir(l, 0, n, c)
    out = list(y[:n]) + [0] * (m - n)
    for j in range(n, min(m, fftn)):
        out[j] = c[j]
    for j in range(n, fftn):
        c[j] = 0
    coset = 1
    while (coset << l) < m:
        b = coset << l
        tmp = list(c)
        fft(l, b, tmp)
        for j in range(min(m - b, fftn)):
            out[b + j] = tmp[j]
        coset += 1
    return out


# ---- Lagrange, barycentric, on inj (0 .. n - 1) --------------------------

def extend_lagrange(y, n, m):
    xs = [inj(i) for i in range(n)]
    wts = []
    for i in range(n):
        d = 1
        for k in range(n):
            if k != i:
                d = mul(d, xs[i] ^ xs[k])
        wts.append(inv(d))
    out = list(y[:n]) + [0] * (m - n)
    for j in range(n, m):
        z = inj(j)
        # p (z) = l (z) * SUM_i w_i y_i / (z - x_i), l (z) = PROD (z - x_k)
        lz = 1
        for k in range(n):
            lz = mul(lz, z ^ xs[k])
        acc = 0
        for i in range(n):
            acc ^= mul(mul(wts[i], y[i]), inv(z ^ xs[i]))
        out[j] = mul(lz, acc)
    return out


CASES = [(1, 1), (1, 2), (1, 16), (2, 3), (2, 4), (3, 8), (4, 4), (4, 5),
         (5, 8), (5, 40), (7, 9), (8, 16), (8, 17), (9, 31), (13, 100),
         (16, 64), (17, 33), (31, 257), (64, 600)]


def hx(v: int) -> str:
    return f"{v:032x}"


def main() -> None:
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE
    rng = random.Random(SEED)
    lines = ["# Additive FFT vectors (ADR 0057), generated by gen_fft_vectors.py"]
    for i in range(DIM):
        if W_HAT[i][i] != 1:
            fail(f"W_hat {i} (beta_{i}) = {hx(W_HAT[i][i])}, expected 1")
        for j in range(DIM):
            if j < i and W_HAT[i][j] != 0:
                fail(f"W_hat {i} (beta_{j}) /= 0 below the diagonal")
            lines.append(f"what {i} {j} {hx(W_HAT[i][j])}")
    for i, u in [(0, 0), (0, 1), (3, 5), (5, 1024), (9, 65535), (15, 32768)]:
        lines.append(f"twiddle {i} {u} {hx(twiddle(i, u))}")
    for n, m in CASES:
        y = [rng.getrandbits(128) for _ in range(n)]
        a = extend_lch14(y, n, m)
        b = extend_lagrange(y, n, m)
        if a != b:
            first = next(j for j in range(m) if a[j] != b[j])
            fail(f"LCH14 and Lagrange disagree for n={n} m={m} at {first}")
        lines.append(f"extend {n} {m} " + " ".join(hx(v) for v in y)
                     + (" " if m > n else "") + " ".join(hx(v) for v in a[n:]))
    (out_dir / "fft.txt").write_text("\n".join(lines) + "\n")
    print(f"gen_fft_vectors: fft.txt with {DIM * DIM} w_hat, 6 twiddle and "
          f"{len(CASES)} extension cases; LCH14 equals Lagrange on every case")


if __name__ == "__main__":
    main()
