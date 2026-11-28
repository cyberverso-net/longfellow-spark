#!/usr/bin/env python3
"""A tested polynomial identity, not a proof: every assertion that four
clauses of the hash relation need is found among the circuit's
assertions.

The relation is Hash_Relation of src/mdoc_relation-hash.ads. Four of its
clauses rest only on bit checks, the plucker, the words in the
multiplicative group and the SHA-256 compression (gadgets G1 to G4 of
ADR 0091): Bits, Chain, Zero_Tail and Length. For each of them this
script computes, from the relation's layout of the inputs and from
upstream's generator code at 0d92f80c, the assertions the circuit must
contain: for example, for every round of every block of the signed
message, the product of assert_eqmod that says the new word is the sum
of its terms modulo 2^32. Each required assertion is a polynomial P of
the circuit's inputs. It is found when the circuit has an assertion A,
a product of two wires that must be zero, with P = c A for a constant c
other than zero: then the circuit's assertion holds exactly when the
required one does.

How it compares. Every input of the circuit gets a field element at
two points, derived from the SHA-256 of the circuit file (so the run is
repeatable and the points are fixed only once the file is). The circuit
is evaluated at both points, every assertion's product with it, and
every required polynomial is evaluated at the same points. P is taken
as proportional to A when P(r1) A(r2) = P(r2) A(r1), with neither pair
zero. Nothing about the circuit's certificate or its generator's labels
is read.

The error bound. A test, not a proof:
- If P = c A, the test passes at every point: no required assertion is
  reported missing by mistake.
- If P is not proportional to A, then Q(x, y) = P(x) A(y) - P(y) A(x) is
  a nonzero polynomial of degree at most deg P + deg A in the inputs of
  both points, and by the Schwartz-Zippel lemma it vanishes at
  uniformly random points with probability at most
  (deg P + deg A) / 2^128.
- One point alone says nothing about proportionality (c is free); the
  second point is what the bound is about. Equality of two fixed
  polynomials of degree d at one point would be d / 2^128.
- A false "found" needs Q to vanish for one of the N assertions of the
  circuit, for one of the R required assertions: at most
  R N D / 2^128, D the largest deg P + deg A. The degrees are upper
  bounds computed from the circuit's terms, printed with the result.
- The bound treats the points as uniform: SHA-256 is assumed to behave
  as a random function of the file. Whoever writes a circuit could try
  many files; each try has the probability above.

Run from the repository root:
  python3 -I scripts/values-check.py CIRCUIT.lfc2
Exit status 0 when every required assertion is found, 1 when one is not
or the circuit does not have the relation's number of inputs, 2 when
the reader refuses the file or the command line is wrong.
"""

import hashlib
import math
import sys
import time
from pathlib import Path

VEC = Path(__file__).resolve().parent.parent / "tests" / "vectors"
sys.path.insert(0, str(VEC))
import gen_circuit_vectors as cv  # noqa: E402

GF = cv.load_sibling("gen_gf2_128_vectors")
FLD = cv.FIELDS["gf2_128"]
MASK = (1 << 128) - 1

# ---------------------------------------------------------------- field


def mul(a, b):
    """GF(2^128) with x^128 + x^7 + x^2 + x + 1, as the circuit file: a
    carry-less product by 4-bit windows, then the reduction."""
    if a == 0 or b == 0:
        return 0
    if a == 1:
        return b
    if b == 1:
        return a
    tab = [0] * 16
    for n in range(16):
        r = 0
        for k in range(4):
            if (n >> k) & 1:
                r ^= a << k
        tab[n] = r
    r = 0
    s = 0
    while b:
        r ^= tab[b & 15] << s
        b >>= 4
        s += 4
    for _ in range(2):
        hi = r >> 128
        r = (r & MASK) ^ hi ^ (hi << 1) ^ (hi << 2) ^ (hi << 7)
    return r


def inv(a):
    return GF.inv_euclid(a)


def of_scalar(n):
    """Upstream's of_scalar in GF(2^128): the subfield element of n."""
    v = 0
    for j in range(16):
        if (n >> j) & 1:
            v ^= GF.UPSTREAM_SUBFIELD_BASIS[j]
    return v


# --------------------------------------------- values with their degree
# A value is (v1, v2, d): the polynomial's values at the two points and
# an upper bound d of its degree in the inputs. d = 0 means a constant,
# whose two values are equal and exact.

def const(c):
    return (c, c, 0)


def add(x, y):
    return (x[0] ^ y[0], x[1] ^ y[1], max(x[2], y[2]))


def times(x, y):
    return (mul(x[0], y[0]), mul(x[1], y[1]), x[2] + y[2])


def scale(k, x):
    return (mul(k, x[0]), mul(k, x[1]), x[2] if k else 0)


ONE = const(1)


def lnot(x):
    return add(ONE, x)


def tree(i0, i1, f, op, empty):
    """The recursions of logic.h (add, mul, land over a range): the
    split im = i0 + (i1 - i0) / 2."""
    if i1 <= i0:
        return empty
    if i1 == i0 + 1:
        return f(i0)
    im = i0 + (i1 - i0) // 2
    return op(tree(i0, im, f, op, empty), tree(im, i1, f, op, empty))


def vbit(n, x):
    return [const((x >> i) & 1) for i in range(n)]


def eq_reduce(a, b):
    """logic.h eq_reduce: a == b, bit by bit then a tree of land."""
    return tree(0, len(a), lambda i: lnot(add(a[i], b[i])), times, ONE)


def lt_reduce(i0, i1, a, b):
    """logic.h lt_reduce: (a == b, a < b) on the bits i0 .. i1 - 1."""
    if i1 - i0 > 1:
        im = i0 + (i1 - i0) // 2
        eq0, lt0 = lt_reduce(i0, im, a, b)
        eq1, lt1 = lt_reduce(im, i1, a, b)
        return times(eq1, eq0), add(lt1, times(eq1, lt0))
    return lnot(add(a[i0], b[i0])), times(lnot(a[i0]), b[i0])


def vlt(a, b):
    return lt_reduce(0, len(a), a, b)[1]


def vleq_const(a, val):
    """logic.h leq(a, val) = not (val < a)."""
    return lnot(vlt(vbit(len(a), val), a))


def implies_assertion(a, b):
    """The polynomial logic.h assert_implies asserts zero: assert1 of
    lor(not a, b), that is a and not b."""
    return times(a, lnot(b))


def bit_assertion(v):
    """logic.h assert_is_bit: v - v v."""
    return add(v, times(v, v))


# ------------------------------------------- G1, G2: the plucker, LOGN 4
# bit_plucker.h: the points X_i = of_scalar(2 i) - of_scalar(15), and
# for bit k the polynomial of degree below 16 that is bit k of i at X_i.

def plucker_polynomials():
    xs = [of_scalar(2 * i) ^ of_scalar(15) for i in range(16)]
    polys = []
    for k in range(4):
        coef = [0] * 16
        for i in range(16):
            if not (i >> k) & 1:
                continue
            num = [1]
            den = 1
            for j in range(16):
                if j == i:
                    continue
                nxt = [0] * (len(num) + 1)
                for d, c in enumerate(num):
                    nxt[d + 1] ^= c
                    nxt[d] ^= mul(c, xs[j])
                num = nxt
                den = mul(den, xs[i] ^ xs[j])
            w = inv(den)
            for d, c in enumerate(num):
                coef[d] ^= mul(w, c)
        polys.append([(d, c) for d, c in enumerate(coef) if c])
    return polys


PLUCK = None


def pluck(e):
    """The four bits of a packed element, as values."""
    top = max(d for p in PLUCK for d, _ in p)
    pw = [ONE, e]
    for _ in range(2, top + 1):
        pw.append(times(pw[-1], e))
    out = []
    for p in PLUCK:
        v = const(0)
        for d, c in p:
            v = add(v, scale(c, pw[d]))
        out.append(v)
    return out


# ------------------------------------- G3: BitAdderAux, characteristic 2

A2I = []
_a = 2                                  # F.x(), bit_adder.h 85
for _ in range(32):
    A2I.append(_a)
    _a = mul(_a, _a)
A2N = _a


def as_field_element(w):
    """bit_adder.h 98: the product of mux(w[i], alpha^(2^i), 1)."""
    return tree(0, 32, lambda i: add(ONE, scale(A2I[i] ^ 1, w[i])),
                times, ONE)


def eqmod_assertion(a, b, k):
    """bit_adder.h 117: the product over i < k of b - alpha^(i 2^32) A."""
    p = [1]
    for _ in range(1, k):
        p.append(mul(A2N, p[-1]))
    aa = as_field_element(a)
    return tree(0, k, lambda i: add(b, scale(p[i], aa)), times, ONE)


def badd(words):
    return tree(0, len(words), lambda i: as_field_element(words[i]),
                times, ONE)


# ----------------------------------------- G4: flatsha256_circuit.h 89

K256 = [int(x, 16) for x in (
    "428a2f98 71374491 b5c0fbcf e9b5dba5 3956c25b 59f111f1 923f82a4 "
    "ab1c5ed5 d807aa98 12835b01 243185be 550c7dc3 72be5d74 80deb1fe "
    "9bdc06a7 c19bf174 e49b69c1 efbe4786 0fc19dc6 240ca1cc 2de92c6f "
    "4a7484aa 5cb0a9dc 76f988da 983e5152 a831c66d b00327c8 bf597fc7 "
    "c6e00bf3 d5a79147 06ca6351 14292967 27b70a85 2e1b2138 4d2c6dfc "
    "53380d13 650a7354 766a0abb 81c2c92e 92722c85 a2bfe8a1 a81a664b "
    "c24b8b70 c76c51a3 d192e819 d6990624 f40e3585 106aa070 19a4c116 "
    "1e376c08 2748774c 34b0bcb5 391c0cb3 4ed8aa4a 5b9cca4f 682e6ff3 "
    "748f82ee 78a5636f 84c87814 8cc70208 90befffa a4506ceb bef9a3f7 "
    "c67178f2").split()]
H_INIT = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
          0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]


def rotr(x, n):
    return [x[(i + n) % 32] for i in range(32)]


def shr(x, n):
    return [x[i + n] if i + n < 32 else const(0) for i in range(32)]


def xor3(a, b, c):
    return [add(add(a[i], b[i]), c[i]) for i in range(32)]


def transform(win, h0, outw, oute, outa, h1, out):
    """assert_transform_block, flatsha256_circuit.h 89 to 141: appends
    the 184 assertions of one block to out."""
    w = list(win) + outw
    for i in range(16, 64):
        terms = [xor3(rotr(w[i - 2], 17), rotr(w[i - 2], 19), shr(w[i - 2], 10)),
                 w[i - 7],
                 xor3(rotr(w[i - 15], 7), rotr(w[i - 15], 18), shr(w[i - 15], 3)),
                 w[i - 16]]
        out.append(("G3 assert_eqmod, schedule", eqmod_assertion(w[i], badd(terms), 4)))
    a, b, c, d, e, f, g, h = h0
    for t in range(64):
        s1e = xor3(rotr(e, 6), rotr(e, 11), rotr(e, 25))
        ch = [add(times(e[i], f[i]), times(lnot(e[i]), g[i])) for i in range(32)]
        t1 = badd([h, s1e, ch, vbit(32, K256[t]), w[t]])
        s0a = as_field_element(xor3(rotr(a, 2), rotr(a, 13), rotr(a, 22)))
        maj = [add(times(a[i], b[i]), times(add(a[i], b[i]), c[i])) for i in range(32)]
        t2 = times(s0a, as_field_element(maj))
        h, g, f = g, f, e
        e = oute[t]
        out.append(("G3 assert_eqmod, rounds",
                    eqmod_assertion(e, times(t1, as_field_element(d)), 6)))
        d, c, b = c, b, a
        a = outa[t]
        out.append(("G3 assert_eqmod, rounds", eqmod_assertion(a, times(t1, t2), 7)))
    fin = [a, b, c, d, e, f, g, h]
    for i in range(8):
        out.append(("G3 assert_eqmod, H1", eqmod_assertion(
            h1[i], times(as_field_element(h0[i]), as_field_element(fin[i])), 2)))


# -------------------------------------------------- the relation's layout
# src/mdoc_relation-hash.ads: the public inputs X (Public_Count 952)
# come first, then the private inputs W; input i is X (i), and
# W (j) is input 952 + j.

NX = 952                    # Public_Count
NW = 84_166                 # Private_Count
X_ID, X_TAGS = 1, 945
W_E, W_COUNT, W_MESSAGE, W_BLOCKS = 0, 768, 776, 21_112
W_VALID_FROM, W_ITEM_BLOCKS, W_DIGEST_INDEX, W_PADS = \
    79_992, 81_064, 84_008, 84_160
MAX_BLOCKS = 40             # kMaxSHABlocks, mdoc_constants.h 25
TRACE = 1472                # BlockWitness: 184 packed words of 8 elements
PREFIX = [0x84, 0x6A, 0x53, 0x69, 0x67, 0x6E, 0x61, 0x74, 0x75, 0x72,
          0x65, 0x31, 0x43, 0xA1, 0x01, 0x26, 0x40, 0x59]   # Prefix


def bit_positions():
    """The inputs Bits (X, W) says are bits."""
    return (list(range(X_ID, X_TAGS))
            + [NX + j for j in range(W_E, W_BLOCKS)]
            + [NX + j for j in range(W_VALID_FROM, W_ITEM_BLOCKS)]
            + [NX + j for j in range(W_DIGEST_INDEX, W_PADS)])


def required(x):
    """The required assertions of Bits, Chain, Zero_Tail and Length, as
    (group, value), x (i) the value of input i."""
    out = []
    # Bits: Logic::input asserts each bit input, logic.h 976 to 980.
    for i in bit_positions():
        out.append(("Bits: an input is a bit", bit_assertion(x[i])))

    def word_of(elems):
        # BitPlucker::unpack, bit_plucker.h: bit LOGN i + j of the word
        # is bit j of element i.
        r = []
        for e in elems:
            r += pluck(x[e])
        return r[:32]

    def trace(b):
        # BlockWitness::input, flatsha256_circuit.h 69 to 84.
        base = NX + W_BLOCKS + TRACE * b
        outw = [[base + 8 * k + i for i in range(8)] for k in range(48)]
        oute = [[base + 384 + 16 * k + i for i in range(8)] for k in range(64)]
        outa = [[base + 392 + 16 * k + i for i in range(8)] for k in range(64)]
        h1 = [[base + 1408 + 8 * k + i for i in range(8)] for k in range(8)]
        return outw, oute, outa, h1

    # G1: every element of the signed message's traces is plucked, each
    # bit asserted (bit_plucker.h, pluck).
    for b in range(MAX_BLOCKS):
        base = NX + W_BLOCKS + TRACE * b
        for e in range(base, base + TRACE):
            for v in pluck(x[e]):
                out.append(("G1: a plucked bit is a bit", bit_assertion(v)))

    def byte(p):
        # The preimage: the 18 bytes of the prefix, then in_ (mdoc_hash.h
        # 287 to 297); bit t of byte p least significant first.
        if p < len(PREFIX):
            return vbit(8, PREFIX[p])
        return [x[NX + W_MESSAGE + 8 * (p - len(PREFIX)) + t] for t in range(8)]

    # Chain: assert_message, flatsha256_circuit.h 192 to 218; the words
    # big-endian, 204 and 205.
    for b in range(MAX_BLOCKS):
        win = [byte(64 * b + 4 * i + 3) + byte(64 * b + 4 * i + 2)
               + byte(64 * b + 4 * i + 1) + byte(64 * b + 4 * i)
               for i in range(16)]
        outw, oute, outa, h1 = trace(b)
        h0 = ([vbit(32, v) for v in H_INIT] if b == 0
              else [word_of(w) for w in trace(b - 1)[3]])
        transform(win, h0, [word_of(w) for w in outw],
                  [word_of(w) for w in oute], [word_of(w) for w in outa],
                  [word_of(w) for w in h1], out)

    # Chain: assert_hash, flatsha256_circuit.h 236 to 262: the state of
    # block nb, selected and unpacked, equals e in reverse byte order.
    nb = [x[NX + W_COUNT + t] for t in range(8)]
    sel = [[None] * 8 for _ in range(8)]
    for b in range(MAX_BLOCKS):
        ebt = eq_reduce(nb, vbit(8, b + 1))
        h1 = trace(b)[3]
        for i in range(8):
            for k in range(8):
                m = times(ebt, x[h1[i][k]])
                sel[i][k] = m if b == 0 else add(sel[i][k], m)
    for j in range(8):
        hj = []
        for k in range(8):
            hj += pluck(sel[j][k])
        for k in range(32):
            e_bit = x[NX + W_E + (7 - j) * 32 + k]
            out.append(("G4: e is the selected state", add(hj[k], e_bit)))

    # Zero_Tail: assert_zero_padding, flatsha256_circuit.h 267 to 278.
    for i in range(MAX_BLOCKS):
        wantzero = vleq_const(nb, i)
        for j in range(64):
            zero = eq_reduce(byte(64 * i + j), vbit(8, 0))
            out.append(("Zero_Tail: nb <= i implies a zero byte",
                        implies_assertion(wantzero, zero)))

    # Length: find_len, flatsha256_circuit.h 283 to 296, then the checks
    # of extract_vind, mdoc_hash.h 299 to 312.
    ln = vbit(64, 0)
    for i in range(MAX_BLOCKS):
        isblk = eq_reduce(nb, vbit(8, i + 1))
        for j in range(64):
            ln[j] = add(ln[j], times(isblk, byte(64 * i + 63 - j // 8)[j % 8]))
    for j in range(64):
        out.append(("Length: a bit of the length is a bit", bit_assertion(ln[j])))
    for j in list(range(3)) + list(range(15, 64)):
        out.append(("Length: the low 3 and high 49 bits are zero", ln[j]))
    return out


# ------------------------------------------------------------ the circuit

def points(data, n):
    """Two points: input i of point p is the first 16 bytes, little
    endian, of SHA-256 (SHA-256 (file) || p || i), p and i as 4-byte
    little-endian integers. Input 0 is the constant one."""
    d = hashlib.sha256(data).digest()
    pts = []
    for p in range(2):
        v = [1]
        for i in range(1, n):
            h = hashlib.sha256(d + p.to_bytes(4, "little") + i.to_bytes(4, "little"))
            v.append(int.from_bytes(h.digest()[:16], "little"))
        pts.append(v)
    return pts


def evaluate(circ, pts):
    """The values of every assertion of the circuit at both points, and
    an upper bound of its degree: (v1, v2, d)."""
    layers = circ["layers"]
    n = circ["ninput"]
    prev = [(pts[0][i], pts[1][i], 0 if i == 0 else 1) for i in range(n)]
    asserts = []
    for j in range(len(layers) - 1, -1, -1):
        nv = circ["noutput"] if j == 0 else layers[j - 1][1]
        cur0, cur1, deg = [0] * nv, [0] * nv, [0] * nv
        for g, h0, h1, k in layers[j][2]:
            a, b = prev[h1], prev[h0]
            if k == 0:
                asserts.append((mul(a[0], b[0]), mul(a[1], b[1]), a[2] + b[2]))
                continue
            cur0[g] ^= mul(k, mul(a[0], b[0]))
            cur1[g] ^= mul(k, mul(a[1], b[1]))
            deg[g] = max(deg[g], a[2] + b[2])
        prev = list(zip(cur0, cur1, deg))
    return asserts


def key(v1, v2):
    """The class of (v1, v2) up to a nonzero constant, or None for (0, 0)."""
    if v1:
        return mul(v2, inv(v1))
    return "v1 zero" if v2 else None


def check(circ, data, required_fn):
    """The groups with their counts (required, found, missing), and the
    numbers of the error bound."""
    pts = points(data, circ["ninput"])
    asserts = evaluate(circ, pts)
    index = {}
    for v1, v2, d in asserts:
        k = key(v1, v2)
        if k is not None:
            index[k] = max(index.get(k, 0), d)
    x = [(pts[0][i], pts[1][i], 0 if i == 0 else 1) for i in range(circ["ninput"])]
    groups = {}
    dmax = 0
    for group, (v1, v2, d) in required_fn(x):
        req, found, miss = groups.get(group, (0, 0, 0))
        if d == 0:
            # A constant: zero holds by itself, any other is false.
            groups[group] = (req + 1, found + (v1 == 0), miss + (v1 != 0))
            continue
        k = key(v1, v2)
        if k is not None and k in index:
            groups[group] = (req + 1, found + 1, miss)
            dmax = max(dmax, d + index[k])
        else:
            groups[group] = (req + 1, found, miss + 1)
    return groups, len(asserts), max((d for _, _, d in asserts), default=0), dmax


def main(argv):
    if len(argv) != 2:
        print(__doc__.split("\n\n")[-1], file=sys.stderr)
        return 2
    global PLUCK
    t0 = time.time()
    data = Path(argv[1]).read_bytes()
    st, circ, _, _ = cv.read_lfc2(FLD, data)
    if st != "ok":
        print("values-check: the reader refuses the file: %s" % st)
        return 2
    if circ["ninput"] != NX + NW:
        print("values-check: %d inputs, not the %d of the relation's layout"
              % (circ["ninput"], NX + NW))
        return 1
    PLUCK = plucker_polynomials()
    groups, nassert, amax, dmax = check(circ, data, required)
    print("values-check: %s" % hashlib.sha256(data).hexdigest())
    code = report(groups, nassert, amax, dmax)
    print("  time %.0f s" % (time.time() - t0))
    return code


def report(groups, nassert, amax, dmax):
    """Print the counts per group and the error bound; the exit status."""
    nreq = sum(r for r, _, _ in groups.values())
    nmiss = sum(m for _, _, m in groups.values())
    for g in sorted(groups):
        r, f, m = groups[g]
        print("  %-48s required %7d  found %7d  missing %d" % (g, r, f, m))
    print("  required %d, missing %d; the circuit's assertions %d" % (nreq, nmiss, nassert))
    print("  degrees: assertions at most %d; required plus assertion at most %d"
          % (amax, dmax))
    if nassert == 0 or nreq - nmiss == 0:
        print("  error bound: no required assertion found, none to bound")
    else:
        print("  error bound (a tested polynomial identity, not a proof): a"
              " false match at most %d / 2^128 per pair, %d x %d x %d / 2^128"
              " <= 2^%.1f in all" % (dmax, nreq, nassert, dmax,
                                     log2_up(nreq * nassert * max(dmax, 1)) - 128))
    return 0 if nmiss == 0 else 1

def log2_up(n):
    """log2 (n) rounded up to one decimal, so that the bound printed is
    never below the exact fraction."""
    return math.ceil(math.log2(n) * 10) / 10


if __name__ == "__main__":
    sys.exit(main(sys.argv))
