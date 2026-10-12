#!/usr/bin/env python3
"""Generator for the stage 3 sumcheck algebra vectors (ADR 0027):
  sumcheck_gf2_128.txt   over GF(2^128)
  sumcheck_p256.txt      over the P-256 base field

Independent reference written from the definitions of draft-google-cfrg-
libzk-03: eq as the product over the bits of x (Section 6.2), bindeq by the
recursive definition of Section 6.2, bind by the formula of Section 6.1
with zero padding, the Lagrange basis on 0, 1, P2 by division (Section
6.4), eval_quad and eval_circuit per Sections 6.3.2 and 6.3.3 (a term with
k = 0 is a Z assertion). GF(2^128) multiplication is schoolbook then long
division by Q(x), as in gen_gf2_128_vectors.py; P-256 is plain integers mod p.

Self-checks, abort on failure: bindeq (c)[i] = eq (c, i, n) on every case;
the Lagrange denominators times their inverses equal 1; the basis is the
unit vectors at the three points, sums to 1, and interpolates a random
degree-two polynomial; the B.3 circuits evaluate to zero on their witnesses.

Tier 1: the explicit circuits of draft Appendix B.3, term lists copied from
the upstream unit tests (google/longfellow-zk d5e6be7, docs/specs/rust/
tests/unit_tests.rs, create_sgonal_circuit_p256 / _gf2_128); B.3.2 over the
base field (the draft's "scalar field" label is an erratum, the printed
order is the base field prime, Table 1 FieldID 0x01); B.3.3 with the input
n computed in the field, 0x6c, the draft's 84 being an erratum (ADR 0027).
Plus a small circuit with a Z assertion, and failing cases.
Tier 2: structural and seeded random cases of eq, eq2, bindeq, bind,
lagrange.

File format (one case per line, '#' comments, blanks separate fields,
elements as big-endian hex of the integer, 32 digits on GF(2^128), 64 on
P-256):
  field <gf2_128|p256>
  const <p2|l0inv|l1inv|l2inv> <value>
  eq <n> <x> <r_0 .. r_n-1> <expected>
  eq2 <n> <x> <alpha> <g0_0 .. g0_n-1> <g1_0 .. g1_n-1> <expected>
  bindeq <n> <c_0 .. c_n-1> <b_0 .. b_2^n-1>
  bind <len> <x> <a_0 .. a_len-1> <b_0 .. b_ceil(len/2)-1>
  lagrange <r> <l0> <l1> <l2>
  circuit <name> <noutput> <ninput> <npublic> <nl>
  layer <j> <logw> <nw_in> <nterms>      (then nterms lines)
  term <g> <h0> <h1> <k>
  witness <w_0 .. w_ninput-1>
  wires <j> <v_0 .. v_size-1>             (segment j, j = 0 .. nl; nl = input)
  expect <ok|fail>
  end

Usage: python3 -I gen_sumcheck_vectors.py [output-directory]
Output is deterministic (fixed seed, no timestamps).
"""

import random
import sys
from pathlib import Path

SEED = 20261012


def fail(msg: str) -> None:
    print(f"gen_sumcheck_vectors: FAILED: {msg}", file=sys.stderr)
    sys.exit(1)


# ---------------------------------------------------------------- fields

class GF2_128:
    name = "gf2_128"
    digits = 32
    Q = (1 << 128) | 0x87
    P2 = 0x5c5971877501d4b8f1871e01b64fda4c      # beta_1 = inj(2)

    @staticmethod
    def add(a, b): return a ^ b
    sub = add

    @staticmethod
    def neg(a): return a

    @staticmethod
    def mul(a, b):
        r = 0
        while b:
            if b & 1:
                r ^= a
            a <<= 1
            b >>= 1
        for i in range(r.bit_length() - 1, 127, -1):
            if (r >> i) & 1:
                r ^= GF2_128.Q << (i - 128)
        return r

    @staticmethod
    def inv(a):
        if a == 0:
            fail("inverse of zero in GF(2^128)")
        r0, r1, s0, s1 = GF2_128.Q, a, 0, 1
        while r1 != 1:
            d = r0.bit_length() - r1.bit_length()
            if d < 0:
                r0, r1, s0, s1 = r1, r0, s1, s0
                continue
            r0 ^= r1 << d
            s0 ^= s1 << d
        s1 = GF2_128.mul(s1, 1)      # reduce
        if GF2_128.mul(a, s1) != 1:
            fail("GF(2^128) inverse check")
        return s1

    @staticmethod
    def of_int(n):
        return n                     # small integers as polynomial bit patterns

    @staticmethod
    def random(rng):
        return rng.getrandbits(128)


class P256:
    name = "p256"
    digits = 64
    P = 2**256 - 2**224 + 2**192 + 2**96 - 1
    P2 = 2

    @staticmethod
    def add(a, b): return (a + b) % P256.P

    @staticmethod
    def sub(a, b): return (a - b) % P256.P

    @staticmethod
    def neg(a): return (-a) % P256.P

    @staticmethod
    def mul(a, b): return (a * b) % P256.P

    @staticmethod
    def inv(a):
        if a == 0:
            fail("inverse of zero in P-256")
        r = pow(a, P256.P - 2, P256.P)
        if P256.mul(a, r) != 1:
            fail("P-256 inverse check")
        return r

    @staticmethod
    def of_int(n):
        return n % P256.P

    @staticmethod
    def random(rng):
        return rng.randrange(P256.P)


# ------------------------------------------------------------- algebra

def eq(F, r, x, n):
    product = 1
    for b in range(n):
        if (x >> b) & 1:
            product = F.mul(product, r[b])
        else:
            product = F.mul(product, F.sub(1, r[b]))
    return product


def eq2(F, x, n, g0, g1, alpha):
    return F.add(eq(F, g0, x, n), F.mul(alpha, eq(F, g1, x, n)))


def bindeq(F, c):
    if len(c) == 0:
        return [1]
    a = bindeq(F, c[1:])
    b = [0] * (2 * len(a))
    for i in range(len(a)):
        b[2 * i] = F.mul(F.sub(1, c[0]), a[i])
        b[2 * i + 1] = F.mul(c[0], a[i])
    return b


def bind(F, a, x):
    def at(i): return a[i] if i < len(a) else 0
    return [F.add(F.mul(F.sub(1, x), at(2 * i)), F.mul(x, at(2 * i + 1)))
            for i in range((len(a) + 1) // 2)]


def lagrange_dens(F):
    x0, x1, x2 = 0, 1, F.P2
    d0 = F.mul(F.sub(x0, x1), F.sub(x0, x2))
    d1 = F.mul(F.sub(x1, x0), F.sub(x1, x2))
    d2 = F.mul(F.sub(x2, x0), F.sub(x2, x1))
    return d0, d1, d2


def lagrange(F, r):
    x0, x1, x2 = 0, 1, F.P2
    d0, d1, d2 = lagrange_dens(F)
    l0 = F.mul(F.mul(F.sub(r, x1), F.sub(r, x2)), F.inv(d0))
    l1 = F.mul(F.mul(F.sub(r, x0), F.sub(r, x2)), F.inv(d1))
    l2 = F.mul(F.mul(F.sub(r, x0), F.sub(r, x1)), F.inv(d2))
    return [l0, l1, l2]


def eval_quad(F, nv, w, terms):
    """terms: list of (g, h0, h1, k). Returns (v, z_ok)."""
    v = [0] * nv
    z_ok = True
    for g, h0, h1, k in terms:
        if k == 0:
            if F.mul(w[h1], w[h0]) != 0:
                z_ok = False
        else:
            v[g] = F.add(v[g], F.mul(F.mul(k, w[h1]), w[h0]))
    return v, z_ok


def eval_circuit(F, circuit, w):
    """circuit: dict(noutput, ninput, npublic, layers=[(logw, nw_in, terms)]).
    Returns (segments, ok): segments[j] = V[j], j = 0 .. nl (nl = inputs)."""
    layers = circuit["layers"]
    nl = len(layers)
    segments = [None] * (nl + 1)
    segments[nl] = list(w)
    ok = True
    cur = list(w)
    for j in range(nl - 1, -1, -1):
        nv = circuit["noutput"] if j == 0 else layers[j - 1][1]
        cur, z_ok = eval_quad(F, nv, cur, layers[j][2])
        ok = ok and z_ok
        segments[j] = cur
    ok = ok and all(x == 0 for x in cur)
    return segments, ok


# ------------------------------------------------------------ circuits

def sgonal_p256():
    k = P256.of_int
    layer1 = [(0, 0, 0, k(1)), (1, 2, 2, k(1)), (2, 0, 3, k(1)), (2, 0, 0, k(-2)),
              (3, 2, 3, k(1)), (3, 0, 2, k(-4)), (4, 0, 1, k(2))]
    layer0 = [(0, 1, 2, k(1)), (0, 0, 3, k(-1)), (0, 0, 4, k(-1))]
    return {"name": "b3_2_sgonal", "noutput": 1, "ninput": 4, "npublic": 1,
            "layers": [(3, 5, layer0), (2, 4, layer1)]}


def sgonal_gf2_128():
    one = 1
    layer1 = [(0, 0, 0, one), (1, 2, 2, one), (2, 0, 3, one), (2, 0, 0, one),
              (3, 2, 3, one), (3, 0, 2, one), (4, 0, 1, one)]
    layer0 = [(0, 1, 2, one), (0, 0, 3, one), (0, 0, 4, one)]
    return {"name": "b3_3_quadratic", "noutput": 1, "ninput": 4, "npublic": 1,
            "layers": [(3, 5, layer0), (2, 4, layer1)]}


def zcheck():
    # y0 = w1 * w2 (Q), and the Z assertion w1 * w1 = 0 on output index 1.
    layer0 = [(0, 1, 2, 1), (1, 1, 1, 0)]
    return {"name": "zcheck", "noutput": 2, "ninput": 3, "npublic": 1,
            "layers": [(2, 3, layer0)]}


# -------------------------------------------------------------- output

def main() -> None:
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent
    for F in (GF2_128, P256):
        write_field(F, out_dir)


def write_field(F, out_dir: Path) -> None:
    rng = random.Random(SEED)
    hx = lambda v: f"{v:0{F.digits}x}"
    lines = []
    emit = lines.append
    emit(f"# Sumcheck algebra vectors over {F.name}, Longfellow ZK stage 3 (ADR 0027).")
    emit("# Generated by gen_sumcheck_vectors.py (this directory); do not edit by hand.")
    emit("# Format: see the generator's docstring. Elements are big-endian hex.")
    emit(f"field {F.name}")

    # constants
    d0, d1, d2 = lagrange_dens(F)
    inv = [F.inv(d) for d in (d0, d1, d2)]
    for d, i in zip((d0, d1, d2), inv):
        if F.mul(d, i) != 1:
            fail("Lagrange denominator inverse")
    emit("# Evaluation point P2 and the inverses of the Lagrange denominators (ADR 0025).")
    emit(f"const p2 {hx(F.P2)}")
    emit(f"const l0inv {hx(inv[0])}")
    emit(f"const l1inv {hx(inv[1])}")
    emit(f"const l2inv {hx(inv[2])}")

    # eq: structural
    emit("# eq (Section 6.2): structural cases, then seeded random cases.")
    def eq_case(n, x, r):
        emit(f"eq {n} {x} " + " ".join(hx(v) for v in r) + (" " if r else "") + hx(eq(F, r, x, n)))
    eq_case(0, 0, [])
    eq_case(0, 5, [])
    eq_case(3, 0, [0, 0, 0])
    eq_case(3, 1, [0, 0, 0])
    eq_case(3, 7, [1, 1, 1])
    eq_case(3, 6, [1, 1, 1])
    eq_case(2, 2, [F.P2, F.P2])
    for n in (1, 2, 3, 5, 8, 12):
        for _ in range(3):
            r = [F.random(rng) for _ in range(n)]
            eq_case(n, rng.getrandbits(n), r)
        # x with bits above n set: eq reads the low n bits only
        r = [F.random(rng) for _ in range(n)]
        eq_case(n, rng.getrandbits(n) | (1 << n) | (1 << (n + 3)), r)

    emit("# eq2 (Section 6.2): eq (g0, x) + alpha * eq (g1, x).")
    for n in (1, 3, 6):
        for _ in range(3):
            g0 = [F.random(rng) for _ in range(n)]
            g1 = [F.random(rng) for _ in range(n)]
            alpha = F.random(rng)
            x = rng.getrandbits(n)
            emit(f"eq2 {n} {x} {hx(alpha)} " + " ".join(hx(v) for v in g0 + g1)
                 + " " + hx(eq2(F, x, n, g0, g1, alpha)))

    emit("# bindeq (Section 6.2), by the recursive definition; checked against eq.")
    for n in range(0, 5):
        for _ in range(2 if n > 0 else 1):
            c = [F.random(rng) for _ in range(n)]
            b = bindeq(F, c)
            for i, bi in enumerate(b):
                if bi != eq(F, c, i, n):
                    fail("bindeq disagrees with eq")
            emit(f"bindeq {n} " + " ".join(hx(v) for v in c + b))
    # structural: all-zero and all-one challenges
    for c in ([0, 0, 0], [1, 1, 1]):
        emit(f"bindeq 3 " + " ".join(hx(v) for v in c + bindeq(F, c)))

    emit("# bind (Section 6.1): b[i] = (1 - x) a[2i] + x a[2i+1], zero padding.")
    for ln in (0, 1, 2, 3, 4, 7, 8):
        a = [F.random(rng) for _ in range(ln)]
        x = F.random(rng)
        emit(f"bind {ln} {hx(x)} " + " ".join(hx(v) for v in a + bind(F, a, x)))
    a = [F.random(rng) for _ in range(5)]
    emit(f"bind 5 {hx(0)} " + " ".join(hx(v) for v in a + bind(F, a, 0)))
    emit(f"bind 5 {hx(1)} " + " ".join(hx(v) for v in a + bind(F, a, 1)))

    emit("# lagrange (Section 6.4): the three points give the unit vectors; random r.")
    for r, unit in ((0, [1, 0, 0]), (1, [0, 1, 0]), (F.P2, [0, 0, 1])):
        l = lagrange(F, r)
        if l != unit:
            fail("Lagrange basis at an evaluation point")
        emit(f"lagrange {hx(r)} " + " ".join(hx(v) for v in l))
    for _ in range(4):
        r = F.random(rng)
        l = lagrange(F, r)
        if F.add(F.add(l[0], l[1]), l[2]) != 1:
            fail("Lagrange basis does not sum to one")
        # interpolation of a random degree-two polynomial
        a0, a1, a2 = (F.random(rng) for _ in range(3))
        def poly(t): return F.add(F.add(a0, F.mul(a1, t)), F.mul(a2, F.mul(t, t)))
        interp = 0
        for li, xi in zip(l, (0, 1, F.P2)):
            interp = F.add(interp, F.mul(li, poly(xi)))
        if interp != poly(r):
            fail("Lagrange basis does not interpolate")
        emit(f"lagrange {hx(r)} " + " ".join(hx(v) for v in l))

    emit("# Tier 1: explicit circuits (draft Appendix B.3, upstream unit_tests.rs).")
    if F is P256:
        circ = sgonal_p256()
        good = [F.of_int(v) for v in (1, 45, 5, 6)]
        bad = [F.of_int(v) for v in (1, 46, 5, 6)]
    else:
        circ = sgonal_gf2_128()
        m, s = 5, 6
        s1 = F.add(s, 1)
        n = F.add(F.mul(s1, F.mul(m, m)), F.mul(s1, m))
        if n != 0x6c:
            fail("B.3.3 input n")
        good = [1, n, m, s]
        bad = [1, F.add(n, 1), m, s]
    for witness, expect in ((good, True), (bad, False)):
        write_circuit(F, emit, hx, circ, witness, expect)
    zc = zcheck()
    for witness, expect in (([1, 0, F.of_int(7)], True),
                            ([1, F.of_int(3), 0], False),
                            ([1, F.of_int(2), F.of_int(3)], False)):
        write_circuit(F, emit, hx, zc, witness, expect)

    path = out_dir / f"sumcheck_{F.name}.txt"
    path.write_text("\n".join(lines) + "\n")
    print(f"wrote {path}: {sum(1 for l in lines if l and l[0] != '#')} lines")


def write_circuit(F, emit, hx, circ, witness, expect_ok) -> None:
    segments, ok = eval_circuit(F, circ, witness)
    if ok != expect_ok:
        fail(f"circuit {circ['name']}: expected ok={expect_ok}, got {ok}")
    nl = len(circ["layers"])
    emit(f"circuit {circ['name']} {circ['noutput']} {circ['ninput']} {circ['npublic']} {nl}")
    for j, (logw, nw_in, terms) in enumerate(circ["layers"]):
        emit(f"layer {j} {logw} {nw_in} {len(terms)}")
        for g, h0, h1, k in terms:
            emit(f"term {g} {h0} {h1} {hx(k)}")
    emit("witness " + " ".join(hx(v) for v in witness))
    for j in range(nl + 1):
        emit(f"wires {j} " + " ".join(hx(v) for v in segments[j]))
    emit("expect " + ("ok" if ok else "fail"))
    emit("end")


if __name__ == "__main__":
    main()
