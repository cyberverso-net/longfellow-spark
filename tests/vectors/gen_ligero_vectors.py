#!/usr/bin/env python3
"""Generator for the stage 5 (Ligero) known-answer vectors:
  merkle.txt            build <n> <leaves...> <root>
                        verify <n> <root> <k> <indices...> <leaves...>
                               <m> <path...> <ok>
  ligero_geometry.txt   geometry <rate_inv> <nreq> <ncol> <nw> <nq> <valid>
                               [<block> <dblock> <wr> <nwrow> <nqt> <nrow>]
  lagrange_<field>.txt  table <k> <m> <m columns> <k inv_d> <k*m entries>
                        eval <k> <m> <m columns> <k coeffs> <c> <expected>

Independent Python reference of the Merkle tree of IETF
draft-google-cfrg-libzk-03, Section 4.1, written from the draft's text:
the heap of 2 n digests (4.1.2), the batch opening (4.1.3) and the batch
verification (4.1.4). hashlib for SHA-256, no third-party package.

Tier 1 is Appendix B.1.1: the five leaves, the root and the batch proofs
for leaves (0, 1) and (1, 3), copied from the draft; the generator
recomputes them and aborts on any mismatch, so its reference is
anchored on the draft before it generates anything. Tier 2 is trees of
1 to 9 leaves (leaf i the SHA-256 of the string "leaf i") with batch
openings of every non-empty subset for up to 5 leaves and of the
subsets of size 1, 2, 3 and n beyond, each verified by the reference.
Negative cases, each expected to fail: an altered path digest, a path
one digest too long and one too short, a duplicate index, an index at
or above n, no index, an altered leaf, an altered root.

Geometry: LigeroGeometry::new of the reference transcribed (the
constraints of 4.2.1 and the row counts), on the configuration of the
Appendix B.3 vectors, whose derived numbers the draft prints (BLOCK 10,
DBLOCK 19, WR 4, NW 29, NQ 2, NWROW 8, NQT 1, NROW 14: checked, the
generator aborts otherwise), on a range of other configurations, and on
configurations that violate 4.2.1 (valid 0).

Lagrange: lagrange_matrix of the reference transcribed over both fields
(GF(2^128) with the arithmetic of gen_gf2_128_vectors.py and the
evaluation points inj(x) on the subfield basis; P-256 with integers
modulo p and the points x), checked against an independent evaluation
(the interpolating polynomial found by solving the Vandermonde system
and evaluated directly) before anything is written; the files hold the
entries at a few queried columns and encode_row at those columns.

The Ligero proof and verifier vectors of ADR 0040 come with blocks 4
and 5.

Usage: python3 -I gen_ligero_vectors.py [output-directory]
Output is deterministic (no timestamps).
"""

import hashlib
import importlib.util
import itertools
import random
import sys
from pathlib import Path

HERE = Path(__file__).parent


def load_sibling(name):
    """A sibling generator as a module, for its field arithmetic."""
    spec = importlib.util.spec_from_file_location(name, HERE / (name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def sha256(data):
    return hashlib.sha256(data).digest()


# ----------------------------------------------------------------------
# Section 4.1, transcribed
# ----------------------------------------------------------------------


def merkle_heap(leaves):
    """4.1.2: layers[n .. 2n) are the leaves, layers[i] = H(layers[2i] ||
    layers[2i + 1]) for i from n - 1 down to 1; the root is layers[1]."""
    n = len(leaves)
    layers = [b""] * (2 * n)
    layers[n:2 * n] = leaves
    for i in range(n - 1, 0, -1):
        layers[i] = sha256(layers[2 * i] + layers[2 * i + 1])
    return layers


def merkle_open(layers, n, indices):
    """4.1.3: the siblings needed along the paths, from n - 1 down to 1."""
    seen = [False] * n
    on_path = [False] * (2 * n)
    for idx in indices:
        if idx >= n or seen[idx]:
            raise ValueError("bad index in opening")
        seen[idx] = True
        on_path[n + idx] = True
    for i in range(n - 1, 0, -1):
        on_path[i] = on_path[2 * i] or on_path[2 * i + 1]
    path = []
    for i in range(n - 1, 0, -1):
        if on_path[i]:
            if on_path[2 * i] and not on_path[2 * i + 1]:
                path.append(layers[2 * i + 1])
            elif not on_path[2 * i] and on_path[2 * i + 1]:
                path.append(layers[2 * i])
    return path


def merkle_verify(n, root, indices, leaves, path):
    """4.1.4: the reconstruction; False on any of the draft's failures."""
    seen = [False] * n
    on_path = [False] * (2 * n)
    for idx in indices:
        if idx >= n or seen[idx]:
            return False
        seen[idx] = True
        on_path[n + idx] = True
    for i in range(n - 1, 0, -1):
        on_path[i] = on_path[2 * i] or on_path[2 * i + 1]
    nodes = [None] * (2 * n)
    for idx, leaf in zip(indices, leaves):
        nodes[n + idx] = leaf
    pos = 0
    for i in range(n - 1, 0, -1):
        if on_path[i]:
            children = []
            for j in (2 * i, 2 * i + 1):
                if on_path[j]:
                    children.append(nodes[j])
                else:
                    if pos >= len(path):
                        return False
                    children.append(path[pos])
                    pos += 1
            nodes[i] = sha256(children[0] + children[1])
    if pos != len(path):
        return False
    return nodes[1] is not None and nodes[1] == root


# ----------------------------------------------------------------------
# Appendix B.1.1, copied from the draft
# ----------------------------------------------------------------------

B11_LEAVES = [
    "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
    "dbc1b4c900ffe48d575b5da5c638040125f65db0fe3e24494b76ea986457d986",
    "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
    "e52d9c508c502347344d8c07ad91cbd6068afc75ff6292f062a09ca381c89e71",
    "e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db",
]
B11_ROOT = "f22f4501ffd3bdffcecc9e4cd6828a4479aeedd6aa484eb7c1f808ccf71c6e76"
B11_PROOFS = {
    (0, 1): [
        "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
        "f03808f5b8088c61286d505e8e93aa378991d9889ae2d874433ca06acabcd493",
    ],
    (1, 3): [
        "e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db",
        "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
        "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
    ],
}


def fail(msg):
    print("gen_ligero_vectors: " + msg, file=sys.stderr)
    sys.exit(1)


def check_b11():
    leaves = [bytes.fromhex(h) for h in B11_LEAVES]
    layers = merkle_heap(leaves)
    if layers[1].hex() != B11_ROOT:
        fail("B.1.1 root: got " + layers[1].hex())
    for idx, want in B11_PROOFS.items():
        got = [d.hex() for d in merkle_open(layers, len(leaves), list(idx))]
        if got != want:
            fail("B.1.1 proof for %s: got %s" % (idx, got))
        if not merkle_verify(len(leaves), layers[1], list(idx),
                             [leaves[i] for i in idx],
                             [bytes.fromhex(h) for h in want]):
            fail("B.1.1 proof for %s does not verify" % (idx,))


# ----------------------------------------------------------------------
# Section 4.2: the geometry, LigeroGeometry::new transcribed
# ----------------------------------------------------------------------

MAX_ENCODED_LEN = 2**16
MAX_QUERIES = 2**12


def geometry(rate_inv, nreq, ncol, nw, nq):
    """The fields of LigeroGeometry, or None when 4.2.1 is violated."""
    if ncol > MAX_ENCODED_LEN or nreq > MAX_QUERIES or nreq < 1:
        return None
    block = (ncol + 1) // (2 + rate_inv)
    if block == 0:
        return None
    dblock = 2 * block - 1
    if ncol < dblock or ncol - dblock < nreq or block <= nreq:
        return None
    wr = block - nreq
    nwrow = (nw + wr - 1) // wr
    nqt = (nq + wr - 1) // wr
    return {"block": block, "dblock": dblock, "wr": wr, "nwrow": nwrow,
            "nqt": nqt, "nrow": 3 + nwrow + 3 * nqt}


# Appendix B.3.2: "Derived geometry: BLOCK = 10, DBLOCK = 19, WR = 4,
# NW = 29, NQ = 2, NWROW = 8, NQT = 1, NROW = 14" for RATE_INV 4, NREQ 6,
# NCOL 64.
B32_GEOMETRY = {"block": 10, "dblock": 19, "wr": 4, "nwrow": 8, "nqt": 1,
                "nrow": 14}


def check_geometry():
    if geometry(4, 6, 64, 29, 2) != B32_GEOMETRY:
        fail("B.3.2 geometry: got %s" % geometry(4, 6, 64, 29, 2))


GEOMETRY_CASES = [
    (4, 6, 64, 29, 2), (4, 6, 64, 1, 0), (4, 6, 64, 4, 1), (4, 6, 64, 5, 5),
    (4, 16, 256, 1000, 50), (7, 132, 2048, 10000, 300), (7, 132, 65536, 1, 1),
    (3, 2, 16, 7, 3), (1, 1, 8, 3, 1),
    # violations of 4.2.1
    (4, 6, 5, 1, 1), (4, 10, 64, 1, 1), (4, 16, 70, 1, 1), (4, 6, 65537, 1, 1),
    (4, 5000, 65536, 1, 1),
]


# ----------------------------------------------------------------------
# Lagrange interpolation, algebra/interpolation.rs transcribed
# ----------------------------------------------------------------------


class GF2128:
    """GF(2^128) through the sibling generator; inj on the basis."""

    name = "gf2_128"

    def __init__(self):
        g = load_sibling("gen_gf2_128_vectors")
        self.g = g
        self.basis = list(g.UPSTREAM_SUBFIELD_BASIS)

    def add(self, a, b):
        return a ^ b

    sub = add

    def mul(self, a, b):
        return self.g.mul(a, b)

    def inv(self, a):
        return self.g.inv_euclid(a)

    def point(self, x):
        r = 0
        for i in range(16):
            if (x >> i) & 1:
                r ^= self.basis[i]
        return r

    def rand(self, rng):
        return rng.getrandbits(128)

    def hx(self, v):
        return "%032x" % v


class P256:
    """The P-256 base field as integers modulo p; the points x."""

    name = "p256"
    p = 2**256 - 2**224 + 2**192 + 2**96 - 1

    def add(self, a, b):
        return (a + b) % self.p

    def sub(self, a, b):
        return (a - b) % self.p

    def mul(self, a, b):
        return (a * b) % self.p

    def inv(self, a):
        return pow(a, self.p - 2, self.p)

    def point(self, x):
        return x % self.p

    def rand(self, rng):
        return rng.getrandbits(256) % self.p

    def hx(self, v):
        return "%064x" % v


def lagrange_matrix(fld, pts, k, n):
    """algebra/interpolation.rs: k rows of n entries, row-major."""
    inv_d = []
    for i in range(k):
        d = 1
        for j in range(k):
            if i != j:
                d = fld.mul(d, fld.sub(pts[i], pts[j]))
        inv_d.append(fld.inv(d))
    l = [0] * (k * n)
    for i in range(k):
        for x in range(n):
            if x < k:
                l[i * n + x] = 1 if x == i else 0
            else:
                num = 1
                for j in range(k):
                    if j != i:
                        num = fld.mul(num, fld.sub(pts[x], pts[j]))
                l[i * n + x] = fld.mul(num, inv_d[i])
    return inv_d, l


def encode_row(fld, l, k, n, row):
    """ligero/reed_solomon.rs: for each column, the sum over i."""
    out = []
    for x in range(n):
        s = 0
        for i in range(k):
            s = fld.add(s, fld.mul(row[i], l[i * n + x]))
        out.append(s)
    return out


def solve_vandermonde(fld, pts, values):
    """The coefficients of the polynomial of degree below k through the
    points, by Gaussian elimination: an evaluation independent of the
    Lagrange formula."""
    k = len(values)
    m = [[1] * k for _ in range(k)]
    for r in range(k):
        v = 1
        for c in range(k):
            m[r][c] = v
            v = fld.mul(v, pts[r])
    rhs = list(values)
    for c in range(k):
        piv = next(r for r in range(c, k) if m[r][c] != 0)
        m[c], m[piv] = m[piv], m[c]
        rhs[c], rhs[piv] = rhs[piv], rhs[c]
        inv = fld.inv(m[c][c])
        m[c] = [fld.mul(x, inv) for x in m[c]]
        rhs[c] = fld.mul(rhs[c], inv)
        for r in range(k):
            if r != c and m[r][c] != 0:
                f = m[r][c]
                m[r] = [fld.sub(a, fld.mul(f, b)) for a, b in zip(m[r], m[c])]
                rhs[r] = fld.sub(rhs[r], fld.mul(f, rhs[c]))
    return rhs


def poly_eval(fld, coeffs, x):
    r = 0
    for c in reversed(coeffs):
        r = fld.add(fld.mul(r, x), c)
    return r


# Small dimensions on purpose: under assertions every P-256
# multiplication executes its big-integer contract and each inverse of
# Build is 256 of them, about five seconds per row of the table. The
# mathematics is carried by the reference above; dimension 19 of the
# Appendix B.3 vectors is exercised end to end by the verifier.
LAGRANGE_CASES = [(3, 8, [3, 5]), (5, 16, [5, 15]), (10, 64, [19, 63])]


def lagrange_lines(fld, rng):
    lines = ["field " + fld.name]
    for k, n, cols in LAGRANGE_CASES:
        pts = [fld.point(x) for x in range(n)]
        inv_d, l = lagrange_matrix(fld, pts, k, n)
        for _ in range(2):
            row = [fld.rand(rng) for _ in range(k)]
            enc = encode_row(fld, l, k, n, row)
            if enc[:k] != row:
                fail("interpolation property fails for k=%d" % k)
            coeffs = solve_vandermonde(fld, pts[:k], row)
            for x in range(n):
                if poly_eval(fld, coeffs, pts[x]) != enc[x]:
                    fail("Lagrange encoding differs from the interpolating"
                         " polynomial at x=%d, k=%d (%s)" % (x, k, fld.name))
            lines.append("eval %d %d %s %s %d %s"
                         % (k, len(cols), " ".join(str(c) for c in cols),
                            " ".join(fld.hx(v) for v in row), 0,
                            fld.hx(enc[cols[0]])))
            lines.append("eval %d %d %s %s %d %s"
                         % (k, len(cols), " ".join(str(c) for c in cols),
                            " ".join(fld.hx(v) for v in row), len(cols) - 1,
                            fld.hx(enc[cols[-1]])))
        entries = [l[i * n + x] for i in range(k) for x in cols]
        lines.append("table %d %d %s %s %s"
                     % (k, len(cols), " ".join(str(c) for c in cols),
                        " ".join(fld.hx(v) for v in inv_d),
                        " ".join(fld.hx(v) for v in entries)))
    return lines



# ----------------------------------------------------------------------
# The Ligero proof reader (Section 7.4): write_ligero_proof transcribed
# ----------------------------------------------------------------------

# A small geometry for the reader: BLOCK 4, DBLOCK 7, WR 2, NWROW 3,
# NQT 1, NROW 9, 18 opened elements, 9 leaves.
READER_GEOMETRY = (2, 2, 16, 5, 1)


def elt_bytes(fld, v):
    """Section 7.2.1: little-endian, 16 or 32 bytes."""
    return v.to_bytes(32 if fld.name == "p256" else 16, "little")


def sub_bytes(fld, v, x):
    """Section 7.2.2: the two coordinate bytes on the basis for
    GF(2^128) (x the coordinates of v), the field's encoding for
    P-256, whose subfield is the field."""
    if fld.name == "p256":
        return elt_bytes(fld, v)
    return x.to_bytes(2, "little")


def write_ligero_proof(fld, polys, nonces, cols, path):
    """write_ligero_proof of Section 7.4: the polynomials, the nonces,
    the opened columns in alternating runs, full field first, each a
    4-byte little-endian count then its elements, then the path with
    its count. cols is a list of (value, x): x the subfield
    coordinates when the encoder sees the element in the subfield
    (contains_subfield), None otherwise; on P-256 every element is."""
    out = b"".join(elt_bytes(fld, v) for poly in polys for v in poly)
    out += b"".join(nonces)
    i = 0
    subfield_run = False
    total = len(cols)
    while i < total:
        runlen = 0
        while (i + runlen < total
               and (cols[i + runlen][1] is not None) == subfield_run):
            runlen += 1
        out += runlen.to_bytes(4, "little")
        for j in range(i, i + runlen):
            v, x = cols[j]
            out += sub_bytes(fld, v, x) if subfield_run else elt_bytes(fld, v)
        i += runlen
        subfield_run = not subfield_run
    out += len(path).to_bytes(4, "little") + b"".join(path)
    return out


def reader_lines(fld, rng):
    """read cases: the geometry, the status the reader must give, the
    bytes, and for an accepted proof its content."""
    rate_inv, nreq, ncol, nw, nq = READER_GEOMETRY
    g = geometry(rate_inv, nreq, ncol, nw, nq)
    assert g == {"block": 4, "dblock": 7, "wr": 2, "nwrow": 3, "nqt": 1,
                 "nrow": 9}
    total = g["nrow"] * nreq
    polys = [[fld.rand(rng) for _ in range(n)]
             for n in (g["block"], g["dblock"], nreq,
                       g["dblock"] - g["block"])]
    nonces = [rng.randbytes(32) for _ in range(nreq)]
    path = [rng.randbytes(32) for _ in range(5)]

    def sub_elt():
        x = rng.getrandbits(16)
        return (fld.point(x), x)

    def full_elt():
        if fld.name == "p256":
            v = fld.rand(rng)
            return (v, v)
        return (fld.rand(rng), None)

    def line(status, data, cols=None):
        s = "read %d %d %d %d %d %s %s" % (rate_inv, nreq, ncol, nw, nq,
                                           status, data.hex())
        if cols is not None:
            elts = [v for poly in polys for v in poly] + [v for v, _ in cols]
            s += " %d %s %d %s %d %s" % (
                len(elts), " ".join(fld.hx(v) for v in elts),
                len(nonces), " ".join(n.hex() for n in nonces),
                len(path), " ".join(d.hex() for d in path))
        return s

    lines = ["field " + fld.name]
    if fld.name == "p256":
        # Every element is in the subfield: a zero-length full-field
        # run, then one subfield run of all, as Appendix B.3.2.
        good = [full_elt() for _ in range(total)]
        sets = [("all in the subfield", good)]
    else:
        sets = [
            ("all full field", [full_elt() for _ in range(total)]),
            ("subfield, full, subfield", [sub_elt() for _ in range(5)]
             + [full_elt() for _ in range(7)] + [sub_elt() for _ in range(6)]),
            ("all subfield", [sub_elt() for _ in range(total)]),
        ]
        good = sets[1][1]
    for what, cols in sets:
        lines.append("# " + what)
        lines.append(line("ok", write_ligero_proof(fld, polys, nonces, cols,
                                                   path), cols))
    data = write_ligero_proof(fld, polys, nonces, good, path)
    fixed = sum(len(p) for p in polys) * (32 if fld.name == "p256" else 16) \
        + 32 * nreq
    head = data[:fixed]
    zero = (0).to_bytes(4, "little")
    lines.append("# a second zero-length run")
    lines.append(line("encoding", head + zero + data[fixed:]))
    lines.append("# a zero-length run that is not the first")
    first_sub = [c for c in good if c[1] is not None][:5]
    body = zero + (5).to_bytes(4, "little") \
        + b"".join(sub_bytes(fld, v, x) for v, x in first_sub) + zero
    lines.append(line("encoding", head + body + data[fixed:]))
    lines.append("# a run beyond the total")
    extra = [full_elt() for _ in range(total + 1)]
    body = (total + 1).to_bytes(4, "little") \
        + b"".join(elt_bytes(fld, v) for v, _ in extra)
    lines.append(line("encoding", head + body + data[-4 - 32 * 5:]))
    lines.append("# a run beyond 2^25")
    lines.append(line("encoding", head + (2**25 + 1).to_bytes(4, "little")))
    lines.append("# bytes missing")
    lines.append(line("encoding", data[:-16]))
    lines.append("# a path count beyond the tree")
    long_path = [rng.randbytes(32) for _ in range(19)]
    lines.append(line("encoding", write_ligero_proof(fld, polys, nonces, good,
                                                     long_path)))
    if fld.name == "p256":
        lines.append("# a non-canonical element")
        lines.append(line("encoding", b"\xff" * 32 + data[32:]))
    return lines

# ----------------------------------------------------------------------
# Output
# ----------------------------------------------------------------------


def hx(b):
    return b.hex()


def verify_line(n, root, indices, leaves, path, ok):
    return ("verify %d %s %d %s %s %d %s %d"
            % (n, hx(root), len(indices),
               " ".join(str(i) for i in indices),
               " ".join(hx(l) for l in leaves),
               len(path), " ".join(hx(p) for p in path), 1 if ok else 0)
            ).replace("  ", " ")


def tier2_subsets(n):
    if n <= 5:
        sizes = range(1, n + 1)
    else:
        sizes = [1, 2, 3, n]
    for k in sizes:
        for subset in itertools.combinations(range(n), k):
            yield list(subset)


def main():
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent
    out.mkdir(parents=True, exist_ok=True)
    check_b11()

    lines = [
        "# Known-answer vectors for the Merkle tree of draft Section 4.1,"
        " Longfellow ZK stage 5.",
        "# Generated by gen_ligero_vectors.py (this directory); do not"
        " edit by hand.",
        "#",
        "# Digests as 64 hex digits in memory order. Lines:",
        "#   build <n> <n leaves> <root>",
        "#       the heap of the leaves has this root (4.1.2)",
        "#   verify <n> <root> <k> <k indices> <k leaves> <m> <m path"
        " digests> <ok>",
        "#       batch verification (4.1.4) succeeds (1) or fails (0)",
        "#",
        "# Section A: Appendix B.1.1, copied from the draft and recomputed",
        "#   by the generator: the five leaves, the root, the proofs for",
        "#   leaves (0, 1) and (1, 3).",
    ]
    leaves = [bytes.fromhex(h) for h in B11_LEAVES]
    root = bytes.fromhex(B11_ROOT)
    lines.append("build 5 %s %s" % (" ".join(B11_LEAVES), B11_ROOT))
    for idx, proof in B11_PROOFS.items():
        lines.append(verify_line(5, root, list(idx), [leaves[i] for i in idx],
                                 [bytes.fromhex(h) for h in proof], True))
    lines.append("#")
    lines.append("# Section B: trees of 1 to 9 leaves (leaf i = SHA-256 of"
                 " \"leaf i\"),")
    lines.append("#   batch openings of every non-empty subset up to 5"
                 " leaves and of the")
    lines.append("#   subsets of size 1, 2, 3 and n beyond, from the"
                 " opening of 4.1.3.")
    n_build = n_verify = 0
    trees = {}
    for n in range(1, 10):
        lv = [sha256(("leaf %d" % i).encode()) for i in range(n)]
        layers = merkle_heap(lv)
        trees[n] = (lv, layers)
        lines.append("build %d %s %s" % (n, " ".join(hx(l) for l in lv),
                                         hx(layers[1])))
        n_build += 1
        for subset in tier2_subsets(n):
            path = merkle_open(layers, n, subset)
            if not merkle_verify(n, layers[1], subset,
                                 [lv[i] for i in subset], path):
                fail("tree of %d, subset %s does not verify" % (n, subset))
            lines.append(verify_line(n, layers[1], subset,
                                     [lv[i] for i in subset], path, True))
            n_verify += 1
    lines.append("#")
    lines.append("# Section C: negative cases on the tree of 7 leaves, subset"
                 " (1, 4, 6):")
    lines.append("#   an altered path digest, a path one digest too long, one"
                 " too short,")
    lines.append("#   a duplicate index, an index at n, no index, an altered"
                 " leaf, an")
    lines.append("#   altered root; each must fail.")
    lv, layers = trees[7]
    root = layers[1]
    subset = [1, 4, 6]
    path = merkle_open(layers, 7, subset)
    sub_leaves = [lv[i] for i in subset]
    altered = bytes([path[0][0] ^ 1]) + path[0][1:]
    cases = [
        (7, root, subset, sub_leaves, [altered] + path[1:]),
        (7, root, subset, sub_leaves, path + [path[0]]),
        (7, root, subset, sub_leaves, path[:-1]),
        (7, root, [1, 4, 4], [lv[1], lv[4], lv[4]],
         merkle_open(layers, 7, [1, 4])),
        (7, root, [1, 7], [lv[1], lv[0]], merkle_open(layers, 7, [1])),
        (7, root, [], [], []),
        (7, root, subset, [lv[1], lv[5], lv[6]], path),
        (7, bytes([root[0] ^ 1]) + root[1:], subset, sub_leaves, path),
    ]
    for n, r, idx, lvs, p in cases:
        if merkle_verify(n, r, idx, lvs, p):
            fail("negative case %s verifies" % (idx,))
        lines.append(verify_line(n, r, idx, lvs, p, False))
    (out / "merkle.txt").write_text("\n".join(lines) + "\n")
    print("gen_ligero_vectors: merkle.txt with %d build, %d verify and %d"
          " negative cases; B.1.1 reproduced" % (n_build + 1, n_verify + 2,
                                                 len(cases)))

    # ---- geometry
    check_geometry()
    glines = [
        "# Known-answer vectors for the Ligero geometry of draft Section 4.2,",
        "# Longfellow ZK stage 5. Generated by gen_ligero_vectors.py; do not"
        " edit by hand.",
        "# LigeroGeometry::new of the reference transcribed; the first case is",
        "# the configuration of Appendix B.3 with the numbers the draft prints.",
        "# Format: geometry <rate_inv> <nreq> <ncol> <nw> <nq> <valid>",
        "#   then, when valid is 1: <block> <dblock> <wr> <nwrow> <nqt> <nrow>",
        "#",
    ]
    for rate_inv, nreq, ncol, nw, nq in GEOMETRY_CASES:
        g = geometry(rate_inv, nreq, ncol, nw, nq)
        if g is None:
            glines.append("geometry %d %d %d %d %d 0" % (rate_inv, nreq, ncol,
                                                         nw, nq))
        else:
            glines.append("geometry %d %d %d %d %d 1 %d %d %d %d %d %d"
                          % (rate_inv, nreq, ncol, nw, nq, g["block"],
                             g["dblock"], g["wr"], g["nwrow"], g["nqt"],
                             g["nrow"]))
    (out / "ligero_geometry.txt").write_text("\n".join(glines) + "\n")
    print("gen_ligero_vectors: ligero_geometry.txt with %d cases; B.3.2"
          " geometry reproduced" % len(GEOMETRY_CASES))

    # ---- Lagrange
    rng = random.Random(20261015)
    for fld in (GF2128(), P256()):
        llines = [
            "# Known-answer vectors for the Lagrange code of ADR 0036 over "
            + fld.name + ",",
            "# Longfellow ZK stage 5. Generated by gen_ligero_vectors.py; do"
            " not edit by hand.",
            "# lagrange_matrix and encode_row of the reference transcribed,"
            " checked",
            "# against the interpolating polynomial found independently"
            " (Vandermonde).",
            "# Elements as big-endian hex integers (the notation of the other"
            " files),",
            "# columns as decimal positions x of the code of length n.",
            "# Format:",
            "#   table <k> <m> <m columns> <k inv_d> <k*m entries, row i then"
            " column c>",
            "#   eval <k> <m> <m columns> <k coeffs> <c> <encode_row at column"
            " c>",
            "#",
        ] + lagrange_lines(fld, rng)
        (out / ("lagrange_%s.txt" % fld.name)).write_text(
            "\n".join(llines) + "\n")
        print("gen_ligero_vectors: lagrange_%s.txt with %d cases; interpolation"
              " checked" % (fld.name, len(LAGRANGE_CASES) * 5))

    # ---- the reader
    rlines = [
        "# Known-answer vectors for the Ligero proof reader of draft Section",
        "# 7.4, Longfellow ZK stage 5. Generated by gen_ligero_vectors.py; do",
        "# not edit by hand. write_ligero_proof of the reference transcribed",
        "# on a small geometry, with the rules of the section violated one at",
        "# a time (ADR 0039, 0040). Bytes and digests as hex in memory order,",
        "# elements as big-endian hex integers after a field line.",
        "# Format:",
        "#   read <rate_inv> <nreq> <ncol> <nw> <nq> <status> <bytes>",
        "#        [<n> <n elements> <nreq nonces> <m> <m path digests>]",
        "#   status ok: the reader accepts, consumes every byte and gives the",
        "#   polynomials then the opened columns (n elements), the nonces and",
        "#   the path; status encoding: Proof_Encoding.",
        "#",
    ]
    n_read = 0
    for fld in (GF2128(), P256()):
        fl = reader_lines(fld, rng)
        rlines += fl
        n_read += sum(1 for l in fl if l.startswith("read "))
    (out / "ligero_proof.txt").write_text("\n".join(rlines) + "\n")
    print("gen_ligero_vectors: ligero_proof.txt with %d reader cases" % n_read)


if __name__ == "__main__":
    main()
