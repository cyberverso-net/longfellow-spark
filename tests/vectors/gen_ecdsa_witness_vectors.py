#!/usr/bin/env python3
"""Generator for the curve and ECDSA witness vectors (Phase D, block 6,
ADR 0086):
  ecdsa_witness.txt
    add <x1> <y1> <z1> <x2> <y2> <z2> <x3> <y3> <z3>
        the complete projective addition of upstream's core/algebra/src/ec.rs
        (P256_Curve.Add); the point at infinity is (0, 1, 0);
    double <x> <y> <z> <x3> <y3> <z3>
        the doubling (P256_Curve.Double);
    affine <x> <y> <z> <ax> <ay>
        (x / z, y / z) (P256_Curve.Affine);
    scalar <k> <px> <py> <rx> <ry>
        the affine result of k (px, py, 1) (P256_Curve.Scalar_Mul, then Affine);
    witness <name> <pkx> <pky> <e> <r> <s> <digest>
        the 1,034 elements of push_legacy_verify_witness_3 (runtime/src/concrete/
        legacy/private.rs) for the signature (r, s) on the digest e under the key
        (pkx, pky), as the SHA-256 of their 32-byte little-endian canonical
        encodings in order (Ecdsa_Witness.Push_Legacy);
    witness_reject <name> <s>
        a signature value s at or above q, which Push_Legacy's precondition refuses
        (Q256_Field.Is_Canonical false), as upstream's builder stops on it;
    witness_file <name> <archive> <first> <pkx> <pky> <e> <r> <s>
        the same witness, equal element by element to the signature witness
        file <archive>_sig_witness.bin of upstream/mdoc/ from its element <first>
        (32-byte little-endian elements; the 900 public inputs come first, then
        the three reduced values, then the issuer's witness at 903 and the
        device's at 1,937); the generator checks the identity itself and fails
        otherwise.

Field elements and 256-bit integers are written as 64 hex digits, most
significant first; points as their coordinates in order.

Independent reference: plain Python integers, the formulas of ec.rs and
ecdsa2/concrete.rs transcribed (add, double, affine, scalar_mul, given,
derived). The real signatures are those of upstream's test document
FAMILYNAME_MUSTERMANN_MDOC_3 (upstream/mdoc/testcases/), from which the two
witness files of each archive were made: the issuer's signature on the MSO
(the digest is the SHA-256 of the COSE Sign1 message, cbor/mdoc.rs
format_cose_sign1_message) and the device's signature on the session
transcript (the digest is compute_transcript_hash). The document is parsed
here with a minimal CBOR reader, enough for the two COSE_Sign1 structures
and the device key; block 6b brings the full parse.

External anchors: RFC 5903 Section 8.1 (the key pairs i, g^i and r, g^r of
the 256-bit example), checked by the generator's own scalar multiplication
and written as scalar cases; the group order q G = O.

Usage: python3 -I gen_ecdsa_witness_vectors.py [output-directory]
Output is deterministic (fixed seed, no timestamps).
"""

import hashlib
import random
import sys
from pathlib import Path

HERE = Path(__file__).parent
MDOC_DIR = HERE / "upstream" / "mdoc"
CASE = "FAMILYNAME_MUSTERMANN_MDOC_3"
ARCHIVES = ("8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121",
            "137e5a75ce72735a37c8a72da1a8a0a5df8d13365c2ae3d2c2bd6a0e7197c7c6")

P = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
Q = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
A = P - 3
B = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
GX = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
GY = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5

# RFC 5903 Section 8.1, the 256-bit example (spaces removed).
RFC5903_I = 0xC88F01F510D9AC3F70A292DAA2316DE544E9AAB8AFE84049C62A9C57862D1433
RFC5903_GIX = 0xDAD0B65394221CF9B051E1FECA5787D098DFE637FC90B9EF945D0C3772581180
RFC5903_GIY = 0x5271A0461CDB8252D61F1C456FA3E59AB1F45B33ACCF5F58389E0577B8990BB3
RFC5903_R = 0xC6EF9C5D78AE012A011164ACB397CE2088685D8F06BF9BE0B283AB46476BEE53
RFC5903_GRX = 0xD12DFB5289C8D4F81208B70270398C342296970A0BCCB74C736FC7554494BF63
RFC5903_GRY = 0x56FBF3CA366CC23E8157854C13C58D6AAC23F046ADA30F8353E74F33039872AB

SEED = 20261108


def fail(msg):
    print(f"gen_ecdsa_witness_vectors: FAILED: {msg}", file=sys.stderr)
    sys.exit(1)


def hx(v):
    assert 0 <= v < 2**256
    return f"{v:064x}"


def inv(x, m):
    return pow(x, m - 2, m)


def fa(x, y): return (x + y) % P
def fs(x, y): return (x - y) % P
def fm(x, y): return (x * y) % P


# ---- core/algebra/src/ec.rs ------------------------------------------------
def zero():
    return (0, 1, 0)


def projective(pt):
    return (pt[0], pt[1], 1)


def affine(pt):
    x, y, z = pt
    zi = inv(z, P)
    return (fm(x, zi), fm(y, zi))


def add(p1, p2):
    k3b = fa(B, fa(B, B))
    x1, y1, z1 = p1
    x2, y2, z2 = p2
    t0 = fm(x1, x2); t1 = fm(y1, y2); t2 = fm(z1, z2)
    t3 = fs(fm(fa(x1, y1), fa(x2, y2)), fa(t0, t1))
    t4 = fs(fm(fa(x1, z1), fa(x2, z2)), fa(t0, t2))
    t5 = fs(fm(fa(y1, z1), fa(y2, z2)), fa(t1, t2))
    z3 = fa(fm(k3b, t2), fm(A, t4))
    x3 = fs(t1, z3); z3 = fa(t1, z3); y3 = fm(x3, z3)
    t1 = fa(fa(t0, t0), t0); t2 = fm(A, t2)
    t4 = fm(k3b, t4); t1 = fa(t1, t2); t2 = fm(A, fs(t0, t2))
    t4 = fa(t4, t2); t0 = fm(t1, t4); y3 = fa(y3, t0)
    t0 = fm(t5, t4); x3 = fs(fm(t3, x3), t0)
    t0 = fm(t3, t1); z3 = fa(fm(t5, z3), t0)
    return (x3, y3, z3)


def double(pt):
    k3b = fa(B, fa(B, B))
    x, y, z = pt
    t0 = fm(x, x); t1 = fm(y, y); t2 = fm(z, z)
    t3 = fm(x, y); t3 = fa(t3, t3)
    z3 = fm(x, z); z3 = fa(z3, z3)
    y3 = fa(fm(A, z3), fm(k3b, t2))
    x3 = fs(t1, y3); y3 = fa(t1, y3); y3 = fm(x3, y3)
    x3 = fm(t3, x3); z3 = fm(k3b, z3); t2 = fm(A, t2)
    t3 = fa(fm(A, fs(t0, t2)), z3)
    t0 = fa(fa(fa(t0, t0), t0), t2); t0 = fm(t0, t3)
    y3 = fa(y3, t0); t2 = fm(y, z); t2 = fa(t2, t2)
    x3 = fs(x3, fm(t2, t3))
    z3 = fm(t2, t1); z3 = fa(z3, z3); z3 = fa(z3, z3)
    return (x3, y3, z3)


def scalar_mul(k, pt):
    res = zero(); tmp = pt
    for i in range(256):
        if (k >> i) & 1:
            res = add(res, tmp)
        tmp = double(tmp)
    return res


def on_curve(pt):
    x, y = affine(pt) if len(pt) == 3 else pt
    return (y * y - (x * x * x + A * x + B)) % P == 0


# ---- circuits/ecdsa2/src/concrete.rs, legacy push ---------------------------
def legacy_witness(pk, e, r, s):
    s_inv = inv(s % Q, Q)
    nes = ((e % Q) * s_inv) % Q
    nrs = ((r % Q) * s_inv) % Q
    g = projective((GX, GY)); pkp = projective(pk)
    rproj = add(scalar_mul(nes, g), scalar_mul(nrs, pkp))
    rx = r % P
    ry = fm(rproj[1], inv(rproj[2], P))
    r_pt = (rx, ry, 1)
    g_pk = affine(add(g, pkp)); g_r = affine(add(g, r_pt)); pk_r = affine(add(pkp, r_pt))
    g_pk_r = affine(add(g, projective(pk_r)))
    nms = (-s) % Q
    opts = [zero(), r_pt, pkp, projective(pk_r), g, projective(g_r), projective(g_pk), projective(g_pk_r)]
    rounds = [None] * 256
    p = zero()
    for i in range(255, -1, -1):
        idx = ((e >> i) & 1) * 4 + ((r >> i) & 1) * 2 + ((nms >> i) & 1)
        p = add(double(p), opts[idx])
        rounds[i] = p
    out = [rx, ry, inv(rx, P), inv(nms % P, P), inv(pk[0], P),
           g_pk[0], g_pk[1], g_r[0], g_r[1], pk_r[0], pk_r[1], g_pk_r[0], g_pk_r[1]]
    for i in range(256):
        bit = 255 - i
        b = ((e >> bit) & 1) + 2 * ((r >> bit) & 1) + 4 * ((nms >> bit) & 1)
        out.append((2 * b - 7) % P)
        if i < 255:
            out += list(rounds[255 - i])
    assert len(out) == 1034
    return out


def digest_of(elements):
    h = hashlib.sha256()
    for v in elements:
        h.update(v.to_bytes(32, "little"))
    return h.hexdigest()


# ---- a minimal CBOR reader for the two COSE_Sign1 structures ----------------
def cbor(data, off=0):
    start = off
    ib = data[off]; off += 1
    major, info = ib >> 5, ib & 31
    if info < 24:
        val = info
    elif info == 24:
        val = data[off]; off += 1
    elif info == 25:
        val = int.from_bytes(data[off:off + 2], "big"); off += 2
    elif info == 26:
        val = int.from_bytes(data[off:off + 4], "big"); off += 4
    elif info == 27:
        val = int.from_bytes(data[off:off + 8], "big"); off += 8
    else:
        fail("indefinite length in the test document")
    if major == 0:
        return (val, start, off)
    if major == 1:
        return (-1 - val, start, off)
    if major == 2:
        return (bytes(data[off:off + val]), start, off + val)
    if major == 3:
        return (data[off:off + val].decode(), start, off + val)
    if major == 4:
        arr = []
        for _ in range(val):
            el = cbor(data, off); arr.append(el); off = el[2]
        return (arr, start, off)
    if major == 5:
        pairs = []
        for _ in range(val):
            k = cbor(data, off); v = cbor(data, k[2]); pairs.append((k, v)); off = v[2]
        return (pairs, start, off)
    if major == 6:
        inner = cbor(data, off)
        return (("tag", val, inner), start, inner[2])
    return (("simple", val), start, off)


def mapv(m, key):
    for k, v in m[0]:
        if k[0] == key:
            return v
    fail(f"key {key!r} missing in the test document")


def untag(el):
    return el[0][2] if isinstance(el[0], tuple) and el[0][0] == "tag" else el


COSE1 = bytes([0x84, 0x6A]) + b"Signature1" + bytes([0x43, 0xA1, 0x01, 0x26, 0x40])


def bytes_head(n):
    if n < 24:
        return bytes([0x40 | n])
    if n < 256:
        return bytes([0x58, n])
    if n < 65536:
        return bytes([0x59]) + n.to_bytes(2, "big")
    return bytes([0x5A]) + n.to_bytes(4, "big")


def text_head(n):
    h = bytes_head(n)
    return bytes([h[0] | 0x20]) + h[1:]


def load_case():
    d = MDOC_DIR / "testcases" / CASE
    mdoc = (d / "mdoc.bin").read_bytes()
    transcript = (d / "transcript.bin").read_bytes()
    req = dict(line.split(" ", 1) for line in (d / "request.txt").read_text().splitlines() if line)
    pk = (int(req["pkx"], 16), int(req["pky"], 16))
    root = cbor(mdoc)
    doc0 = mapv(root, "documents")[0][0]
    issuer_signed = mapv(doc0, "issuerSigned")
    issuer_auth = untag(mapv(issuer_signed, "issuerAuth"))
    mso_wrapped = issuer_auth[0][2][0]
    sig = issuer_auth[0][3][0]
    if len(sig) != 64:
        fail("issuer signature length")
    issuer_r, issuer_s = int.from_bytes(sig[:32], "big"), int.from_bytes(sig[32:], "big")
    msg = COSE1 + bytes_head(len(mso_wrapped)) + mso_wrapped
    issuer_e = int.from_bytes(hashlib.sha256(msg).digest(), "big")
    mso_map = cbor(cbor(mso_wrapped)[0][2][0])
    dk = mapv(mapv(mso_map, "deviceKeyInfo"), "deviceKey")
    dpk = (int.from_bytes(mapv(dk, -2)[0], "big"), int.from_bytes(mapv(dk, -3)[0], "big"))
    dev_sig_el = untag(mapv(mapv(mapv(doc0, "deviceSigned"), "deviceAuth"), "deviceSignature"))
    dsig = dev_sig_el[0][3][0]
    if len(dsig) != 64:
        fail("device signature length")
    dev_r, dev_s = int.from_bytes(dsig[:32], "big"), int.from_bytes(dsig[32:], "big")
    da = (bytes([0x84, 0x74]) + b"DeviceAuthentication" + transcript
          + text_head(len(req["doc_type"])) + req["doc_type"].encode() + bytes([0xD8, 0x18, 0x41, 0xA0]))
    payload = bytes([0xD8, 0x18]) + bytes_head(len(da)) + da
    dev_e = int.from_bytes(hashlib.sha256(COSE1 + bytes_head(len(payload)) + payload).digest(), "big")
    if not on_curve(pk) or not on_curve(dpk):
        fail("a key of the test document is not on the curve")
    return pk, (issuer_e, issuer_r, issuer_s), dpk, (dev_e, dev_r, dev_s)


def verify_sig(pk, e, r, s):
    """Plain ECDSA verification, so that the generator does not trust the
    document blindly."""
    w = inv(s % Q, Q)
    u1, u2 = ((e % Q) * w) % Q, ((r % Q) * w) % Q
    x, _ = affine(add(scalar_mul(u1, projective((GX, GY))), scalar_mul(u2, projective(pk))))
    return x % Q == r % Q


def main():
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE
    rng = random.Random(SEED)
    g = projective((GX, GY))

    # ---- anchors
    if not on_curve((GX, GY)):
        fail("G is not on the curve")
    if affine(scalar_mul(RFC5903_I, g)) != (RFC5903_GIX, RFC5903_GIY):
        fail("RFC 5903 g^i")
    if affine(scalar_mul(RFC5903_R, g)) != (RFC5903_GRX, RFC5903_GRY):
        fail("RFC 5903 g^r")
    if scalar_mul(Q, g)[2] != 0:
        fail("q G is not the point at infinity")
    shared = affine(scalar_mul(RFC5903_I, projective((RFC5903_GRX, RFC5903_GRY))))
    if shared != affine(scalar_mul(RFC5903_R, projective((RFC5903_GIX, RFC5903_GIY)))):
        fail("RFC 5903 shared secret")

    lines = []
    w = lines.append
    w("# Known-answer vectors for P256_Curve and Ecdsa_Witness (block 6 of Phase D, ADR 0086).")
    w("# Generated by gen_ecdsa_witness_vectors.py (this directory); do not edit by hand.")
    w("# Formulas: upstream core/algebra/src/ec.rs (complete projective addition and")
    w("#   doubling, point at infinity (0, 1, 0)) and circuits/ecdsa2/src/concrete.rs")
    w("#   at d5e6be7. Values: 64 hex digits, most significant first.")
    w("#")
    w("# Section A: the group law on G and the RFC 5903 Section 8.1 points, the point")
    w("#   at infinity on both sides, doubling, affine conversion.")
    gi = projective((RFC5903_GIX, RFC5903_GIY)); gr = projective((RFC5903_GRX, RFC5903_GRY))
    pts = [g, gi, gr, zero(), double(g), add(g, gi), add(double(gi), gr)]
    for p1 in pts[:4]:
        for p2 in pts[:4]:
            r3 = add(p1, p2)
            w(f"add {hx(p1[0])} {hx(p1[1])} {hx(p1[2])} {hx(p2[0])} {hx(p2[1])} {hx(p2[2])} {hx(r3[0])} {hx(r3[1])} {hx(r3[2])}")
    for p1 in pts:
        d = double(p1)
        w(f"double {hx(p1[0])} {hx(p1[1])} {hx(p1[2])} {hx(d[0])} {hx(d[1])} {hx(d[2])}")
    for p1 in pts:
        if p1[2] != 0:
            ax, ay = affine(p1)
            w(f"affine {hx(p1[0])} {hx(p1[1])} {hx(p1[2])} {hx(ax)} {hx(ay)}")
    w(f"affine {hx(0)} {hx(1)} {hx(0)} {hx(0)} {hx(0)}")
    w("#")
    w("# Section B: scalar multiplication: the RFC 5903 key pairs (i, g^i), (r, g^r), the")
    w("#   shared secret from both sides, q - 1 (the negation of G), 0, 1, 2, and random scalars.")
    for k, pt in ((RFC5903_I, g), (RFC5903_R, g), (RFC5903_I, gr), (RFC5903_R, gi),
                  (Q - 1, g), (0, g), (1, g), (2, g), (2**255, g), (2**256 - 1, g)):
        res = scalar_mul(k, pt)
        ax, ay = affine(res) if res[2] != 0 else (0, 0)
        px, py = affine(pt)
        w(f"scalar {hx(k)} {hx(px)} {hx(py)} {hx(ax)} {hx(ay)}")
    for _ in range(8):
        k = rng.getrandbits(256)
        d = 1 + rng.getrandbits(256) % (Q - 1)
        pt = scalar_mul(d, g)
        res = scalar_mul(k, pt)
        ax, ay = affine(res) if res[2] != 0 else (0, 0)
        px, py = affine(pt)
        w(f"scalar {hx(k)} {hx(px)} {hx(py)} {hx(ax)} {hx(ay)}")
    w("#")
    w("# Section C: random projective points (random Z, not normalised) under add and double.")
    for _ in range(12):
        d1 = 1 + rng.getrandbits(256) % (Q - 1); d2 = 1 + rng.getrandbits(256) % (Q - 1)
        z1 = 1 + rng.getrandbits(256) % (P - 1); z2 = 1 + rng.getrandbits(256) % (P - 1)
        a1 = affine(scalar_mul(d1, g)); a2 = affine(scalar_mul(d2, g))
        p1 = (fm(a1[0], z1), fm(a1[1], z1), z1); p2 = (fm(a2[0], z2), fm(a2[1], z2), z2)
        r3 = add(p1, p2); d3 = double(p1)
        w(f"add {hx(p1[0])} {hx(p1[1])} {hx(p1[2])} {hx(p2[0])} {hx(p2[1])} {hx(p2[2])} {hx(r3[0])} {hx(r3[1])} {hx(r3[2])}")
        w(f"double {hx(p1[0])} {hx(p1[1])} {hx(p1[2])} {hx(d3[0])} {hx(d3[1])} {hx(d3[2])}")
    w("#")
    w("# Section D: the ECDSA witness on random valid signatures (key d, nonce k, digest e),")
    w("#   as the SHA-256 of the 1,034 elements' 32-byte little-endian encodings.")
    for i in range(6):
        d = 1 + rng.getrandbits(256) % (Q - 1)
        k = 1 + rng.getrandbits(256) % (Q - 1)
        e = rng.getrandbits(256)
        pk = affine(scalar_mul(d, g))
        r = affine(scalar_mul(k, g))[0] % Q
        s = (inv(k, Q) * ((e % Q) + r * d)) % Q
        if r == 0 or s == 0 or not verify_sig(pk, e, r, s):
            fail("random signature")
        wit = legacy_witness(pk, e, r, s)
        w(f"witness random{i} {hx(pk[0])} {hx(pk[1])} {hx(e)} {hx(r)} {hx(s)} {digest_of(wit)}")
    w("#")
    w("# Section E: the boundary of the scalar field: e and r at or above q and at 2^256 - 1,")
    w("#   which upstream reduces (e, r) while reading their raw bits for the digits and the")
    w("#   table; s at or above q, which upstream's builder refuses and Push_Legacy's")
    w("#   precondition excludes.")
    d = 1 + rng.getrandbits(256) % (Q - 1)
    pk = affine(scalar_mul(d, g))
    s_valid = 1 + rng.getrandbits(256) % (Q - 1)
    for i, (e, r) in enumerate(((Q, Q + 5), (Q + 1, 2**256 - 1), (2**256 - 1, Q), (Q - 1, Q - 1))):
        wit = legacy_witness(pk, e, r, s_valid)
        w(f"witness boundary{i} {hx(pk[0])} {hx(pk[1])} {hx(e)} {hx(r)} {hx(s_valid)} {digest_of(wit)}")
    for i, s_bad in enumerate((Q, Q + 1, 2**256 - 1)):
        w(f"witness_reject reject{i} {hx(s_bad)}")
    w("#")
    w("# Section F: the two signatures of upstream's test document FAMILYNAME_MUSTERMANN_MDOC_3")
    w("#   (upstream/mdoc/testcases/): the issuer's on the MSO and the device's on the session")
    w("#   transcript, equal to the signature witness files of both archives at the given")
    w("#   element (checked by the generator).")
    pk, issuer, dpk, device = load_case()
    for name, key, sig in (("issuer", pk, issuer), ("device", dpk, device)):
        e, r, s = sig
        if not verify_sig(key, e, r, s):
            fail(f"the {name} signature of the test document does not verify")
        wit = legacy_witness(key, e, r, s)
        w(f"witness {name} {hx(key[0])} {hx(key[1])} {hx(e)} {hx(r)} {hx(s)} {digest_of(wit)}")
        first = 903 if name == "issuer" else 903 + 1034
        for arch in ARCHIVES:
            data = (MDOC_DIR / f"{arch}_sig_witness.bin").read_bytes()
            els = [int.from_bytes(data[i:i + 32], "little") for i in range(0, len(data), 32)]
            if els[first:first + 1034] != wit:
                bad = next(i for i in range(1034) if els[first + i] != wit[i])
                fail(f"{name} witness differs from {arch[:8]} at element {first + bad}")
            w(f"witness_file {name} {arch} {first} {hx(key[0])} {hx(key[1])} {hx(e)} {hx(r)} {hx(s)}")
    (out_dir / "ecdsa_witness.txt").write_text("\n".join(lines) + "\n")
    n = sum(1 for l in lines if l and not l.startswith("#"))
    print(f"RFC 5903 key pairs verified; the two signatures of the test document verify and their"
          f" witnesses equal the files of both archives; wrote {out_dir / 'ecdsa_witness.txt'}: {n} cases")


if __name__ == "__main__":
    main()
