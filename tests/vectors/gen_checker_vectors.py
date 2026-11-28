#!/usr/bin/env python3
"""The vectors of the circuit checker's harness (ADR 0093, ADR 0094): small
circuits written by hand, their honest certificates, and one hostile
certificate for each check of Circuit_Checker.Accepts and each status of
the certificate's reader, with the outcome each must give.

The honest certificate and the digest of each circuit's facts come from
scripts/census.py, the independent computation of the checker's model.
Every certificate is rebuilt here from its structure (the slot counts of
each layer), and the honest one is required to equal census.py's byte for
byte; a hostile one changes one thing in that structure.

The capacities (Pool_Full, Too_Many_Slots, Too_Many_Terms, Too_Many_Vars)
are reached on small instances of the checker that the harness declares,
each with one limit low and the others as the registered instance's.

Output: checker.txt in this directory (or the directory given), one case
per line:
  field gf2_128
  circuit <name> <lfc2 hex>
  facts <name> <sha256 hex>        the census digest of the circuit's facts
  cert <case> <circuit> <instance> <outcome> <status> <lfck hex>
      instance: gf2_128 (the registered limits) or one of the small ones;
      outcome: the lower-case values of Circuit_Check.Outcome; status: the
      lower-case status of the step that refused (the certificate
      reader's or the walk's), or - when there is none

Run from the repository root:
  python3 -I tests/vectors/gen_checker_vectors.py [OUT_DIR]
"""

import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import gen_circuit_vectors as cv  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    "census", ROOT / "scripts" / "census.py")
census = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(census)

FIELD = "gf2_128"
FLD = cv.FIELDS[FIELD]


def fail(msg):
    sys.exit(f"gen_checker_vectors: {msg}")


# ------------------------------------------------------- certificates

def parse_cert(data):
    """(identifier, layers): the inverse of cert_bytes, for honest
    certificates only; a layer is the list of its wires' slot counts."""
    if data[:4] != b"LFCK":
        fail("census certificate: magic")
    pos = 4

    def nxt():
        nonlocal pos
        v, shift = 0, 0
        while True:
            b = data[pos]
            pos += 1
            v |= (b & 0x7F) << shift
            shift += 7
            if b < 0x80:
                return v

    if nxt() != 2:
        fail("census certificate: version")
    ident = data[pos:pos + 32]
    pos += 32
    layers = []
    for _ in range(nxt()):
        layers.append([nxt() for _ in range(nxt())])
    if pos != len(data):
        fail("census certificate: trailing bytes")
    return ident, layers


def cert_bytes(ident, layers, version=2):
    out = bytearray(b"LFCK") + cv.uleb(version) + ident + cv.uleb(len(layers))
    for counts in layers:
        out += cv.uleb(len(counts))
        for c in counts:
            out += cv.uleb(c)
    return bytes(out)


def with_layer(layers, i, counts):
    """The layers with the walk's layer i (0: the last circuit layer)
    replaced."""
    out = [list(c) for c in layers]
    out[i] = counts
    return out


# ----------------------------------------------------------- circuits

F = FLD["F"]


def circuit(ninput, noutput, layers):
    """layers from layer 0 (the outputs) to the last (reading the
    inputs): (number of wires the layer reads, terms (g, h0, h1, k))."""
    out = []
    for nw, terms in layers:
        logw = max(1, (nw - 1).bit_length())
        out.append((logw, nw, terms))
    return {"noutput": noutput, "ninput": ninput, "npublic": 0,
            "layers": out}


def c1(k=3):
    """Four inputs (wire 0 is one, then x1, x2, x3).
    Layer 1, reading the inputs:
      w0 = 1 * 1 * 1            linear: the constant, for layer 0
      w1 = x1 * x2              degree 2: declared, variable 4
      w2 = x1 + x2 + 7 x1       linear, the monomial x1 twice: 6 x1 + x2
      w3 = k x3                 linear
      w4 = 0 * x1 * x3          an assertion: x1 x3 = 0
    Layer 0, the outputs (w4, an assertion's wire, is not read):
      o0 = w1 * w2              degree 2: declared, variable 5
      o1 = w2 + w3 + 5          linear, with the constant: four slots
    Terms are (g, h0, h1, k), the term k * w(h1) * w(h0)."""
    layer1 = [(0, 0, 0, 1),
              (1, 2, 1, 1),
              (2, 0, 1, 1), (2, 0, 2, 1), (2, 0, 1, 7),
              (3, 0, 3, k),
              (4, 3, 1, 0)]
    layer0 = [(0, 2, 1, 1),
              (1, 0, 2, 1), (1, 0, 3, 1), (1, 0, 0, 5)]
    return circuit(4, 2, [(5, layer0), (4, layer1)])


def lfc2(circ):
    data = cv.write_lfc2(FLD, circ)
    st, _, _, _ = cv.read_lfc2(FLD, data)
    if st != "ok":
        fail(f"a hand-written circuit is refused: {st}")
    return data


def honest(data):
    st, res = census.census(data, FIELD)
    if st != "ok":
        fail(f"census: {st}")
    ident, layers = parse_cert(res["certificate"])
    if cert_bytes(ident, layers) != res["certificate"]:
        fail("the certificate rebuilt differs from census.py's")
    return ident, layers, res["facts_sha256"]


# --------------------------------------------------------------- main

def main():
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE
    lines = [
        "# The circuit checker's harness (ADR 0093): hand-written circuits,",
        "# their honest certificates, and one hostile certificate per check",
        "# of Accepts and per status of the certificate reader.",
        "# Generated by gen_checker_vectors.py (this directory); do not edit.",
        f"field {FIELD}",
    ]
    emit = lines.append
    cases = []

    def case(name, circ, inst, outcome, status, data):
        cases.append(f"cert {name} {circ} {inst} {outcome} {status} "
                     f"{data.hex()}")

    # The circuit, and paragraph D of the record: one constant changed.
    a = lfc2(c1())
    b = lfc2(c1(k=9))
    ia, la, fa = honest(a)
    ib, lb, fb = honest(b)
    if la != lb:
        fail("paragraph D: the counts of the changed circuit differ")
    if fa == fb:
        fail("paragraph D: the facts of the changed circuit are the same")
    emit(f"circuit c1 {a.hex()}")
    emit(f"facts c1 {fa}")
    emit(f"circuit c1_k {b.hex()}")
    emit(f"facts c1_k {fb}")

    # The walk's layers: 0 is circuit layer 1 (reading the inputs), 1 is
    # layer 0. Circuit layer 1: counts w0 1, w1 1, w2 2 (its third pair,
    # x1 again, finds the slot of its first), w3 1, w4 0. Layer 0: o0 2
    # slots, o1 4.
    c_l1 = la[0]
    c_l0 = la[1]
    if c_l1 != [1, 1, 2, 1, 0]:
        fail(f"c1 layer 1 is not as written: {la[0]}")
    if c_l0 != [2, 4]:
        fail(f"c1 layer 0 is not as written: {la[1]}")

    ok = cert_bytes(ia, la)
    case("honest", "c1", "gf2_128", "accepted", "-", ok)
    case("honest_k", "c1_k", "gf2_128", "accepted", "-", cert_bytes(ib, lb))

    def walk(name, layers, status, inst="gf2_128"):
        case(name, "c1", inst, "walk_refused", status, cert_bytes(ia, layers))

    # One certificate per check of Accepts.
    walk("one_layer_fewer", la[:1], "cert_mismatch")
    walk("one_wire_fewer", with_layer(la, 0, c_l1[:4]), "cert_mismatch")
    # w2's count one below the true one: its second monomial takes a slot
    # beyond the count.
    walk("count_below", with_layer(la, 0, [1, 1, 1, 1, 0]), "count_exceeded")
    # w3's count one above: a slot no pair reaches.
    walk("count_above", with_layer(la, 0, [1, 1, 2, 2, 0]), "empty_slot")
    # The capacities, each on a small instance with that limit low.
    walk("over_terms", la, "too_many_terms", inst="small_terms")
    walk("over_slots", la, "too_many_slots", inst="small_slots")
    walk("over_pool", la, "pool_full", inst="small_pool")
    walk("over_vars", la, "too_many_vars", inst="small_vars")
    walk("over_inputs", la, "too_many_vars", inst="small_inputs")

    # The driver: a certificate for another circuit.
    wrong = bytearray(ok)
    wrong[5] ^= 1
    case("wrong_circuit", "c1", "gf2_128", "wrong_circuit", "-",
         bytes(wrong))

    # The reader, one case per status.
    def reader(name, data, status):
        case(name, "c1", "gf2_128", "certificate_refused", status, data)

    reader("bad_magic", b"LFCX" + ok[4:], "bad_magic")
    reader("bad_version", ok[:4] + cv.uleb(1) + ok[5:], "bad_version")
    reader("truncated", ok[:-1], "truncated")
    reader("bad_integer",
           ok[:37] + bytes([0x82, 0x80, 0x80, 0x80, 0x00]) + ok[38:],
           "bad_integer")
    reader("bound_exceeded",
           cert_bytes(ia, with_layer(la, 0, [1, 1, 70000, 1, 0])),
           "bound_exceeded")
    reader("trailing", ok + b"\x00", "trailing")

    lines += cases
    (out_dir / "checker.txt").write_text("\n".join(lines) + "\n")


if __name__ == "__main__":
    main()
