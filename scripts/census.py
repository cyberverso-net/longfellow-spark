#!/usr/bin/env python3
"""The facts of a circuit as the checker computes them, by an independent
program (ADR 0093).

The circuit checker walks a circuit from its inputs to its outputs and
gives every wire a meaning over declared variables. This script does
the same computation in Python, through the Python reader of the vector
generators (tests/vectors/gen_circuit_vectors.py) rather than the SPARK
reader, so that the two can be compared on the registered circuits: the
counts by kind and shape, and a digest of every fact. It is not a proof;
it is a second computation.

The model (ADR 0093):

- input wire i is the declared variable i; variable 0 is input wire 0,
  read as one;
- layer by layer from the inputs, the terms of a layer are taken in file
  order; a term k * w(h1) * w(h0) with k /= 0 adds the expansion of
  k * meaning(h1) * meaning(h0) into the slots of its wire g, one slot
  per monomial of degree at most 2 (variable 0 standing for one); a term
  with k = 0 is an assertion, whose fact is the pair of meanings;
- at the end of the layer, wire by wire in order, the wire's polynomial Q
  is its slots with their collected coefficients, in the order their
  monomials first appear; a slot whose coefficient is zero is kept, so
  that the kind does not depend on comparing field elements: the wire is
  linear when every slot has degree at most 1 and they name at most
  Max_Form variables besides the constant (its meaning is Q), declared
  otherwise (it becomes the next variable, its meaning is that variable,
  its fact is d = Q);
- the outputs of layer 0 have the fact "meaning = 0".

The facts, in the order of the walk (for each layer from the last: its
assertions in term order, then its declared wires in wire order; then
the outputs in wire order), are written to a byte string and digested
with SHA-256:

- an assertion: b"A", then the two meanings, of h1 and of h0;
- a declared wire: b"D", its variable, the number of its slots, then
  its slots in order: a, b and the coefficient;
- an output: b"O", its wire, then its meaning;
- a meaning: the number of its entries, then its entries in order: the
  variable, then the coefficient;
- a variable or wire: 4 bytes little-endian; a coefficient: the field's
  bytes as in the circuit file.

It also prints the limits the checker's contract bounds: the variables,
the terms of one wire, the slots of one wire and of one layer, and the
pairs of one term's expansion.

With --certificate, it also writes the certificate the walk expects
(Circuit_Certificates): for each layer, each wire's slot count and, for
every pair, the slot its monomial took, the gadget instances left 0. It
is a test vehicle for the checker on the registered circuits, not the
certificate of block 4, which the instrumented generator emits with the
gadget instances.

Run from the repository root:
  python3 -I scripts/census.py CIRCUIT.lfc2 gf2_128|p256 [--json OUT]
                               [--certificate OUT]
Exit status 0, or 2 when the file is refused by the reader.
"""

import argparse
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

VEC = Path(__file__).resolve().parent.parent / "tests" / "vectors"
sys.path.insert(0, str(VEC))
import gen_circuit_vectors as cv  # noqa: E402

MAX_FORM = {"gf2_128": 3, "p256": 2}


def u32(n):
    return n.to_bytes(4, "little")


def census(data, field):
    fld = cv.FIELDS[field]
    F = fld["F"]
    st, circ, _, ident = cv.read_lfc2(fld, data)
    if st != "ok":
        return st, None
    max_form = MAX_FORM[field]
    one = 1

    def mul(a, b):
        if a == one:
            return b
        if b == one:
            return a
        return F.mul(a, b)

    def form_bytes(m):
        return u32(len(m)) + b"".join(
            u32(v) + cv.elt_bytes(fld, c) for v, c in m.items())

    layers = circ["layers"]
    ninput = circ["ninput"]
    cert = [b"LFCK", cv.uleb(1), ident, cv.uleb(len(layers))]
    prev = [{0: one}] + [{i: one} for i in range(1, ninput)]
    nvar = ninput
    out = hashlib.sha256()
    kinds = Counter()
    shapes = Counter()
    lim = Counter()
    for j in range(len(layers) - 1, -1, -1):
        _, _, terms = layers[j]
        nv = circ["noutput"] if j == 0 else layers[j - 1][1]
        slots = [dict() for _ in range(nv)]
        nterms = [0] * nv
        hints = []
        for g, h0, h1, k in terms:
            a, b = prev[h1], prev[h0]
            lim["pairs_per_term"] = max(lim["pairs_per_term"], len(a) * len(b))
            if k == 0:
                out.update(b"A" + form_bytes(a) + form_bytes(b))
                kinds["assertion"] += 1
                continue
            nterms[g] += 1
            s = slots[g]
            for va, ca in a.items():
                kca = mul(k, ca)
                for vb, cb in b.items():
                    key = (va, vb) if va <= vb else (vb, va)
                    if key not in s:
                        s[key] = 0
                    hints.append(list(s).index(key))
                    s[key] = F.add(s[key], mul(kca, cb))
        lim["slots_per_layer"] = max(lim["slots_per_layer"], sum(len(s) for s in slots))
        cert.append(cv.uleb(nv) + cv.uleb(len(hints)))
        cert.append(b"".join(cv.uleb(len(slots[g])) + cv.uleb(0) for g in range(nv)))
        cert.append(b"".join(cv.uleb(h) for h in hints))
        cur = [None] * nv
        for g in range(nv):
            lim["terms_per_wire"] = max(lim["terms_per_wire"], nterms[g])
            lim["slots_per_wire"] = max(lim["slots_per_wire"], len(slots[g]))
            q = slots[g]
            deg2 = [kk for kk in q if kk[0] != 0]
            nvars = len({kk[1] for kk in q if kk[1] != 0}) if not deg2 else None
            if not deg2 and nvars <= max_form:
                kinds["linear"] += 1
                cur[g] = {kk[1]: c for kk, c in q.items()}
            else:
                kinds["declared"] += 1
                shapes[(len(deg2), len({v for kk in q for v in kk if v}), len(q))] += 1
                out.update(b"D" + u32(nvar) + u32(len(q)) + b"".join(
                    u32(a) + u32(b) + cv.elt_bytes(fld, c) for (a, b), c in q.items()))
                cur[g] = {nvar: one}
                nvar += 1
        if j == 0:
            for g in range(nv):
                out.update(b"O" + u32(g) + form_bytes(cur[g]))
        prev = cur
    lim["variables"] = nvar
    res = {
        "field": field,
        "wires": sum(kinds[k] for k in ("linear", "declared")),
        "kinds": dict(kinds),
        "limits": dict(lim),
        "shapes": sorted([[a, b, c, n] for (a, b, c), n in shapes.items()],
                         key=lambda x: -x[3]),
        "facts_sha256": out.hexdigest(),
        "certificate": b"".join(cert),
    }
    return "ok", res


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("circuit")
    ap.add_argument("field", choices=sorted(MAX_FORM))
    ap.add_argument("--json")
    ap.add_argument("--certificate")
    args = ap.parse_args()
    st, res = census(Path(args.circuit).read_bytes(), args.field)
    if st != "ok":
        print("census: the reader refuses the file: %s" % st, file=sys.stderr)
        return 2
    print("census: %s, %d wires: %s" % (res["field"], res["wires"], res["kinds"]))
    print("census: limits %s" % res["limits"])
    print("census: facts %s" % res["facts_sha256"])
    certificate = res.pop("certificate")
    if args.certificate:
        Path(args.certificate).write_bytes(certificate)
    if args.json:
        Path(args.json).write_text(json.dumps(res, indent=1, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
