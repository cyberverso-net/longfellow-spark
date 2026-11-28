#!/usr/bin/env python3
"""Tests of census.py: small circuits over GF(2^128) whose facts are
written out here by hand, byte for byte, as the docstring of census.py
states them, and the certificate it writes for them. Each test names the
rule of ADR 0093 it holds census.py to.

Run: python3 -I scripts/census-test.py
"""

import hashlib
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
VEC = HERE.parent / "tests" / "vectors"
sys.path.insert(0, str(VEC))
import gen_circuit_vectors as cv  # noqa: E402

_spec = importlib.util.spec_from_file_location("census", HERE / "census.py")
census = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(census)

FLD = cv.FIELDS["gf2_128"]
failed = 0
passed = 0


def check(ok, what):
    global failed, passed
    if ok:
        passed += 1
    else:
        failed += 1
        print(f"FAIL: {what}")


def u32(n):
    return n.to_bytes(4, "little")


def elt(v):
    return v.to_bytes(16, "little")


def run(layers, ninput, noutput):
    """census of the circuit whose layers, from layer 0, are (number of
    wires read, terms (g, h0, h1, k))."""
    circ = {"noutput": noutput, "ninput": ninput, "npublic": 0,
            "layers": [(max(1, (nw - 1).bit_length()), nw, t)
                       for nw, t in layers]}
    data = cv.write_lfc2(FLD, circ)
    st, res = census.census(data, "gf2_128")
    if st != "ok":
        sys.exit(f"census-test: a test circuit is refused: {st}")
    return data, res


def digest(*parts):
    return hashlib.sha256(b"".join(parts)).hexdigest()


# 1. A declared wire and an output. Inputs: 1, x1, x2. One layer:
#    o0 = x1 * x2 + 3. Its slots, in the order their monomials first
#    appear: (1, 2) with 1, (0, 0) with 3. It has degree 2: declared,
#    variable 3, fact d3 = x1 x2 + 3; the output's meaning is d3.
data, res = run([(3, [(0, 2, 1, 1), (0, 0, 0, 3)])], 3, 1)
want = digest(b"D", u32(3), u32(2), u32(1), u32(2), elt(1), u32(0), u32(0),
              elt(3),
              b"O", u32(0), u32(1), u32(3), elt(1))
check(res["facts_sha256"] == want, "a declared wire: the facts' bytes")
check(res["kinds"] == {"declared": 1}, f"a declared wire: kinds {res['kinds']}")
check(res["limits"]["variables"] == 4, "a declared wire: four variables")

# 2. A linear wire, an assertion, the constant one carried by a wire.
#    Layer 1: w0 = 1 (the constant), w1 = x1 + 5 x2 (linear), w2 = 0 * x1
#    * x2 (an assertion: x1 x2 = 0). Layer 0: o0 = w1 + 7 w0, linear:
#    meaning x1 + 5 x2 + 7.
data, res = run([(3, [(0, 0, 1, 1), (0, 0, 0, 7)]),
                 (3, [(0, 0, 0, 1), (1, 0, 1, 1), (1, 0, 2, 5),
                      (2, 2, 1, 0)])], 3, 1)
want = digest(b"A", u32(1), u32(1), elt(1), u32(1), u32(2), elt(1),
              b"O", u32(0), u32(3), u32(1), elt(1), u32(2), elt(5), u32(0),
              elt(7))
check(res["facts_sha256"] == want, "a linear wire and an assertion: the bytes")
check(res["kinds"] == {"linear": 4, "assertion": 1},
      f"a linear wire and an assertion: kinds {res['kinds']}")

# 3. Zero coefficients are kept, and the kind looks at monomials only.
#    o0 = x1 + x1: one slot (0, 1) whose coefficient is 1 + 1 = 0 in
#    GF(2^128); kept, so the wire is linear with the meaning 0 x1.
#    o1 = x1 x2 + x1 x2: the slot (1, 2) with 0, kept, so the wire is
#    declared (variable 3) with the fact d3 = 0 x1 x2.
data, res = run([(3, [(0, 0, 1, 1), (0, 0, 1, 1),
                      (1, 2, 1, 1), (1, 2, 1, 1)])], 3, 2)
want = digest(b"D", u32(3), u32(1), u32(1), u32(2), elt(0),
              b"O", u32(0), u32(1), u32(1), elt(0),
              b"O", u32(1), u32(1), u32(3), elt(1))
check(res["facts_sha256"] == want, "zero coefficients kept: the bytes")
check(res["kinds"] == {"linear": 1, "declared": 1},
      f"zero coefficients kept: kinds {res['kinds']}")

# 4. The certificate (ADR 0094): each wire's slot count, the distinct
#    monomials of its expansion. o0 = x1 + x2 + x1: two slots.
data, res = run([(3, [(0, 0, 1, 1), (0, 0, 2, 1), (0, 0, 1, 1)])], 3, 1)
_, _, _, ident = cv.read_lfc2(FLD, data)
want = (b"LFCK" + cv.uleb(2) + ident + cv.uleb(1)
        + cv.uleb(1) + cv.uleb(2))
check(res["certificate"] == want, "the certificate's bytes")

# 5. A linear wire longer than Max_Form is declared: o0 = x1 + x2 + x3 +
#    x4, four variables besides the constant, over GF(2^128)'s 3.
data, res = run([(5, [(0, 0, 1, 1), (0, 0, 2, 1), (0, 0, 3, 1),
                      (0, 0, 4, 1)])], 5, 1)
check(res["kinds"] == {"declared": 1}, f"over Max_Form: kinds {res['kinds']}")

# 6. The facts are length-prefixed: two assertions whose meanings split
#    the same entries differently have different digests. Layer 1: w0,
#    w1; layer 0: the assertion w0 * w1 = 0. In the first circuit w0 = x1
#    + x2 and w1 = x3, in the second w0 = x1 and w1 = x2 + x3: (x1 + x2)
#    x3 and x1 (x2 + x3) differ at x1 x2.
_, r1 = run([(2, [(0, 1, 0, 0)]),
             (4, [(0, 0, 1, 1), (0, 0, 2, 1), (1, 0, 3, 1)])], 4, 1)
_, r2 = run([(2, [(0, 1, 0, 0)]),
             (4, [(0, 0, 1, 1), (1, 0, 2, 1), (1, 0, 3, 1)])], 4, 1)
check(r1["facts_sha256"] != r2["facts_sha256"],
      "two assertions that split the same entries: different digests")

print(f"census-test: {passed} passed, {failed} failed")
sys.exit(1 if failed else 0)
