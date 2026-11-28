#!/usr/bin/env python3
"""Tests of values-check.py on small circuits over GF(2^128) written here
by hand: a required assertion the circuit has is found, also up to a
constant; one it does not have is reported missing; a changed constant
in the circuit is detected. Also the field's product against the
vectors' own, the plucker's polynomials on their points, and the points'
dependence on the file.

Run: python3 -I scripts/values-check-test.py
"""

import importlib.util
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("vc", HERE / "values-check.py")
vc = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(vc)
cv = vc.cv

failed = 0
passed = 0


def check(ok, what):
    global failed, passed
    if ok:
        passed += 1
    else:
        failed += 1
        print(f"FAIL: {what}")


def circuit(layers, ninput, noutput):
    """The bytes and the reader's form of the circuit whose layers, from
    layer 0, are (number of wires read, terms (g, h0, h1, k))."""
    circ = {"noutput": noutput, "ninput": ninput, "npublic": 0,
            "layers": [(max(1, (nw - 1).bit_length()), nw, t)
                       for nw, t in layers]}
    data = cv.write_lfc2(vc.FLD, circ)
    st, back, _, _ = cv.read_lfc2(vc.FLD, data)
    if st != "ok":
        sys.exit(f"values-check-test: a test circuit is refused: {st}")
    return back, data


def groups(circ, data, fn):
    return vc.check(circ, data, fn)[0]


# The field: the windowed product equals the vectors' product, and the
# inverse is one.
rnd = random.Random(1)
ok = True
for _ in range(200):
    a, b = rnd.getrandbits(128), rnd.getrandbits(128)
    ok = ok and vc.mul(a, b) == cv.FIELDS["gf2_128"]["F"].mul(a, b)
check(ok, "the product equals the vectors' product")
a = rnd.getrandbits(128) | 1
check(vc.mul(a, vc.inv(a)) == 1, "the inverse")

# The plucker: bit k of i at the point X_i, bit_plucker.h.
vc.PLUCK = vc.plucker_polynomials()
xs = [vc.of_scalar(2 * i) ^ vc.of_scalar(15) for i in range(16)]
ok = True
for i in range(16):
    bits = vc.pluck(vc.const(xs[i]))
    ok = ok and [b[0] for b in bits] == [(i >> k) & 1 for k in range(4)]
check(ok, "the plucker's four polynomials at the sixteen points")

# 1. One layer, inputs 1, x1, x2; an output, and the assertion x1 x2 = 0
#    alone on its wire (the reader's Isolated premise).
c1, d1 = circuit([(3, [(0, 0, 0, 1), (1, 2, 1, 0)])], 3, 2)
g = groups(c1, d1, lambda x: [("a", vc.times(x[1], x[2])),
                              ("a", vc.scale(5, vc.times(x[1], x[2])))])
check(g == {"a": (2, 2, 0)}, f"an assertion found, also times 5: {g}")

# 2. One it does not have: x1 x1 = 0.
g = groups(c1, d1, lambda x: [("b", vc.times(x[1], x[1]))])
check(g == {"b": (1, 0, 1)}, f"an assertion missing: {g}")

# 3. Two layers: w0 = 1, w1 = x1 + 3, w2 = x2; then (x1 + 3) x2 = 0.
lay1 = (3, [(0, 0, 0, 1), (1, 0, 1, 1), (1, 0, 0, 3), (2, 0, 2, 1)])
c3, d3 = circuit([(3, [(0, 0, 0, 1), (1, 2, 1, 0)]), lay1], 3, 2)
want = lambda x: [("c", vc.times(vc.add(x[1], vc.const(3)), x[2]))]  # noqa: E731
check(groups(c3, d3, want) == {"c": (1, 1, 0)}, "through a linear wire")

# 4. The same circuit with the constant 3 changed to 4: refused.
lay1b = (3, [(0, 0, 0, 1), (1, 0, 1, 1), (1, 0, 0, 4), (2, 0, 2, 1)])
c4, d4 = circuit([(3, [(0, 0, 0, 1), (1, 2, 1, 0)]), lay1b], 3, 2)
check(groups(c4, d4, want) == {"c": (1, 0, 1)}, "a changed constant")

# 5. A bit assertion, x1 - x1 x1 = 0, as logic.h asserts an input bit:
#    w0 = 1, w1 = x1 + x1 x1 (declared), then w1 * 1 = 0.
lay5 = (3, [(0, 0, 0, 1), (1, 0, 1, 1), (1, 1, 1, 1)])
c5, d5 = circuit([(2, [(0, 0, 0, 1), (1, 0, 1, 0)]), lay5], 3, 2)
g = groups(c5, d5, lambda x: [("Bits", vc.bit_assertion(x[1])),
                              ("Bits", vc.bit_assertion(x[2]))])
check(g == {"Bits": (2, 1, 1)}, f"a bit assertion found, another missing: {g}")

# 6. Constants: zero holds by itself, one never does.
g = groups(c1, d1, lambda x: [("k", vc.const(0)), ("k", vc.const(1))])
check(g == {"k": (2, 1, 1)}, f"constant required assertions: {g}")

# 7. The points depend on the file and only on it.
p1 = vc.points(d1, 3)
check(p1 == vc.points(d1, 3) and p1 != vc.points(d3, 3) and p1[0] != p1[1],
      "the points: repeatable, per file, two distinct")

# 8. No assertion in the circuit: the required ones are reported
#    missing, exit status 1, and the report does not fail on the empty
#    set (the bound is not computed).
import contextlib  # noqa: E402
import io  # noqa: E402

out = io.StringIO()
with contextlib.redirect_stdout(out):
    code = vc.report({"a": (3, 0, 3)}, 0, 0, 0)
check(code == 1 and "none to bound" in out.getvalue(),
      f"no assertion in the circuit: exit {code}")

print(f"values-check-test: passed {passed}, failed {failed}")
sys.exit(1 if failed else 0)
