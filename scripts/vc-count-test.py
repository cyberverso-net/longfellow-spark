#!/usr/bin/env python3
"""Tests of vc-count.py: small runs written as GNATprove writes them (a
gnatprove.out with its summary and its units, one .spark file per unit),
and what the script must print or refuse.

Run: python3 -I scripts/vc-count-test.py
"""

import json
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "vc-count.py")

#  The units of the partition p256 of prove-partitions.txt, so that the
#  mode --partition can be tested on the real list.
P256 = ["p256_field", "field_p256", "field_p256-laws"]


def check(rule, severity="info", suppressed=None):
    e = {"rule": rule, "severity": severity, "file": "x.adb", "line": 1}
    if suppressed:
        e["suppressed"] = suppressed
    return e


def run_dir(units, total, assume=()):
    """A directory with gnatprove.out and the .spark files of `units`, a
    map from unit to (flow entries, proof entries)."""
    d = tempfile.mkdtemp()
    out = ["Summary of SPARK analysis", "",
           "SPARK Analysis results        Total        Flow   Provers",
           "Total                          %d    0 (0%%)    0 (0%%)" % total, "",
           "Analyzed %d units" % len(units)]
    for u in units:
        out.append("in unit %s, 1 subprograms and packages out of 1 analyzed" % u)
        out.append("  X at x.ads:1 flow analyzed (0 errors, 0 checks) and proved (0 checks)")
        flow, proof = units[u]
        with open(os.path.join(d, u + ".spark"), "w") as f:
            json.dump({"flow": flow, "proof": proof,
                       "pragma_assume": [1] if u in assume else []}, f)
    with open(os.path.join(d, "gnatprove.out"), "w") as f:
        f.write("\n".join(out) + "\n")
    return d


def run(args):
    r = subprocess.run([sys.executable, "-I", SCRIPT] + args, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


GOOD = {
    "p256_field": ([check("GLOBAL_WRONG"), check("UNINITIALIZED")],
                   [check("VC_RANGE_CHECK"), check("VC_PREDICATE_CHECK"), check("VC_POSTCONDITION")]),
    "field_p256": ([check("GLOBAL_WRONG")], [check("VC_RESOURCE_LEAK")]),
    "field_p256-laws": ([], [check("VC_POSTCONDITION")]),
}

CASES = [
    # (name, units, total, assume, arguments, exit status, text expected in the output)
    ("adds up", GOOD, 8, (), ["p256_field"], 0, "| Type predicates | 1 | provers |"),
    ("the totals per unit", GOOD, 8, (), ["p256_field", "field_p256"], 0, "| **Total** | **5** | **2** | |"),
    ("the provers' line", GOOD, 8, (), ["p256_field"], 0, "discharged by the provers: p256_field 3"),
    ("the leak checks named", GOOD, 8, (), ["field_p256"], 0, "| Memory leaks (an allocation freed) | 1 | provers |"),
    ("a check too many", GOOD, 7, (), ["p256_field"], 2, "add up to 8 checks, the summary says 7"),
    ("a check missing", GOOD, 9, (), ["p256_field"], 2, "add up to 8 checks, the summary says 9"),
    ("a flow warning is not a check",
     dict(GOOD, p256_field=(GOOD["p256_field"][0] + [check("INEFFECTIVE", "warning")], GOOD["p256_field"][1])),
     8, (), ["p256_field"], 0, "flow warnings, not counted: p256_field 1"),
    ("an unproved check",
     dict(GOOD, field_p256=(GOOD["field_p256"][0], [check("VC_ASSERT", "medium")])),
     8, (), ["field_p256"], 1, "field_p256: unproved VC_ASSERT"),
    ("a justified check",
     dict(GOOD, field_p256=(GOOD["field_p256"][0], [check("VC_ASSERT", "medium", "reviewed")])),
     8, (), ["field_p256"], 1, "field_p256: justified VC_ASSERT"),
    ("a pragma Assume", GOOD, 8, ("field_p256",), ["field_p256"], 1, "field_p256: 1 pragma Assume"),
    ("a unit the run did not analyse", GOOD, 8, (), ["gf2_128"], 2, "gf2_128 was not analysed"),
    ("the partition, its units as columns", GOOD, 8, (), ["--partition", "p256"], 0,
     "| Check | `p256_field` | `field_p256` | `field_p256-laws` | Discharged by |"),
    ("the files of another partition", GOOD, 8, (), ["--partition", "sumcheck"], 2, "not of the partition sumcheck"),
    ("a partition that does not exist", GOOD, 8, (), ["--partition", "nosuch"], 2, "no partition nosuch"),
    ("no unit named", GOOD, 8, (), [], 2, "no unit named"),
    ("an unknown option", GOOD, 8, (), ["--units"], 2, "unknown option --units"),
]


def main():
    failures = 0
    for name, units, total, assume, args, status, text in CASES:
        d = run_dir(units, total, assume)
        code, out = run(["--dir", d] + args)
        if code != status or text not in out:
            failures += 1
            print("FAIL %s: exit %d (expected %d), output:\n%s" % (name, code, status, out))
    code, out = run(["--dir", os.path.join(tempfile.mkdtemp(), "none"), "p256_field"])
    if code != 2 or "run a proof first" not in out:
        failures += 1
        print("FAIL no gnatprove.out: exit %d\n%s" % (code, out))
    print("vc-count: %d cases, %d failures" % (len(CASES) + 1, failures))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
