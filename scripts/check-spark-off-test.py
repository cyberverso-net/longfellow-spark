#!/usr/bin/env python3
"""The tests of scripts/check-spark-off.py, on temporary trees.

Each case writes a small tree (units under src/, a register under
docs/guide/), runs the checker on it and compares its exit status with
what is expected: a body outside SPARK that the register names passes,
one it does not name fails, and so does a unit under pragma
SPARK_Mode (Off). Run by the lint step of make check; needs only
Python 3.
"""

import os
import subprocess
import sys
import tempfile

CHECKER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check-spark-off.py")

BODY = ("package body Alpha is\n"
        "   procedure Lemma (X : Integer) with\n"
        "     SPARK_Mode => Off\n"
        "   is\n   begin\n      null;\n   end Lemma;\n"
        "   --  SPARK_Mode => Off in a comment does not count.\n"
        "end Alpha;\n")
UNIT_OFF = "pragma SPARK_Mode (Off);\npackage body Beta is\nend Beta;\n"

CASES = [
    ("named qualified", {"src/alpha.adb": BODY}, "| L1 | `Alpha.Lemma` is proved elsewhere. |\n", 0),
    ("named bare", {"src/alpha.adb": BODY}, "| T6 | `Lemma` is trusted. |\n", 0),
    ("not named", {"src/alpha.adb": BODY}, "| L1 | `Gamma.Lemma` is proved elsewhere. |\n", 1),
    ("named outside a row", {"src/alpha.adb": BODY}, "`Alpha.Lemma` in prose.\n", 1),
    ("unit off, not named", {"src/beta.adb": UNIT_OFF}, "| L1 | `Alpha.Lemma` |\n", 1),
    ("unit off, named", {"src/beta.adb": UNIT_OFF}, "| L2 | `Beta` |\n", 0),
    ("nothing off", {"src/gamma.adb": "package body Gamma is\nend Gamma;\n"}, "", 0),
]


def run(files, register):
    with tempfile.TemporaryDirectory() as root:
        for rel, text in files.items():
            os.makedirs(os.path.dirname(os.path.join(root, rel)), exist_ok=True)
            with open(os.path.join(root, rel), "w", encoding="utf-8") as f:
                f.write(text)
        os.makedirs(os.path.join(root, "docs", "guide"), exist_ok=True)
        with open(os.path.join(root, "docs", "guide", "trusted-base.md"), "w",
                  encoding="utf-8") as f:
            f.write(register)
        return subprocess.run([sys.executable, "-I", CHECKER, root],
                              capture_output=True, text=True).returncode


def main():
    failures = 0
    for label, files, register, expected in CASES:
        got = run(files, register)
        if got != expected:
            print("check-spark-off-test: %s: exit %d, expected %d" % (label, got, expected))
            failures += 1
    print("check-spark-off-test: %d cases, %d failures" % (len(CASES), failures))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
