#!/usr/bin/env python3
"""The tests of scripts/check-spark-off.py, on temporary trees.

Each case writes a small tree (units under src/, a register under
docs/guide/), runs the checker on it and compares its exit status with
what is expected: a body outside SPARK that a row names, qualified, in
its column Item passes; one named only bare, only as a dependant, or not
at all fails; the aspect and the pragma are found across line breaks; a
comment marker inside a string literal does not hide what follows it,
and a character literal is not taken for the start of a string; a body
in a nested package is named with that package; a body nested in a
subprogram body, and a file whose scopes cannot be followed, are
refused. Run by the lint step of make check; needs only Python 3.
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

MULTILINE = ("package body Gamma is\n"
             "   procedure Lemma (X : Integer) with\n"
             "     SPARK_Mode =>\n"
             "       Off\n"
             "   is\n   begin\n      null;\n   end Lemma;\n"
             "end Gamma;\n")
PRAGMA_SPLIT = "pragma\n  SPARK_Mode\n    (Off);\npackage body Delta is\nend Delta;\n"

#  The aspect after a default that holds the comment marker: split at
#  "--", the line would lose its aspect.
STRING_DASH = ("package body Alpha is\n"
               "   procedure Lemma (S : String := \"a\"\"--\") with SPARK_Mode => Off is\n"
               "   begin\n      null;\n   end Lemma;\n"
               "end Alpha;\n")
#  A character literal that is a quotation mark, then the aspect.
CHAR_QUOTE = ("package body Alpha is\n"
              "   Q : constant Character := '\"';\n"
              "   D : constant String := Character'('-') & \"-\";\n"
              "   procedure Lemma (X : Integer) with SPARK_Mode => Off is\n"
              "   begin\n      null;\n   end Lemma;\n"
              "end Alpha;\n")
#  A real comment after a string literal.
STRING_COMMENT = ("package body Alpha is\n"
                  "   S : constant String := \"x\";  --  SPARK_Mode => Off\n"
                  "end Alpha;\n")
#  A body outside SPARK in a package nested in the unit's body, beside a
#  body of the same simple name in the unit.
NESTED = ("package body Field_GF2_128 is\n"
          "   function Same (A, B : Integer) return Boolean is (A = B);\n"
          "   package Helpers is\n"
          "      function Same (A, B : Integer) return Boolean;\n"
          "   end Helpers;\n"
          "   package body Helpers is\n"
          "      function Same (A, B : Integer) return Boolean with\n"
          "        SPARK_Mode => Off\n"
          "      is\n      begin\n         return A = B;\n      end Same;\n"
          "   end Helpers;\n"
          "end Field_GF2_128;\n")
NESTED_PRAGMA = ("package body Alpha is\n"
                 "   package body Helpers is\n"
                 "      pragma SPARK_Mode (Off);\n"
                 "   end Helpers;\n"
                 "end Alpha;\n")
#  A body outside SPARK local to a subprogram body.
LOCAL = ("package body Alpha is\n"
         "   procedure Outer is\n"
         "      procedure Local with SPARK_Mode => Off is\n"
         "      begin\n         null;\n      end Local;\n"
         "   begin\n      Local;\n   end Outer;\n"
         "end Alpha;\n")
#  An end whose name is not the scope it closes.
MISMATCH = ("package body Alpha is\n"
            "   procedure Lemma (X : Integer) with SPARK_Mode => Off is\n"
            "   begin\n      null;\n   end Other;\n"
            "end Alpha;\n")
PACKAGE_OFF = ("package body Epsilon with SPARK_Mode => Off is\n"
               "   procedure P is\n   begin\n      null;\n   end P;\n"
               "end Epsilon;\n")

CASES = [
    ("named in its Item", {"src/alpha.adb": BODY}, "| L1 | `Alpha.Lemma` is proved elsewhere. | x | y | z |\n", 0),
    ("named bare only", {"src/alpha.adb": BODY}, "| T6 | `Lemma` is trusted. | x | y | z |\n", 1),
    ("named only as a dependant", {"src/alpha.adb": BODY},
     "| L1 | `Gamma.Other` is proved elsewhere. | `Alpha.Lemma` uses it. | y | z |\n", 1),
    ("not named", {"src/alpha.adb": BODY}, "| L1 | `Gamma.Lemma` is proved elsewhere. | x | y | z |\n", 1),
    ("named outside a row", {"src/alpha.adb": BODY}, "`Alpha.Lemma` in prose.\n", 1),
    ("aspect across lines, not named", {"src/gamma.adb": MULTILINE}, "| L1 | `Alpha.Lemma` | x |\n", 1),
    ("aspect across lines, named", {"src/gamma.adb": MULTILINE}, "| L1 | `Gamma.Lemma` | x |\n", 0),
    ("pragma across lines, not named", {"src/delta.adb": PRAGMA_SPLIT}, "| L1 | `Alpha.Lemma` | x |\n", 1),
    ("pragma across lines, named", {"src/delta.adb": PRAGMA_SPLIT}, "| L2 | `Delta` | x |\n", 0),
    ("unit off, not named", {"src/beta.adb": UNIT_OFF}, "| L1 | `Alpha.Lemma` | x |\n", 1),
    ("unit off, named", {"src/beta.adb": UNIT_OFF}, "| L2 | `Beta` | x |\n", 0),
    ("nothing off", {"src/gamma.adb": "package body Gamma is\nend Gamma;\n"}, "", 0),
    ("comment marker in a string, not named", {"src/alpha.adb": STRING_DASH}, "| L1 | `Gamma.Lemma` | x |\n", 1),
    ("comment marker in a string, named", {"src/alpha.adb": STRING_DASH}, "| L1 | `Alpha.Lemma` | x |\n", 0),
    ("character literal quotation mark, not named", {"src/alpha.adb": CHAR_QUOTE}, "| L1 | `Gamma.Lemma` | x |\n", 1),
    ("character literal quotation mark, named", {"src/alpha.adb": CHAR_QUOTE}, "| L1 | `Alpha.Lemma` | x |\n", 0),
    ("comment after a string", {"src/alpha.adb": STRING_COMMENT}, "", 0),
    ("nested package, the unit's name only", {"src/field_gf2_128.adb": NESTED},
     "| T6 | `Field_GF2_128.Same` | x |\n", 1),
    ("nested package, named", {"src/field_gf2_128.adb": NESTED},
     "| T6 | `Field_GF2_128.Helpers.Same` | x |\n", 0),
    ("pragma in a nested package, the unit's name only", {"src/alpha.adb": NESTED_PRAGMA}, "| L2 | `Alpha` | x |\n", 1),
    ("pragma in a nested package, named", {"src/alpha.adb": NESTED_PRAGMA}, "| L2 | `Alpha.Helpers` | x |\n", 0),
    ("local to a subprogram body", {"src/alpha.adb": LOCAL},
     "| L1 | `Alpha.Local` `Alpha.Outer.Local` | x |\n", 1),
    ("scopes that cannot be followed", {"src/alpha.adb": MISMATCH}, "| L1 | `Alpha.Lemma` | x |\n", 1),
    ("aspect on a package, named", {"src/epsilon.adb": PACKAGE_OFF}, "| L2 | `Epsilon` | x |\n", 0),
    ("aspect on a package, not named", {"src/epsilon.adb": PACKAGE_OFF}, "| L2 | `Epsilon.P` | x |\n", 1),
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
