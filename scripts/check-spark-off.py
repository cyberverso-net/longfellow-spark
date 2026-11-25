#!/usr/bin/env python3
"""List the code outside SPARK in src/ and check that each has a register row.

GNATprove does not analyse a body under SPARK_Mode Off: it takes the
subprogram's contract as given. Such a body is an assumption of the
proof, and every one must be listed in the register of the trusted base
(docs/guide/trusted-base.md). This script finds each one in src/:

- an aspect SPARK_Mode => Off on a subprogram: the subprogram, named
  Unit.Subprogram from the unit of its file;
- a pragma SPARK_Mode (Off) at the start of a unit: the whole unit.

It prints the list, and fails when a row of the register's tables (a
line that starts with "| ") does not name the subprogram (or the unit)
in backquotes, qualified (`Unit.Subprogram`) or not (`Subprogram`).
Each failure is printed with its file and line; the exit status is 1
when there is one.

Run from the repository root:  python3 -I scripts/check-spark-off.py
"""

import os
import re
import sys

OFF = re.compile(r"SPARK_Mode\s*(=>\s*Off\b|\(\s*Off\s*\))", re.IGNORECASE)
PRAGMA = re.compile(r"^\s*pragma\s+SPARK_Mode\b", re.IGNORECASE)
SUBPROGRAM = re.compile(r"^\s*(?:overriding\s+)?(?:procedure|function)\s+([A-Za-z_][\w]*)",
                        re.IGNORECASE)
UNIT = re.compile(r"^\s*(?:private\s+)?(?:package(?:\s+body)?|procedure|function)\s+([A-Za-z_][\w.]*)",
                  re.IGNORECASE)


def code(line):
    """The line without its comment."""
    return line.split("--", 1)[0]


def off_parts(path):
    """The (line number, name) of each part of a file outside SPARK."""
    with open(path, encoding="utf-8") as f:
        lines = f.read().splitlines()
    unit = None
    for text in lines:
        m = UNIT.match(code(text))
        if m:
            unit = m.group(1)
            break
    parts = []
    for i, text in enumerate(lines):
        c = code(text)
        if not OFF.search(c):
            continue
        if PRAGMA.match(c):
            parts.append((i + 1, unit, None))
            continue
        name = None
        for j in range(i, -1, -1):
            m = SUBPROGRAM.match(code(lines[j]))
            if m:
                name = m.group(1)
                break
        parts.append((i + 1, unit, name))
    return parts


def register_rows(path):
    with open(path, encoding="utf-8") as f:
        return [line for line in f.read().splitlines() if line.startswith("| ")]


def named(rows, unit, name):
    keys = ["`%s`" % unit] if name is None else ["`%s.%s`" % (unit, name), "`%s`" % name]
    return any(k in row for row in rows for k in keys)


def main(root):
    rows = register_rows(os.path.join(root, "docs", "guide", "trusted-base.md"))
    src = os.path.join(root, "src")
    failures = 0
    found = 0
    for base in sorted(os.listdir(src)):
        if not base.endswith((".ads", ".adb")):
            continue
        path = os.path.join(src, base)
        for line, unit, name in off_parts(path):
            found += 1
            label = unit if name is None else "%s.%s" % (unit, name)
            if named(rows, unit, name):
                print("spark-off: src/%s:%d %s" % (base, line, label))
            else:
                print("src/%s:%d: %s is outside SPARK and has no row in "
                      "docs/guide/trusted-base.md" % (base, line, label))
                failures += 1
    print("spark-off: %d parts outside SPARK, %d without a register row"
          % (found, failures))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "."))
