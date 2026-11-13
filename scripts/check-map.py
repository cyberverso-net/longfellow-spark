#!/usr/bin/env python3
"""Check the code maps of the guide against the code (make lint).

The diagrams of the guide name units in their boxes, and under each
diagram a table "Where it is in the code" maps every box to the units
an evaluator opens. This script keeps the two true to the code:

- every unit named in a box or in a map exists: a box names its units
  on the line after its last <br/>, comma-separated; a map names them
  in its column "Units", as links to their specification;
- every Unit.Subprogram named in a box is declared in the unit's
  specification (or, for a generic's instance, in the generic's), so
  that a rename breaks the diagram instead of leaving it behind; and
  every name of a map's column "Key subprograms" is declared in its
  unit, or, unqualified, in one of the row's units;
- every box of a diagram that names units has a row in its map;
- every link of a map's column "Units" points at the specification of
  the unit its text names;
- every unit appears in at least one map: the units of the proof
  partitions (scripts/prove-partitions.txt) and the sources of cli/src.
  A library-level instance (package X is new G) is covered by its
  generic G.

A map is a Markdown table whose first header cell is "Box" and which
has a column "Units". Each failure is printed with its file and line;
the exit status is 1 when there is one.

Run from the repository root:  python3 -I scripts/check-map.py
"""

import os
import re
import sys

PAGES = "docs/guide"
SRC_DIRS = ["src", "cli/src"]
PARTITIONS = "scripts/prove-partitions.txt"
INSTANCE = re.compile(r"^(.*)_(gf2_128|p256)$")
UNIT = re.compile(r"^[A-Z][A-Za-z0-9]*(?:_[A-Za-z0-9]+)*(?:\.[A-Z][A-Za-z0-9]*(?:_[A-Za-z0-9]+)*)*$")
LINK = re.compile(r"\[`?([^`\]]+)`?\]\(([^)]+)\)")
BOX = re.compile(r"\b([A-Za-z0-9_]+)\[\"(.*?)\"\]")


def spec_path(unit):
    """The specification of a unit, or None: Sha256.Trace is sha256-trace.ads."""
    name = unit.lower().replace(".", "-") + ".ads"
    for d in SRC_DIRS:
        p = os.path.join(d, name)
        if os.path.isfile(p):
            return p
    return None


def body_path(unit):
    name = unit.lower().replace(".", "-") + ".adb"
    for d in SRC_DIRS:
        p = os.path.join(d, name)
        if os.path.isfile(p):
            return p
    return None


def source(path):
    """A file's text with its Ada comments removed, so that a declaration
    commented out is not taken for one."""
    return re.sub(r"--[^\n]*", "", open(path, encoding="utf-8").read())


def declares(unit, sub):
    """True when the unit (or its generic) declares the subprogram."""
    seen = set()
    while unit and unit not in seen:
        seen.add(unit)
        for path in (spec_path(unit), body_path(unit)):
            if path:
                text = source(path)
                if re.search(r"\b(procedure|function)\s+%s\b" % re.escape(sub), text, re.I):
                    return True
        m = INSTANCE.match(unit.lower())
        spec = spec_path(unit)
        generic = None
        if spec:
            g = re.search(r"\bis\s+new\s+([A-Za-z0-9_.]+)", source(spec))
            generic = g.group(1) if g else None
        unit = generic or (m.group(1) if m else None)
    return False


def resolve(name):
    """The unit and subprogram a name such as Zk_Prover.Commit stands for:
    the longest prefix that is a unit, the rest a subprogram."""
    parts = name.split(".")
    for k in range(len(parts), 0, -1):
        unit = ".".join(parts[:k])
        if spec_path(unit) or body_path(unit):
            return unit, ".".join(parts[k:])
    return None, None


def generic_of(unit):
    """The generic a library-level instance instantiates, in lower case."""
    spec = spec_path(unit.replace("-", "."))
    if not spec:
        return None
    text = re.sub(r"--[^\n]*", "", open(spec, encoding="utf-8").read())
    m = re.search(r"^\s*package\s+[A-Za-z0-9_.]+\s+is\s+new\s+([A-Za-z0-9_.]+)", text, re.M | re.I)
    return m.group(1).lower().replace(".", "-") if m else None


def all_units():
    units = set()
    for line in open(PARTITIONS, encoding="utf-8"):
        line = line.split("#")[0].split()
        units.update(u.lower() for u in line[1:])
    for name in os.listdir("cli/src"):
        if name.endswith((".ads", ".adb")):
            units.add(name[:-4])
    return units


def tables(lines):
    """The maps of a page: (header line, header cells, rows as (line, cells))."""
    i = 0
    while i < len(lines):
        if lines[i].startswith("|"):
            cells = [c.strip() for c in lines[i].strip().strip("|").split("|")]
            j = i + 1
            rows = []
            while j < len(lines) and lines[j].startswith("|"):
                rows.append((j + 1, [c.strip() for c in lines[j].strip().strip("|").split("|")]))
                j += 1
            if cells and cells[0] == "Box" and "Units" in cells:
                yield i + 1, cells, rows[1:]
            i = j
        else:
            i += 1


def main():
    failures = []
    covered = set()
    pages = sorted(os.path.join(PAGES, n) for n in os.listdir(PAGES) if n.endswith(".md"))
    maps = 0
    for page in pages:
        lines = open(page, encoding="utf-8").read().split("\n")
        #  The boxes of each diagram, by node id, with their line; a
        #  diagram's boxes are checked when the next map names them.
        diagrams = []
        fence = False
        for n, line in enumerate(lines, 1):
            if line.startswith("```"):
                if not fence and line.strip() == "```mermaid":
                    fence = True
                    diagrams.append((n, {}))
                else:
                    fence = False
                continue
            if fence:
                for node, text in BOX.findall(line):
                    diagrams[-1][1][node] = (n, text)
        ids_of = {}
        for header, head, rows in tables(lines):
            before = [d for d in diagrams if d[0] < header]
            boxes = before[-1][1] if before else {}
            if before:
                ids_of.setdefault(before[-1][0], set()).update(
                    i.replace(".", "_") for _, c in rows for i in re.findall(r"[A-Za-z0-9.]+", c[0]))
            for _, cells in rows:
                ids = {i.replace(".", "_") for i in re.findall(r"[A-Za-z0-9.]+", cells[0])}
                #  A node stands for the ids its name holds, joined by
                #  "__", with "_" for the dot of an id: PS4__PS5__H is a
                #  box of PS4 and PS5, D3_2 the box D3.2.
                for node, (n, text) in boxes.items():
                    if not ids & set(node.split("__")) or "<br/>" not in text:
                        continue
                    for name in text.rsplit("<br/>", 1)[1].split(","):
                        name = name.strip().strip("`")
                        if not name:
                            continue
                        if not UNIT.match(name):
                            failures.append((page, n, "box %s names %r, not a unit" % (node, name)))
                            continue
                        unit, sub = resolve(name)
                        if unit is None:
                            failures.append((page, n, "box %s names %s, no such unit" % (node, name)))
                        elif sub and not declares(unit, sub.split(".")[-1]):
                            failures.append((page, n, "box %s names %s, not declared in %s"
                                             % (node, name, unit)))
        #  Every box that names units, in a diagram with a map, has a row
        #  in one of the maps that follow it, or its units would escape
        #  the checks above.
        for start, boxes in diagrams:
            if start not in ids_of:
                continue
            for node, (n, text) in boxes.items():
                if "<br/>" in text and not ids_of[start] & set(node.split("__")):
                    failures.append((page, n, "box %s names units but has no row in its map" % node))
        for header, head, rows in tables(lines):
            maps += 1
            col = head.index("Units")
            key = head.index("Key subprograms") if "Key subprograms" in head else None
            for n, cells in rows:
                if col >= len(cells):
                    continue
                row_units = [resolve(t)[0] for t, _ in LINK.findall(cells[col])]
                #  The key subprograms: a qualified name is checked in its
                #  unit, a bare one in one of the row's units.
                if key is not None and key < len(cells):
                    for name in re.findall(r"`([A-Za-z0-9_.]+)`", cells[key]):
                        if "." in name:
                            unit, sub = resolve(name)
                            if unit is None or not sub:
                                failures.append((page, n, "map's key subprogram %s names no unit"
                                                 % name))
                                continue
                            units = [unit]
                        else:
                            sub, units = name, [u for u in row_units if u]
                        if not any(declares(u, sub.split(".")[-1]) for u in units):
                            failures.append((page, n, "map's key subprogram %s is declared in none of %s"
                                             % (name, ", ".join(units) or "the row's units")))
                for text, target in LINK.findall(cells[col]):
                    unit, sub = resolve(text)
                    if unit is None:
                        failures.append((page, n, "map names %s, no such unit" % text))
                        continue
                    want = (spec_path(unit) or body_path(unit))
                    got = os.path.normpath(os.path.join(os.path.dirname(page), target.split("#")[0]))
                    if got != os.path.normpath(want):
                        failures.append((page, n, "map links %s to %s, its specification is %s"
                                         % (text, target, want)))
                    if sub and not declares(unit, sub.split(".")[-1]):
                        failures.append((page, n, "map names %s, not declared in %s" % (text, unit)))
                    covered.add(unit.lower().replace(".", "-"))
    if maps:
        for unit in sorted(all_units()):
            if unit in covered or (generic_of(unit) or "") in covered:
                continue
            failures.append((PARTITIONS if spec_path(unit) and spec_path(unit).startswith("src")
                             else "cli/src", 0, "unit %s is in no map: code the guide does not place"
                             % unit))
    failures = list(dict.fromkeys(failures))
    for page, n, why in failures:
        print("%s:%d: %s" % (page, n, why))
    if failures:
        return 1
    print("maps: %d maps, every unit named exists and every unit is placed" % maps)
    return 0


if __name__ == "__main__":
    sys.exit(main())
