#!/usr/bin/env python3
"""The verification conditions of some units, by kind of check, from the
files GNATprove writes for each unit it analyses, checked against the
summary of the run.

The summary GNATprove prints at the end of a run covers every unit the
run analysed; a chapter of the guide gives the counts of its own units.
After a run (`make prove`, or `make prove-partition PARTITION=<name>`),
this script reads obj/development/gnatprove/<unit>.spark for every unit
the run analysed and prints one table: a row per kind of check, a column
per unit named.

Run: python3 -I scripts/vc-count.py [--dir DIR] [--partition NAME] [UNIT...]
  UNIT       a unit as gnatprove -u takes it, without extension: gf2_128,
             clmul64, sumcheck_verifier_p256 ...
  NAME       a partition of scripts/prove-partitions.txt: the run must be
             of exactly that partition; with no UNIT, its units are the
             columns.
  DIR        where the files are (default obj/development/gnatprove).

The script checks itself before it prints anything: the units the run
analysed, as gnatprove.out lists them, must add up to the total of its
summary, and every unit named must be one of them. A file left by an
earlier run, a kind of check the script misreads, or a check counted
twice makes it fail rather than print a wrong table.

The last lines say whether any check is unproved or justified, and
whether a unit has a pragma Assume. Flow warnings (a value set and not
used, a statement with no effect) are not checks and are not counted;
a line gives their number. The checks the provers discharged, per unit,
are also the sum of the "proved (N checks)" of gnatprove.out for the
unit's subprograms; the flow checks are not in that sum.

Exit status: 0 when the counts add up, every check of every unit named
is proved and no unit has a pragma Assume; 1 when a check is unproved or
justified or a unit has a pragma Assume; 2 when the counts do not add
up, a file is missing or an argument is wrong.
"""

import json
import os
import re
import sys

#  The kinds of check, as the .spark files name them, in the order and
#  with the words of the chapters' tables.
FLOW = [
    ("GLOBAL_WRONG", "Data dependencies (`Global`)"),
    ("DEPENDS_WRONG", "Flow dependencies (`Depends`)"),
    ("UNINITIALIZED", "Initialisation"),
    ("ALIASING", "Non-aliasing"),
    ("SUBPROGRAM_TERMINATION", "Termination"),
]
PROOF = [
    ("VC_RANGE_CHECK", "Range checks"),
    ("VC_DIVISION_CHECK", "Division checks (`/`, `mod`)"),
    ("VC_OVERFLOW_CHECK", "Overflow checks"),
    ("VC_INDEX_CHECK", "Index checks"),
    ("VC_LENGTH_CHECK", "Length checks"),
    ("VC_DISCRIMINANT_CHECK", "Discriminant checks"),
    ("VC_TAG_CHECK", "Tag checks"),
    ("VC_NULL_POINTER_DEREFERENCE", "Null dereferences"),
    ("VC_PREDICATE_CHECK", "Type predicates"),
    ("VC_CONTAINER_AGGR_CHECK", "Container aggregates"),
    ("VC_PRECONDITION", "Preconditions of the calls"),
    ("VC_ASSERT", "Assertions"),
    ("VC_LOOP_INVARIANT_INIT", "Loop invariants (base case and preservation)"),
    ("VC_LOOP_INVARIANT_PRESERV", "Loop invariants (base case and preservation)"),
    ("VC_LOOP_VARIANT", "Loop variants"),
    ("VC_POSTCONDITION", "Postconditions"),
    ("VC_CONTRACT_CASE", "Contract cases"),
    ("VC_SUBPROGRAM_VARIANT", "Variants of the recursive functions"),
    ("VC_RESOURCE_LEAK", "Memory leaks (an allocation freed)"),
    ("VC_RESOURCE_LEAK_AT_END_OF_SCOPE", "Memory leaks (an allocation freed)"),
]
PARTITIONS = os.path.join(os.path.dirname(os.path.abspath(__file__)), "prove-partitions.txt")


def fail(message):
    print("vc-count: " + message, file=sys.stderr)
    sys.exit(2)


def summary(directory):
    """The total of the summary and the units of the run, from gnatprove.out."""
    path = os.path.join(directory, "gnatprove.out")
    try:
        text = open(path).read()
    except OSError:
        fail("no %s; run a proof first" % path)
    total = re.search(r"^Total\s+(\d+)\s", text, re.M)
    if not total:
        fail("%s has no summary total" % path)
    units = re.findall(r"^in unit ([A-Za-z0-9_.-]+), ", text, re.M)
    return int(total.group(1)), units


def partition_units(name):
    for line in open(PARTITIONS):
        if line.startswith("#") or not line.strip():
            continue
        words = line.split()
        if words[0] == name:
            return words[1:]
    fail("no partition %s in %s" % (name, PARTITIONS))


def load(directory, unit):
    path = os.path.join(directory, unit + ".spark")
    try:
        with open(path) as f:
            return json.load(f)
    except OSError:
        fail("no %s" % path)
    except ValueError:
        fail("%s is not a GNATprove file" % path)


def tally(d):
    """(counts by (label, by), flow warnings, problems) of one unit."""
    counts, warnings, problems = {}, 0, []
    for part, kinds, by in (("flow", FLOW, "flow analysis"), ("proof", PROOF, "provers")):
        names = dict(kinds)
        for e in d.get(part, []):
            rule = e.get("rule")
            #  A flow warning (a value set and not used, a statement with
            #  no effect) is not a check: GNATprove's summary does not
            #  count it, and neither does this table.
            if e.get("severity") == "warning":
                warnings += 1
                continue
            key = (names.get(rule, rule), by)
            counts[key] = counts.get(key, 0) + 1
            if e.get("severity") != "info":
                what = "justified" if e.get("suppressed") else "unproved"
                problems.append("%s %s at %s:%s" % (what, rule, e.get("file"), e.get("line")))
    if d.get("pragma_assume"):
        problems.append("%d pragma Assume" % len(d["pragma_assume"]))
    return counts, warnings, problems


def main(argv):
    directory = os.path.join("obj", "development", "gnatprove")
    partition = None
    units = []
    while argv:
        a = argv.pop(0)
        if a in ("--dir", "--partition"):
            if not argv:
                fail("%s needs a value" % a)
            if a == "--dir":
                directory = argv.pop(0)
            else:
                partition = argv.pop(0)
        elif a.startswith("-"):
            fail("unknown option %s\n%s" % (a, __doc__.split("\n\n")[2]))
        else:
            units.append(a)
    total, analysed = summary(directory)
    if partition is not None:
        expected = partition_units(partition)
        if sorted(expected) != sorted(analysed):
            fail("the files are of a run of %s, not of the partition %s (%s)"
                 % (" ".join(sorted(analysed)) or "no unit", partition, " ".join(sorted(expected))))
        units = units or expected
    if not units:
        fail("no unit named\n" + __doc__.split("\n\n")[2])
    for u in units:
        if u not in analysed:
            fail("%s was not analysed by the run of %s" % (u, directory))
    tallies = {u: tally(load(directory, u)) for u in analysed}
    added = sum(sum(c.values()) for c, _, _ in tallies.values())
    if added != total:
        fail("the units of the run add up to %d checks, the summary says %d" % (added, total))

    order = [(l, "flow analysis") for _, l in FLOW] + [(l, "provers") for _, l in PROOF]
    for u in units:
        for key in tallies[u][0]:
            if key not in order:
                order.append(key)
    rows = []
    for key in order:
        if key not in [r[0] for r in rows] and any(key in tallies[u][0] for u in units):
            rows.append((key, [tallies[u][0].get(key, 0) for u in units]))
    print("| Check | " + " | ".join("`%s`" % u for u in units) + " | Discharged by |")
    print("|---" * (len(units) + 2) + "|")
    for (label, by), counts in rows:
        print("| %s | %s | %s |" % (label, " | ".join(str(c) for c in counts), by))
    print("| **Total** | " + " | ".join("**%d**" % sum(tallies[u][0].values()) for u in units) + " | |")
    print()
    print("discharged by the provers: " + ", ".join(
        "%s %d" % (u, sum(n for (_, by), n in tallies[u][0].items() if by == "provers")) for u in units))
    print("the %d units of the run add up to its summary, %d checks" % (len(analysed), total))
    warned = [(u, tallies[u][1]) for u in units if tallies[u][1]]
    if warned:
        print("flow warnings, not counted: " + ", ".join("%s %d" % w for w in warned))
    problems = ["%s: %s" % (u, p) for u in units for p in tallies[u][2]]
    if problems:
        for p in problems:
            print(p)
        return 1
    print("every check proved, none justified, no pragma Assume")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
