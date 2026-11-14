#!/usr/bin/env python3
"""The tests of scripts/check-map.py, on temporary trees.

Each case writes a small tree (units under src/ and cli/src/, a list of
partitions, a page of the guide with a diagram and its map), runs the
checker on it and compares what it reports with what is expected, so
that a correct map that is refused fails as surely as a wrong one that
is let through. Run by the lint step of make check; needs only Python 3.
"""

import os
import subprocess
import sys
import tempfile

CHECKER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check-map.py")

UNITS = {
    "src/alpha.ads": "package Alpha is\n   procedure Run;\n   function Size return Natural;\nend Alpha;\n",
    "src/beta.ads": "generic\npackage Beta is\n   procedure Step;\nend Beta;\n",
    "src/beta_gf2_128.ads": "with Beta;\npackage Beta_GF2_128 is new Beta;\n",
    "src/gamma-delta.ads": "package Gamma.Delta is\n   procedure Go;\nend Gamma.Delta;\n",
    "cli/src/main_prog.adb": "procedure Main_Prog is\nbegin\n   null;\nend Main_Prog;\n",
    "scripts/prove-partitions.txt": "#  name, units\none alpha beta_gf2_128 gamma-delta\n",
}

GOOD = """# Page

```mermaid
flowchart LR
  X1["X1 run<br/>Alpha.Run"] --> X2__X3["X2, X3 steps<br/>Beta.Step, Gamma.Delta.Go"]
  N["a box without units"]
```

| Box | Units | Key subprograms | What |
|---|---|---|---|
| X1 | [`Alpha`](../../src/alpha.ads) | `Run`, `Size` | run |
| X2, X3 | [`Beta`](../../src/beta.ads), [`Gamma.Delta`](../../src/gamma-delta.ads) | `Step`, `Gamma.Delta.Go` | steps |

| Box | Units | What |
|---|---|---|
| Programs | [`Main_Prog`](../../cli/src/main_prog.adb) | the program |
"""

CASES = [
    ("a correct map", GOOD, []),
    ("a box names a unit that does not exist",
     GOOD.replace("Alpha.Run\"]", "Alphaa.Run\"]"), ["box X1 names Alphaa.Run, no such unit"]),
    ("a box names a subprogram its unit does not declare",
     GOOD.replace("Alpha.Run\"]", "Alpha.Walk\"]"), ["box X1 names Alpha.Walk, not declared in Alpha"]),
    ("a box names a subprogram of the generic, through the instance",
     GOOD.replace("Beta.Step,", "Beta_GF2_128.Step,"), []),
    ("a map links a unit to another unit's specification",
     GOOD.replace("[`Alpha`](../../src/alpha.ads)", "[`Alpha`](../../src/beta.ads)"),
     ["map links Alpha to ../../src/beta.ads, its specification is src/alpha.ads"]),
    ("a unit of the partitions in no map",
     GOOD.replace(", [`Gamma.Delta`](../../src/gamma-delta.ads)", ""),
     ["unit gamma-delta is in no map: code the guide does not place"]),
    ("a program of cli/src in no map",
     GOOD.replace("| Programs | [`Main_Prog`](../../cli/src/main_prog.adb) | the program |\n", ""),
     ["unit main_prog is in no map: code the guide does not place"]),
    ("an instance is placed by its generic", GOOD, []),
    ("a key subprogram declared in none of the row's units",
     GOOD.replace("`Run`, `Size`", "`Run`, `Step`"),
     ["map's key subprogram Step is declared in none of Alpha"]),
    ("a qualified key subprogram its unit does not declare",
     GOOD.replace("`Gamma.Delta.Go`", "`Gamma.Delta.Stop`"),
     ["map's key subprogram Gamma.Delta.Stop is declared in none of Gamma.Delta"]),
    ("a qualified key subprogram whose unit does not exist",
     GOOD.replace("`Gamma.Delta.Go`", "`Gamma.Missing.Go`"),
     ["map's key subprogram Gamma.Missing.Go names no unit"]),
    ("a declaration commented out is not a declaration",
     GOOD, ["box X1 names Alpha.Run, not declared in Alpha",
            "map's key subprogram Run is declared in none of Alpha"]),
    ("a box that names units and has no row in its map",
     GOOD.replace('N["a box without units"]', 'X4["X4 more<br/>Alpha.Run"]'),
     ["box X4 names units but has no row in its map"]),
    ("a box of the second map after the diagram is matched",
     GOOD.replace('N["a box without units"]', 'Programs["the program<br/>Main_Prog"]'), []),
    ("a diagram with no map is not checked",
     "# Page\n\n```mermaid\nflowchart LR\n  A[\"a<br/>no such thing\"]\n```\n", []),
]


COMMENTED = {"src/alpha.ads": "package Alpha is\n   -- procedure Run;\n   function Size return Natural;\nend Alpha;\n"}


def run(page, units=None):
    with tempfile.TemporaryDirectory() as root:
        files = dict(UNITS)
        files.update(units or {})
        files["docs/guide/page.md"] = page
        for name, body in files.items():
            path = os.path.join(root, name)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                f.write(body)
        out = subprocess.run([sys.executable, "-I", CHECKER], cwd=root,
                             capture_output=True, text=True)
    reported = [line.split(": ", 1)[1] for line in out.stdout.splitlines()
                if ": " in line and not line.startswith("maps:")]
    return out.returncode, reported


def main():
    failed = 0
    for name, page, expected in CASES:
        status, reported = run(page, COMMENTED if "commented out" in name else None)
        if sorted(reported) != sorted(expected) or status != (1 if expected else 0):
            print("check-map-test: %s: expected %s, reported %s (exit %d)"
                  % (name, expected, reported, status), file=sys.stderr)
            failed = 1
    if failed:
        return 1
    print("check-map-test: %d cases, each wrong map reported, each correct one accepted"
          % len(CASES))
    return 0


if __name__ == "__main__":
    sys.exit(main())
