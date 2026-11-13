#!/usr/bin/env python3
"""The tests of scripts/check-links.py, on temporary trees.

Each case writes a small tree of Markdown files, runs the checker on
it and compares the links it reports with the links expected, so that
a valid link that is refused fails as surely as a broken link that is
let through. Run by the lint step of make check; needs only Python 3.
"""

import os
import subprocess
import sys
import tempfile

CHECKER = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check-links.py")

FENCE4 = "````\n```\n## Ghost heading\n````\n"

CASES = [
    ("files, directories, case and the repository root",
     {"docs/a.md": "[ok](b.md) [dir](../docs/) [top](/README.md) [web](https://x.invalid/c.md)\n"
                   "[mail](mailto:a@x.invalid) [missing](c.md) [case](B.md)\n",
      "docs/b.md": "# B\n", "README.md": "# Readme\n"},
     ["c.md", "B.md"]),
    ("anchors, duplicates numbered as GitHub numbers them",
     {"docs/a.md": "# Alpha\n## Alpha-1\n## Alpha\n## `Code` and [a link](a.md) here\n"
                   "[1](#alpha) [2](#alpha-1) [3](#alpha-2) [4](#code-and-a-link-here)\n"
                   "[5](#alpha-3) [6](b.md#nope) [7](b.md#b)\n",
      "docs/b.md": "# B\n"},
     ["#alpha-3", "b.md#nope"]),
    ("queries and percent-encoding",
     {"docs/a.md": "# Café\n[1](b.md?plain=1) [2](b.md?plain=1#b) [3](#caf%C3%A9) [4](b%20c.md)\n"
                   "[5](b.md?plain=1#nope)\n",
      "docs/b.md": "# B\n", "docs/b c.md": "# C\n"},
     ["b.md?plain=1#nope"]),
    ("images, linked images and reference definitions",
     {"docs/a.md": "[![badge](missing.svg)](b.md) ![img](b.md) [ref]\n\n[ref]: gone.md\n",
      "docs/b.md": "# B\n"},
     ["missing.svg", "gone.md"]),
    ("headings by their rendered text, and Setext headings",
     {"docs/a.md": "# _Alpha_\n# A &amp; B\n# `snake_case` and snake_case\n\nOverview\n========\n\n"
                   "Details\n-------\n\n- item\n---\n"
                   "[1](#alpha) [2](#a--b) [3](#snake_case-and-snake_case) [4](#overview)\n"
                   "[5](#details) [6](#_alpha_) [7](#a-amp-b) [8](#item)\n"},
     ["#_alpha_", "#a-amp-b", "#item"]),
    ("balanced and escaped parentheses in a destination",
     {"docs/a.md": "[1](guide(v2).md) [2](guide\\(v2\\).md) [3](gone(v2).md)\n",
      "docs/guide(v2).md": "# G\n"},
     ["gone(v2).md"]),
    ("code is not read, for links or for anchors",
     {"docs/a.md": "`[x](none.md)` and `<a id=\"ghost\"></a>`\n```\n[y](none.md)\n<a id=\"ghost2\"></a>\n```\n"
                   + FENCE4 + "<a id=\"real\"></a>\n"
                   "[1](#ghost) [2](#ghost2) [3](#ghost-heading) [4](#real)\n"},
     ["#ghost", "#ghost2", "#ghost-heading"]),
]


def run(files):
    with tempfile.TemporaryDirectory() as root:
        for name, body in files.items():
            path = os.path.join(root, name)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "w", encoding="utf-8") as f:
                f.write(body)
        names = sorted(n for n in files if n.endswith(".md") and n != "README.md")
        out = subprocess.run([sys.executable, "-I", CHECKER] + names, cwd=root,
                             capture_output=True, text=True)
    reported = [line.split(": ")[1] for line in out.stdout.splitlines() if ": " in line
                and not line.startswith("links:")]
    return out.returncode, reported


def main():
    failed = 0
    for name, files, expected in CASES:
        status, reported = run(files)
        if sorted(reported) != sorted(expected) or status != (1 if expected else 0):
            print("check-links-test: %s: expected %s, reported %s (exit %d)"
                  % (name, expected, reported, status), file=sys.stderr)
            failed = 1
    if failed:
        return 1
    print("check-links-test: %d cases, each broken link reported, each valid one accepted"
          % len(CASES))
    return 0


if __name__ == "__main__":
    sys.exit(main())
