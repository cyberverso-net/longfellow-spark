#!/usr/bin/env python3
"""List the code outside SPARK in src/ and check that each has a register row.

GNATprove does not analyse a body under SPARK_Mode Off: it takes the
subprogram's contract as given. Such a body is an assumption of the
proof, and every one must be listed in the register of the trusted base
(docs/guide/trusted-base.md). This script finds each one in src/:

- an aspect SPARK_Mode => Off on a subprogram or a package: that
  subprogram or package, named by its full name (the unit, the packages
  that enclose it, then its own name: Unit.Subprogram,
  Unit.Helpers.Subprogram);
- a pragma SPARK_Mode (Off): the unit, the package or the subprogram
  whose declarations it starts, named the same way; before the unit, the
  whole unit.

The text is read as Ada's lexer reads it: comments are removed, and
string and character literals are blanked, so that "--" or "SPARK_Mode"
inside a literal counts for nothing. The aspect and the pragma are then
found across line breaks. The scopes are followed from the keywords
that open them (a package, a subprogram body, a block) to the end that
closes them. A part outside SPARK inside a subprogram body or a block
has no name the register could use, and is refused; so is a file whose
scopes cannot be followed.

The script prints the list, and fails when no row of the register's
tables (a line that starts with "| ") names the part, qualified and in
backquotes, in its column Item: a name in the other columns, such as
"What depends on it", does not register an assumption.
Each failure is printed with its file and line; the exit status is 1
when there is one.

Run from the repository root:  python3 -I scripts/check-spark-off.py
"""

import os
import re
import sys

#  An identifier, possibly expanded (Gadgets.Bits), a compound
#  delimiter that matters here, or any other character.
TOKEN = re.compile(r"[A-Za-z][\w]*(?:\.[A-Za-z][\w]*)*|=>|<>|\S")
WORD = re.compile(r"[A-Za-z]")

#  The words after "end" that close a construct which opens no scope.
END_KEYWORDS = {"if", "loop", "case", "record", "select", "return"}
#  The words after "is" that make a declaration something other than a
#  body: an instance, a stub, a null or abstract subprogram, an
#  expression function (its expression in parentheses or, for an
#  aggregate, in brackets), a formal default.
NOT_A_BODY = {"new", "separate", "null", "abstract", "(", "[", "<>"}


#  Ada's reserved words (RM 2.9) after which an apostrophe starts a
#  character literal: "when '(' =>", "in 'a' .. 'z'". "all" is left out:
#  after it the apostrophe is an attribute (P.all'Address).
RESERVED = set("""abort abs abstract accept access aliased and array at begin body
case constant declare delay delta digits do else elsif end entry exception
exit for function generic goto if in interface is limited loop mod new not
null of or others out overriding package parallel pragma private procedure
protected raise range record rem renames requeue return reverse select
separate some subtype synchronized tagged task terminate then type until use
when while with xor""".split())


class Refused(Exception):
    """The scopes of a file cannot be followed."""


def blank_literals(line):
    """The line without its comment, its string and character literals
    replaced by spaces of the same length (Ada, RM 2.4 to 2.7)."""
    out = []
    i = 0
    n = len(line)
    prev = ""   # the last significant character outside a literal
    while i < n:
        c = line[i]
        if c == '"':
            j = i + 1
            while True:
                if j >= n:
                    raise Refused("a string literal not closed on its line")
                if line[j] == '"':
                    if j + 1 < n and line[j + 1] == '"':
                        j += 2
                        continue
                    break
                j += 1
            out.append('"' + " " * (j - i - 1) + '"')
            prev = '"'
            i = j + 1
            continue
        if c == "'":
            #  A character literal, unless the apostrophe follows a name
            #  or a closing parenthesis: then it is an attribute or a
            #  qualified expression (Character'('-') is both). A reserved
            #  word is not a name.
            word = re.search(r"[A-Za-z_][\w]*$", "".join(out).rstrip())
            after_name = prev != "" and (prev in "_)" or (prev.isalnum() and not (
                word and word.group(0).lower() in RESERVED)))
            if not after_name and i + 2 < n and line[i + 2] == "'":
                out.append("' '")
                prev = "'"
                i += 3
                continue
            out.append(c)
            prev = c
            i += 1
            continue
        if c == "-" and i + 1 < n and line[i + 1] == "-":
            break
        out.append(c)
        if not c.isspace():
            prev = c
        i += 1
    return "".join(out)


def tokens(lines):
    """The tokens of the text, each with its line number (from 1),
    lower-cased words compared, original spelling kept."""
    for number, text in enumerate(lines, 1):
        for m in TOKEN.finditer(text):
            yield number, m.group(0)


class Frame:
    def __init__(self, kind, name):
        self.kind = kind          # "package", "subprogram" or "block"
        self.name = name          # None for a block
        self.in_statements = False


def full_name(frames, name):
    """The full name of a declaration named name in the scopes frames,
    or None when one of them is a subprogram body or a block."""
    parts = []
    for f in frames:
        if f.kind != "package":
            return None
        parts.append(f.name)
    parts.append(name)
    return ".".join(parts)


def off_parts(path):
    """The (line number, full name) of each part of a file outside SPARK;
    the full name is None for a part nested in a subprogram body or a
    block. Raises Refused when the scopes cannot be followed."""
    with open(path, encoding="utf-8") as f:
        lines = []
        for number, line in enumerate(f.read().splitlines(), 1):
            try:
                lines.append(blank_literals(line))
            except Refused as e:
                raise Refused("line %d: %s" % (number, e))
    toks = list(tokens(lines))
    low = [t.lower() for _, t in toks]
    frames = []
    parts = []
    unit = None
    #  The declaration being read, from its name to its "is" or ";":
    #  (kind, name, its full name or None, line).
    decl = None
    depth = 0
    k = 0
    while k < len(toks):
        line, tok = toks[k]
        w = low[k]
        nxt = low[k + 1] if k + 1 < len(toks) else ""
        if tok in ("(", "["):
            depth += 1
        elif tok in (")", "]"):
            depth -= 1
        if depth > 0:
            k += 1
            continue
        if w in ("package", "procedure", "function") and (k == 0 or low[k - 1] not in ("access", "with")):
            j = k + 1
            kind = "package" if w == "package" else "subprogram"
            if w == "package" and j < len(toks) and low[j] == "body":
                j += 1
            #  The name, or the blanked operator symbol of an operator ("+").
            if j < len(toks) and (WORD.match(toks[j][1]) or toks[j][1] == '"'):
                name = toks[j][1]
                if unit is None and not frames:
                    unit = name
                decl = (kind, name, full_name(frames, name), line)
                k = j + (2 if name == '"' else 1)
                continue
        if w == "spark_mode":
            off_aspect = nxt == "=>" and k + 2 < len(toks) and low[k + 2] == "off"
            off_pragma = (k > 0 and low[k - 1] == "pragma" and nxt == "("
                          and k + 2 < len(toks) and low[k + 2] == "off")
            if off_aspect:
                if decl is None:
                    raise Refused("line %d: an aspect SPARK_Mode => Off on no "
                                  "package or subprogram" % line)
                parts.append((line, decl[2]))
            elif off_pragma:
                if not frames:
                    parts.append((line, "<unit>"))
                else:
                    top = frames[-1]
                    if top.kind == "block" or top.in_statements:
                        parts.append((line, None))
                    else:
                        parts.append((line, full_name(frames[:-1], top.name)))
        if tok == ";":
            decl = None
        elif w == "is" and decl is not None:
            if nxt not in NOT_A_BODY:
                frames.append(Frame(decl[0], decl[1]))
            decl = None
        elif w == "declare":
            frames.append(Frame("block", None))
        elif w == "begin":
            if frames and not frames[-1].in_statements:
                frames[-1].in_statements = True
            else:
                f = Frame("block", None)
                f.in_statements = True
                frames.append(f)
        elif w == "end" and nxt not in END_KEYWORDS:
            if not frames:
                raise Refused("line %d: an end that closes no scope" % line)
            f = frames.pop()
            if nxt not in (";", "") and f.name is not None and nxt != f.name.lower():
                raise Refused("line %d: end %s closes %s" % (line, toks[k + 1][1], f.name))
        k += 1
    if frames:
        raise Refused("%s %s is not closed" % (frames[-1].kind, frames[-1].name or ""))
    if depth != 0:
        raise Refused("the parentheses or brackets do not balance")
    #  A pragma before the unit applies to the whole unit.
    return [(line, unit if name == "<unit>" else name) for line, name in parts]


def register_items(path):
    """The column Item of every row of the register's tables."""
    items = []
    with open(path, encoding="utf-8") as f:
        for line in f.read().splitlines():
            if line.startswith("| "):
                cells = line.split("|")
                if len(cells) > 2:
                    items.append(cells[2])
    return items


def named(items, name):
    key = "`%s`" % name
    return any(key in item for item in items)


def main(root):
    rows = register_items(os.path.join(root, "docs", "guide", "trusted-base.md"))
    src = os.path.join(root, "src")
    failures = 0
    found = 0
    for base in sorted(os.listdir(src)):
        if not base.endswith((".ads", ".adb")):
            continue
        path = os.path.join(src, base)
        try:
            parts = off_parts(path)
        except Refused as e:
            print("src/%s: the scopes cannot be followed (%s); the lint refuses "
                  "the file" % (base, e))
            failures += 1
            continue
        for line, name in parts:
            found += 1
            if name is None:
                print("src/%s:%d: a part outside SPARK inside a subprogram body or "
                      "a block has no name a register row can give; move it to a "
                      "package" % (base, line))
                failures += 1
            elif named(rows, name):
                print("spark-off: src/%s:%d %s" % (base, line, name))
            else:
                print("src/%s:%d: %s is outside SPARK and has no row in "
                      "docs/guide/trusted-base.md" % (base, line, name))
                failures += 1
    print("spark-off: %d parts outside SPARK, %d failures"
          % (found, failures))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1] if len(sys.argv) > 1 else "."))
