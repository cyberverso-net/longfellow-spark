#!/usr/bin/env python3
"""Check the relative links of the repository's Markdown (make lint).

Reads every Markdown file under docs/ and the repository's README.md,
or the files given on the command line, and checks each relative link
and image:

- the target file or directory exists, with the same case as written
  (GitHub's paths are case-sensitive, some file systems are not);
- when the link has an anchor and the target is a Markdown file, the
  target has a heading, or an explicit <a id> or <a name>, with that
  anchor, computed as GitHub computes it.

Links with a scheme (https:, mailto: and so on) are not followed. Code
spans and fenced code blocks are not read, so a link written as an
example is not checked. Each failure is printed as file:line: link and
the reason; the exit status is 1 when there is one, 0 otherwise.

Run from the repository root:  python3 -I scripts/check-links.py
"""

import html
import os
import re
import sys
from urllib.parse import unquote, urlsplit

#  Links that are wrong on purpose and stay: the body of an Accepted
#  record is immutable (ADR 0042), so a wrong link in it is corrected by
#  a note in its Status line, not in place. Each entry is the file, the
#  link as written, and where the correction is. An entry whose link is
#  no longer in its file is itself a failure, so the list cannot go stale.
KNOWN = {
    ("docs/adr/0085-prover-and-verifier-in-two-phases.md",
     "0049-phase-c-scope-prover-and-exit-criterion.md"):
        "corrected by the note of 2026-11-11 in the record's Status",
}

FENCE = re.compile(r"^ {0,3}(`{3,}|~{3,})")
CODE_SPAN = re.compile(r"(`+)(.+?)\1", re.S)
DEST = r"\(\s*(<[^>]*>|(?:[^\s()\\]|\\.|\([^\s()]*\))+)(?:\s+(?:\"[^\"]*\"|'[^']*'))?\s*\)"
INLINE = re.compile(r"!?\[(?:[^\[\]]|\[[^\[\]]*\])*\]" + DEST)
IMAGE = re.compile(r"!\[[^\[\]]*\]" + DEST)
REFDEF = re.compile(r"^ {0,3}\[[^\]]+\]:\s*(<[^>]*>|\S+)", re.M)
HEADING = re.compile(r"^ {0,3}(#{1,6})\s+(.*?)\s*#*\s*$")
SETEXT = re.compile(r"^ {0,3}(=+|-+)\s*$")
NOT_PARAGRAPH = re.compile(r"^ {0,3}([#>|]|[-*+] |\d+[.)] |(=+|-+)\s*$)|^\s*$")
HTML_ANCHOR = re.compile(r"<a\s+(?:id|name)\s*=\s*[\"']([^\"']+)[\"']", re.I)
SCHEME = re.compile(r"^[A-Za-z][A-Za-z0-9+.-]*:")


def blank(match):
    """Replace a match by spaces, keeping its newlines and offsets."""
    return re.sub(r"[^\n]", " ", match.group(0))


def unfenced(text):
    """The text with its fenced code blocks blanked out, lines kept.

    A block closes on a line of the same character, at least as long
    as the opening fence and with nothing else on it."""
    out = []
    fence = None
    for line in text.split("\n"):
        m = FENCE.match(line)
        if fence is None and m:
            fence = m.group(1)
            out.append("")
        elif fence is not None:
            if (m and m.group(1)[0] == fence[0] and len(m.group(1)) >= len(fence)
                    and not line.strip(fence[0] + " ")):
                fence = None
            out.append("")
        else:
            out.append(line)
    return "\n".join(out)


def prose(text):
    """The text with fenced code blocks and code spans blanked out."""
    return CODE_SPAN.sub(blank, unfenced(text))


def visible(part):
    """The rendered text of a heading's part outside code spans: links
    and images by their text, no HTML tags, entities decoded, and no
    emphasis delimiters (an underscore inside a word stays)."""
    part = re.sub(r"!?\[([^\]]*)\]\([^)]*\)", r"\1", part)
    part = re.sub(r"<[^>]+>", "", part)
    part = re.sub(r"(?<![^\W_])_+|_+(?![^\W_])", "", part)
    return html.unescape(part.replace("*", ""))


def slug(heading):
    """GitHub's anchor for a heading's text: the visible text, code
    spans as written, lower case, punctuation removed, spaces as
    hyphens."""
    pieces = re.split(r"(`+)(.+?)\1", heading)
    text = "".join(visible(p) if i % 3 == 0 else (p if i % 3 == 2 else "")
                   for i, p in enumerate(pieces))
    text = text.strip().lower()
    text = re.sub(r"[^\w\- ]", "", text)
    return text.replace(" ", "-")


_anchors = {}


def anchors(path):
    """Every anchor of a Markdown file, duplicates numbered as GitHub does."""
    if path not in _anchors:
        with open(path, encoding="utf-8") as f:
            text = f.read()
        #  github-slugger: a slug already taken gets the next free suffix
        #  of its base, so "Alpha", "Alpha-1", "Alpha" give alpha,
        #  alpha-1, alpha-2.
        occurrences = {}
        found = set(HTML_ANCHOR.findall(prose(text)))
        lines = unfenced(text).split("\n")
        for i, line in enumerate(lines):
            h = HEADING.match(line)
            #  A Setext heading: a one-line paragraph underlined by = or -.
            if not h and i + 1 < len(lines) and SETEXT.match(lines[i + 1]) \
                    and not NOT_PARAGRAPH.match(line) \
                    and (i == 0 or not lines[i - 1].strip()):
                heading = line.strip()
            elif h:
                heading = h.group(2)
            else:
                continue
            if heading:
                base = slug(heading)
                result = base
                while result in occurrences:
                    occurrences[base] += 1
                    result = "%s-%d" % (base, occurrences[base])
                occurrences[result] = 0
                found.add(result)
        _anchors[path] = found
    return _anchors[path]


def exists_with_case(path):
    """True when every component of path exists with this exact case."""
    if not os.path.exists(path):
        return False
    head = path
    while True:
        parent, name = os.path.split(head)
        if name in ("", ".", ".."):
            return True
        if name not in os.listdir(parent or "."):
            return False
        head = parent


def check(path):
    """The failures of one file, as (line, link, reason)."""
    with open(path, encoding="utf-8") as f:
        text = prose(f.read())
    #  A linked image, [![alt](image)](link), is two links: the outer
    #  match holds the image, which IMAGE finds on its own.
    links = {(m.start(1), m.group(1)) for m in INLINE.finditer(text)}
    links |= {(m.start(1), m.group(1)) for m in IMAGE.finditer(text)}
    links |= {(m.start(1), m.group(1)) for m in REFDEF.finditer(text)}
    failures = []
    for offset, link in sorted(links):
        link = link[1:-1] if link.startswith("<") else re.sub(r"\\(.)", r"\1", link)
        if SCHEME.match(link):
            continue
        line = text.count("\n", 0, offset) + 1
        if (os.path.normpath(path), link) in KNOWN:
            continue
        parts = urlsplit(link)
        target, anchor = unquote(parts.path), unquote(parts.fragment)
        if target.startswith("/"):
            resolved = os.path.normpath("." + target)
        elif target:
            resolved = os.path.normpath(os.path.join(os.path.dirname(path), target))
        else:
            resolved = path
        if not exists_with_case(resolved):
            failures.append((line, link, "no such file"))
        elif anchor and resolved.endswith(".md") and os.path.isfile(resolved):
            if anchor not in anchors(resolved):
                failures.append((line, link, "no such anchor in " + resolved))
    return failures


def markdown_files():
    files = ["README.md"]
    for root, dirs, names in os.walk("docs"):
        dirs.sort()
        files += [os.path.join(root, n) for n in sorted(names) if n.endswith(".md")]
    return files


def main(argv):
    files = argv[1:] or markdown_files()
    status = 0
    for path in files:
        for line, link, reason in check(path):
            print("%s:%d: %s: %s" % (path, line, link, reason))
            status = 1
    for (path, link), why in KNOWN.items():
        if argv[1:]:
            break
        if not os.path.isfile(path) or link not in open(path, encoding="utf-8").read():
            print("%s: known link %s (%s) is no longer there; remove it from KNOWN"
                  % (path, link, why))
            status = 1
    if status == 0:
        print("links: %d files, every relative link resolves" % len(files))
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv))
