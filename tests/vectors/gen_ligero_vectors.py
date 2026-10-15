#!/usr/bin/env python3
"""Generator for the stage 5 (Ligero) known-answer vectors:
  merkle.txt   build <n> <leaves...> <root>
               verify <n> <root> <k> <indices...> <leaves...> <m> <path...> <ok>

Independent Python reference of the Merkle tree of IETF
draft-google-cfrg-libzk-03, Section 4.1, written from the draft's text:
the heap of 2 n digests (4.1.2), the batch opening (4.1.3) and the batch
verification (4.1.4). hashlib for SHA-256, no third-party package.

Tier 1 is Appendix B.1.1: the five leaves, the root and the batch proofs
for leaves (0, 1) and (1, 3), copied from the draft; the generator
recomputes them and aborts on any mismatch, so its reference is
anchored on the draft before it generates anything. Tier 2 is trees of
1 to 9 leaves (leaf i the SHA-256 of the string "leaf i") with batch
openings of every non-empty subset for up to 5 leaves and of the
subsets of size 1, 2, 3 and n beyond, each verified by the reference.
Negative cases, each expected to fail: an altered path digest, a path
one digest too long and one too short, a duplicate index, an index at
or above n, no index, an altered leaf, an altered root.

The geometry, Lagrange and Ligero vectors of ADR 0040 are added by the
later blocks of stage 5.

Usage: python3 -I gen_ligero_vectors.py [output-directory]
Output is deterministic (no timestamps).
"""

import hashlib
import itertools
import sys
from pathlib import Path


def sha256(data):
    return hashlib.sha256(data).digest()


# ----------------------------------------------------------------------
# Section 4.1, transcribed
# ----------------------------------------------------------------------


def merkle_heap(leaves):
    """4.1.2: layers[n .. 2n) are the leaves, layers[i] = H(layers[2i] ||
    layers[2i + 1]) for i from n - 1 down to 1; the root is layers[1]."""
    n = len(leaves)
    layers = [b""] * (2 * n)
    layers[n:2 * n] = leaves
    for i in range(n - 1, 0, -1):
        layers[i] = sha256(layers[2 * i] + layers[2 * i + 1])
    return layers


def merkle_open(layers, n, indices):
    """4.1.3: the siblings needed along the paths, from n - 1 down to 1."""
    seen = [False] * n
    on_path = [False] * (2 * n)
    for idx in indices:
        if idx >= n or seen[idx]:
            raise ValueError("bad index in opening")
        seen[idx] = True
        on_path[n + idx] = True
    for i in range(n - 1, 0, -1):
        on_path[i] = on_path[2 * i] or on_path[2 * i + 1]
    path = []
    for i in range(n - 1, 0, -1):
        if on_path[i]:
            if on_path[2 * i] and not on_path[2 * i + 1]:
                path.append(layers[2 * i + 1])
            elif not on_path[2 * i] and on_path[2 * i + 1]:
                path.append(layers[2 * i])
    return path


def merkle_verify(n, root, indices, leaves, path):
    """4.1.4: the reconstruction; False on any of the draft's failures."""
    seen = [False] * n
    on_path = [False] * (2 * n)
    for idx in indices:
        if idx >= n or seen[idx]:
            return False
        seen[idx] = True
        on_path[n + idx] = True
    for i in range(n - 1, 0, -1):
        on_path[i] = on_path[2 * i] or on_path[2 * i + 1]
    nodes = [None] * (2 * n)
    for idx, leaf in zip(indices, leaves):
        nodes[n + idx] = leaf
    pos = 0
    for i in range(n - 1, 0, -1):
        if on_path[i]:
            children = []
            for j in (2 * i, 2 * i + 1):
                if on_path[j]:
                    children.append(nodes[j])
                else:
                    if pos >= len(path):
                        return False
                    children.append(path[pos])
                    pos += 1
            nodes[i] = sha256(children[0] + children[1])
    if pos != len(path):
        return False
    return nodes[1] is not None and nodes[1] == root


# ----------------------------------------------------------------------
# Appendix B.1.1, copied from the draft
# ----------------------------------------------------------------------

B11_LEAVES = [
    "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
    "dbc1b4c900ffe48d575b5da5c638040125f65db0fe3e24494b76ea986457d986",
    "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
    "e52d9c508c502347344d8c07ad91cbd6068afc75ff6292f062a09ca381c89e71",
    "e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db",
]
B11_ROOT = "f22f4501ffd3bdffcecc9e4cd6828a4479aeedd6aa484eb7c1f808ccf71c6e76"
B11_PROOFS = {
    (0, 1): [
        "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
        "f03808f5b8088c61286d505e8e93aa378991d9889ae2d874433ca06acabcd493",
    ],
    (1, 3): [
        "e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db",
        "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
        "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
    ],
}


def fail(msg):
    print("gen_ligero_vectors: " + msg, file=sys.stderr)
    sys.exit(1)


def check_b11():
    leaves = [bytes.fromhex(h) for h in B11_LEAVES]
    layers = merkle_heap(leaves)
    if layers[1].hex() != B11_ROOT:
        fail("B.1.1 root: got " + layers[1].hex())
    for idx, want in B11_PROOFS.items():
        got = [d.hex() for d in merkle_open(layers, len(leaves), list(idx))]
        if got != want:
            fail("B.1.1 proof for %s: got %s" % (idx, got))
        if not merkle_verify(len(leaves), layers[1], list(idx),
                             [leaves[i] for i in idx],
                             [bytes.fromhex(h) for h in want]):
            fail("B.1.1 proof for %s does not verify" % (idx,))


# ----------------------------------------------------------------------
# Output
# ----------------------------------------------------------------------


def hx(b):
    return b.hex()


def verify_line(n, root, indices, leaves, path, ok):
    return ("verify %d %s %d %s %s %d %s %d"
            % (n, hx(root), len(indices),
               " ".join(str(i) for i in indices),
               " ".join(hx(l) for l in leaves),
               len(path), " ".join(hx(p) for p in path), 1 if ok else 0)
            ).replace("  ", " ")


def tier2_subsets(n):
    if n <= 5:
        sizes = range(1, n + 1)
    else:
        sizes = [1, 2, 3, n]
    for k in sizes:
        for subset in itertools.combinations(range(n), k):
            yield list(subset)


def main():
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent
    out.mkdir(parents=True, exist_ok=True)
    check_b11()

    lines = [
        "# Known-answer vectors for the Merkle tree of draft Section 4.1,"
        " Longfellow ZK stage 5.",
        "# Generated by gen_ligero_vectors.py (this directory); do not"
        " edit by hand.",
        "#",
        "# Digests as 64 hex digits in memory order. Lines:",
        "#   build <n> <n leaves> <root>",
        "#       the heap of the leaves has this root (4.1.2)",
        "#   verify <n> <root> <k> <k indices> <k leaves> <m> <m path"
        " digests> <ok>",
        "#       batch verification (4.1.4) succeeds (1) or fails (0)",
        "#",
        "# Section A: Appendix B.1.1, copied from the draft and recomputed",
        "#   by the generator: the five leaves, the root, the proofs for",
        "#   leaves (0, 1) and (1, 3).",
    ]
    leaves = [bytes.fromhex(h) for h in B11_LEAVES]
    root = bytes.fromhex(B11_ROOT)
    lines.append("build 5 %s %s" % (" ".join(B11_LEAVES), B11_ROOT))
    for idx, proof in B11_PROOFS.items():
        lines.append(verify_line(5, root, list(idx), [leaves[i] for i in idx],
                                 [bytes.fromhex(h) for h in proof], True))
    lines.append("#")
    lines.append("# Section B: trees of 1 to 9 leaves (leaf i = SHA-256 of"
                 " \"leaf i\"),")
    lines.append("#   batch openings of every non-empty subset up to 5"
                 " leaves and of the")
    lines.append("#   subsets of size 1, 2, 3 and n beyond, from the"
                 " opening of 4.1.3.")
    n_build = n_verify = 0
    trees = {}
    for n in range(1, 10):
        lv = [sha256(("leaf %d" % i).encode()) for i in range(n)]
        layers = merkle_heap(lv)
        trees[n] = (lv, layers)
        lines.append("build %d %s %s" % (n, " ".join(hx(l) for l in lv),
                                         hx(layers[1])))
        n_build += 1
        for subset in tier2_subsets(n):
            path = merkle_open(layers, n, subset)
            if not merkle_verify(n, layers[1], subset,
                                 [lv[i] for i in subset], path):
                fail("tree of %d, subset %s does not verify" % (n, subset))
            lines.append(verify_line(n, layers[1], subset,
                                     [lv[i] for i in subset], path, True))
            n_verify += 1
    lines.append("#")
    lines.append("# Section C: negative cases on the tree of 7 leaves, subset"
                 " (1, 4, 6):")
    lines.append("#   an altered path digest, a path one digest too long, one"
                 " too short,")
    lines.append("#   a duplicate index, an index at n, no index, an altered"
                 " leaf, an")
    lines.append("#   altered root; each must fail.")
    lv, layers = trees[7]
    root = layers[1]
    subset = [1, 4, 6]
    path = merkle_open(layers, 7, subset)
    sub_leaves = [lv[i] for i in subset]
    altered = bytes([path[0][0] ^ 1]) + path[0][1:]
    cases = [
        (7, root, subset, sub_leaves, [altered] + path[1:]),
        (7, root, subset, sub_leaves, path + [path[0]]),
        (7, root, subset, sub_leaves, path[:-1]),
        (7, root, [1, 4, 4], [lv[1], lv[4], lv[4]],
         merkle_open(layers, 7, [1, 4])),
        (7, root, [1, 7], [lv[1], lv[0]], merkle_open(layers, 7, [1])),
        (7, root, [], [], []),
        (7, root, subset, [lv[1], lv[5], lv[6]], path),
        (7, bytes([root[0] ^ 1]) + root[1:], subset, sub_leaves, path),
    ]
    for n, r, idx, lvs, p in cases:
        if merkle_verify(n, r, idx, lvs, p):
            fail("negative case %s verifies" % (idx,))
        lines.append(verify_line(n, r, idx, lvs, p, False))
    (out / "merkle.txt").write_text("\n".join(lines) + "\n")
    print("gen_ligero_vectors: merkle.txt with %d build, %d verify and %d"
          " negative cases; B.1.1 reproduced" % (n_build + 1, n_verify + 2,
                                                 len(cases)))


if __name__ == "__main__":
    main()
