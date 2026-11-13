#!/usr/bin/env python3
"""The performance matrix by step, from the attributions of
attribute-steps.py.

Takes the three time attributions of one program (three profiles), its
heap attribution at the peak, and the totals of the performance page
(the median wall time of three runs of the release build, and the peak
heap under heapshim). Prints one Markdown row per step: its class and
what could run in parallel inside it, the share of
the samples (the median of the three profiles) and that share of the
total time, per circuit; the bytes alive at the peak that the step
allocated, and their share of the peak. Then the rows "the program"
and "not attributed", so that what the attribution misses is printed
beside what it finds.

Usage: step-matrix.py TOTAL_SECONDS PEAK_BYTES HEAP.tsv TIME1.tsv TIME2.tsv TIME3.tsv
"""

import collections
import statistics
import sys


#  The class of each step (D6 and D7 of the performance page) and what
#  could run in parallel inside it.
CLASS = {
    "PS1": ("[D]", ""), "PS2": ("[D]", ""),
    "PS3": ("[P]", "the two witnesses"),
    "PS4": ("[D]", ""),
    "PS5": ("[P]", "the rows of the encoding, the nodes of one level of the tree"),
    "PS6": ("[T]", ""),
    "PS7": ("[D]", "the wires of one layer"),
    "PS8": ("[T]", "the terms of a round, the binding of a round"),
    "PS9": ("[D]", ""),
    "PS10": ("[P]", "the combined rows, the opened columns"),
    "PS11": ("[D]", ""),
    "VS1": ("[D]", ""), "VS2": ("[T]", ""), "VS3": ("[T]", ""), "VS4": ("[T]", ""),
    "VS5": ("[P]", "the terms of a layer"),
    "VS6": ("[D]", ""),
    "VS7": ("[P]", "the opened columns and their paths"),
    "VS8": ("[D]", ""),
}


def read(path):
    rows = collections.OrderedDict()
    for line in open(path):
        f = line.rstrip("\n").split("\t")
        if f[0] in ("root", "total", "object"):
            continue
        rows[(f[0], f[1])] = (int(f[2]), float(f[3]))
    return rows


def main(argv):
    if len(argv) != 7:
        print(__doc__, file=sys.stderr)
        return 2
    total, peak = float(argv[1]), int(argv[2])
    heap = read(argv[3])
    times = [read(p) for p in argv[4:7]]
    steps = []
    for t in times + [heap]:
        for step, _ in t:
            if step not in steps:
                steps.append(step)
    #  Every step of the program, in order, those below one sample too.
    prefix = "PS" if any(s.startswith("PS") for s in steps) else "VS"
    count = 11 if prefix == "PS" else 8
    named = ["%s%d" % (prefix, i) for i in range(1, count + 1)]
    merged = [s for s in steps if "-" in s]
    steps = named + merged + ["program", "not attributed"]
    print("| Step | Class | Parallel inside | Time, hash | Time, signature | Time, not per circuit | Share of the samples | Heap alive at the peak | Share of the peak |")
    print("|---|---|---|---|---|---|---|---|---|")
    for step in steps:
        cells, share_all = [], 0.0
        for c in ("hash", "sig", "both"):
            share = statistics.median(t.get((step, c), (0, 0.0))[1] for t in times)
            share_all += share
            cells.append("%.2f s" % (share * total) if share else "")
        b = sum(heap.get((step, c), (0, 0.0))[0] for c in ("hash", "sig", "both"))
        cls, inside = CLASS.get(step, ("", ""))
        print("| %s | %s | %s | %s | %s | %s | %.1f %% | %s | %s |" % (
            step, cls, inside, cells[0], cells[1], cells[2], 100 * share_all,
            "{:,} B".format(b) if b else "", "%.1f %%" % (100 * b / peak) if b else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
