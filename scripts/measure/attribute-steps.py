#!/usr/bin/env python3
"""Attribute a profile to the steps of the guide's system map.

The steps (PS1 to PS11 for the prover, VS1 to VS8 for the verifier) are
those of docs/guide/system-map.md. Each step has root subprograms,
listed below for this project and for upstream. A sample of the time
profile, or a block of the heap profile alive at the peak, belongs to
the step whose root is the nearest one on its call stack, walking from
the innermost frame out; the fields, the hashes and the other units
used by every step are leaves and take the step of the root above
them. A root may require an ancestor (the linear constraints are PS9
only inside the proof, not inside the commitment). The circuit is told
apart by the instance in the root's name: GF(2^128) for the hash
circuit, P-256 for the signature circuit. What has no root on its stack
is reported as not attributed, and the program's own frames as the
program; both shares are printed.

Inputs:
  time  PERF_SCRIPT          the text of `perf script` with call chains
  heap  HEAPPROF_DUMP BIN    a dump of scripts/measure/heapprof.c, its
                             addresses resolved with addr2line -f -i in
                             the modules of its map lines

Usage:
  attribute-steps.py ours|upstream prove|verify time PERF_SCRIPT
  attribute-steps.py ours|upstream prove|verify heap HEAPPROF_DUMP

Output: one line per step and circuit, tab-separated: the step, the
circuit (hash, sig or both), the samples or bytes, the share; then the
lines "program" and "not attributed"; then, for each root, its own
samples or bytes, so that a root never seen shows as zero; then, for a
heap profile, the objects: the bytes alive at the peak by step and by
the first subprogram of the program's own code that allocated them.
"""

import collections
import re
import subprocess
import sys

#  (pattern, step, required ancestor or None). Ada names as GNAT emits
#  them, lower case with "__" between units; the instance token decides
#  the circuit.
INST = r"[a-z0-9_]*?(?:gf2_128|p256)"
OURS = {
    "prove": [
        (r"^mdoc_cli__load_circuits$", "PS1", None),
        (r"^circuit_reader_" + INST + r"__(read_packed|load|read)$", "PS1", None),
        (r"^mdoc_prover_cli__(hash_ok|sig_ok|parts_fit|max_len)$", "PS1", None),
        (r"^mdoc_parse__parse$", "PS2", None),
        (r"^mdoc_witness__(hash_witness|sig_witness)$", "PS3", None),
        (r"^mdoc_prover_cli__(prove_profile|prove_mdoc)$", "PS3", None),
        (r"^sumcheck_prover_cli_" + INST + r"__sample_pads$", "PS4", None),
        (r"^ligero_prover_cli_" + INST + r"__(commit|commit_row|hash_leaves)$", "PS5", None),
        (r"^zk_prover_cli_" + INST + r"__commit$", "PS5", None),
        (r"^mdoc_mac__legacy_tags$", "PS6", None),
        (r"^mdoc_inputs__(hash_inputs|sig_inputs)$", "PS6", None),
        (r"^mdoc_proof__write_tags$", "PS6", None),
        (r"^mdoc_prover_cli__prove$", "PS6", None),
        (r"^packed_eval_" + INST + r"__eval_circuit$", "PS7", None),
        (r"^zk_prover_cli_" + INST + r"__prove_committed$", "PS7", None),
        (r"^sumcheck_transcript_" + INST + r"__write_sumcheck_statement$", "PS8", None),
        (r"^sumcheck_prover_cli_" + INST + r"__prove$", "PS8", None),
        (r"^sumcheck_verifier_" + INST + r"__(verifier_core|input_constraint)$", "PS9", None),
        (r"^sumcheck_prover_cli_" + INST + r"__lqc_triples$", "PS9",
         r"^zk_prover_cli_" + INST + r"__prove_committed$"),
        (r"^ligero_prover_cli_" + INST + r"__prove$", "PS10", None),
        (r"^proof_writer_" + INST + r"__(write_proof|put_slot)$", "PS11", None),
        (r"^mdoc_cli__write_file$", "PS11", None),
    ],
    "verify": [
        (r"^mdoc_cli__load_circuits$", "VS1", None),
        (r"^circuit_reader_" + INST + r"__(read_packed|load|read)$", "VS1", None),
        (r"^zk_verifier_" + INST + r"__receive$", "VS2", None),
        (r"^device_auth__digest$", "VS3", None),
        (r"^mdoc_inputs__(hash_inputs|sig_inputs)$", "VS3", None),
        (r"^mdoc_verifier__verify$", "VS3", None),
        (r"^sumcheck_transcript_" + INST + r"__replay_from_statement$", "VS4", None),
        (r"^zk_verifier_" + INST + r"__verify_received$", "VS4", None),
        (r"^sumcheck_verifier_" + INST + r"__(verifier_core|input_constraint)$", "VS6", None),
        (r"^zk_verifier_" + INST + r"__bound_quads$", "VS5", None),
        (r"^ligero_verifier_" + INST + r"__(verify|build_tables)$", "VS7", None),
        (r"^lagrange_" + INST + r"__build$", "VS7", None),
        (r"^mdoc_verifier__verify_profile$", "VS8", None),
    ],
}
OURS_PROGRAM = r"^(_ada_)?longfellow_(prove|verify)_mdoc$|^mdoc_cli__|^main$"

#  Upstream at d5e6be7, the driver heap_v7.rs, symbols demangled in the
#  v0 scheme so that the field type of a monomorphised function shows.
UP_INST = r".*"
UPSTREAM = {
    "prove": [
        (r"mdoc_zk_artifacts::load_circuit", "PS1", None),
        (r"^ZSTD_|^HUF_|^FSE_", "PS1", None),
        (r"core_proto::reader::lfc2::|mdoc_zk_artifacts::|mdoc_zk_runtime::proto::decompress_circuits", "PS1", None),
        (r"mdoc_zk_runtime::provider::materialize", "PS1", None),
        (r"::parse_mdoc\b", "PS2", None),
        (r"mdoc_zk_runtime::.*push_witness_(hash|sig)\b", "PS3", None),
        (r"mdoc_zk_runtime::.*generate_mac_ap\b", "PS3", None),
        (r"runtime_zk::prover::new_pad", "PS4", None),
        (r"runtime_ligero::prover::.*::commit\b", "PS5", None),
        (r"runtime_zk::prover::.*::commit\b", "PS5", None),
        (r"mdoc_zk_runtime::.*push_macs\b", "PS6", None),
        (r"mdoc_zk_runtime::.*push_input_(hash|sig)\b", "PS6", None),
        (r"runtime_sumcheck::.*eval_circuit", "PS7", None),
        (r"runtime_zk::prover::.*::prove\b", "PS7", None),
        (r"runtime_sumcheck::prover::prove_core", "PS8", None),
        (r"write_sumcheck_statement", "PS8", None),
        (r"symbolic_sumcheck_verifier_core", "PS9", None),
        (r"runtime_ligero::prover::.*::prove\b", "PS10", None),
        (r"::write\b", "PS11", r"mdoc_zk_runtime::prover::run_mdoc_prover_inner"),
    ],
    "verify": [
        (r"mdoc_zk_artifacts::load_circuit", "VS1", None),
        (r"^ZSTD_|^HUF_|^FSE_", "VS1", None),
        (r"core_proto::reader::lfc2::|mdoc_zk_artifacts::|mdoc_zk_runtime::proto::decompress_circuits", "VS1", None),
        (r"mdoc_zk_runtime::provider::materialize", "VS1", None),
        (r"MdocProof.*::read\b", "VS2", None),
        (r"mdoc_zk_runtime::verifier::run_mdoc_verifier_inner", "VS3", None),
        (r"mdoc_zk_runtime::.*(push_macs|push_input_(hash|sig))\b", "VS3", None),
        (r"write_sumcheck_statement", "VS4", None),
        (r"symbolic_sumcheck_verifier_core", "VS5-VS6", None),
        (r"runtime_zk::verifier::.*::verify\b", "VS4", None),
        (r"runtime_ligero::verifier::.*::verify\b", "VS7", None),
    ],
}
UP_PROGRAM = r"(heap_v7::main|^main$|mdoc_zk_runtime::prover::run_mdoc_prover_inner)"


def circuit_of(name, side):
    if side == "ours":
        if "gf2_128" in name:
            return "hash"
        if "p256" in name:
            return "sig"
        return "both"
    if ("Gf2_128" in name or "gf2_128" in name) and "Fp" in name:
        return "both"
    if "Gf2_128" in name or "gf2_128" in name:
        return "hash"
    if "Fp" in name or "p256" in name.lower():
        return "sig"
    return "both"


def normal(name, side):
    """A frame's name as the patterns expect it: no offset, and for Ada
    the GNAT form, lower case with "__" between units."""
    name = re.sub(r"\s+\(inlined\)$", "", name.strip())
    name = re.sub(r"\+0x[0-9a-f]+$", "", name)
    if side == "ours":
        #  GNAT names the body of a subprogram with a postcondition
        #  X___wrapped_statements, and a nested one X__Y; the former is
        #  X itself.
        name = name.replace(".", "__").lower()
        name = re.sub(r"___wrapped_statements(__[0-9]+)?$", "", name)
    else:
        #  The crate disambiguators of the v0 scheme, runtime_zk[1a2b...].
        name = re.sub(r"\[[0-9a-f]{16}\]", "", name)
        name = re.sub(r"\.(constprop|part|isra|cold)\.[0-9]+", "", name)
    return name


def attribute(frames, roots, program, side):
    """The (step, circuit, root) of one stack, innermost frame first."""
    names = [normal(f, side) for f in frames]
    for i, name in enumerate(names):
        for pattern, step, within in roots:
            if re.search(pattern, name):
                if within and not any(re.search(within, n) for n in names[i + 1:]):
                    continue
                c = circuit_of(name, side)
                return step, c, pattern
    for name in names:
        if re.search(program, name):
            return "program", "both", program
    return "not attributed", "both", None


#  Frames of the allocators and of the language's run time, skipped when
#  naming the subprogram that allocated a block.
RUNTIME = re.compile(r"^(\?\?|malloc|calloc|realloc|memalign|posix_memalign|aligned_alloc|"
                     r"__gnat_|system__|ada__|_ada_|__libc|operator new|"
                     r"alloc::|<alloc::|core::|<core::|std::|<std::|__rust|hashbrown|"
                     r"\(allocated)")


def allocator(frames, side):
    """The first frame of the program's own code in an allocation's stack."""
    for f in frames:
        n = normal(f, side)
        if "heapprof" in n or RUNTIME.match(n):
            continue
        return n
    return "??"


def perf_stacks(path):
    """The stacks of `perf script`: one (frames, weight) per sample."""
    frames = []
    with open(path, errors="replace") as f:
        for line in f:
            if not line.strip():
                if frames:
                    yield frames, 1
                frames = []
                continue
            if line[0] not in " \t":
                frames = []
                continue
            m = re.match(r"\s+[0-9a-f]+\s+(.*?)(?:\s+\((.*)\))?$", line.rstrip("\n"))
            if m:
                frames.append(m.group(1))
    if frames:
        yield frames, 1


def heap_stacks(path):
    """The blocks of a heapprof dump, their addresses resolved."""
    maps, blocks, at = [], [], 0
    for line in open(path):
        if line.startswith("at "):
            at = int(line.split()[1])
        elif line.startswith("map "):
            f = line.split()
            if len(f) >= 7 and "x" in f[2]:
                lo, hi = (int(x, 16) for x in f[1].split("-"))
                maps.append((lo, hi, int(f[3], 16), f[6]))
        elif line.startswith("block "):
            f = line.split()
            blocks.append((int(f[1]), [int(a, 16) for a in f[2:]]))
    wanted = collections.defaultdict(set)

    #  addr2line takes the address as the module's own virtual address,
    #  not as an offset in its file: the two differ where a loadable
    #  segment's file offset is not its address (lld does this), so the
    #  offset is converted by the module's program headers.
    segments = {}

    def to_vaddr(mod, off):
        if mod not in segments:
            r = subprocess.run(["readelf", "-lW", mod], capture_output=True, text=True)
            segments[mod] = [(int(f[1], 16), int(f[2], 16), int(f[4], 16))
                             for f in (l.split() for l in r.stdout.split("\n"))
                             if len(f) > 5 and f[0] == "LOAD"]
        for p_off, p_vaddr, p_filesz in segments[mod]:
            if p_off <= off < p_off + p_filesz:
                return off - p_off + p_vaddr
        return off

    def place(a):
        for lo, hi, off, mod in maps:
            if lo <= a < hi:
                return mod, to_vaddr(mod, a - lo + off)
        return None, None

    for _, addrs in blocks:
        for a in addrs:
            mod, off = place(a - 1)
            if mod:
                wanted[mod].add(off)
    #  addr2line -a -f -i prints, for each address, the address, then
    #  one pair of lines per frame, inlined ones first: the function,
    #  then its file and line.
    names = {}
    for mod, offs in wanted.items():
        offs = sorted(offs)
        r = subprocess.run(["addr2line", "-a", "-f", "-i", "-C", "-e", mod] + ["%x" % o for o in offs],
                           capture_output=True, text=True)
        cur, pair = None, 0
        for line in r.stdout.split("\n"):
            if re.match(r"^0x[0-9a-f]+$", line):
                cur = (mod, int(line, 16))
                names[cur] = []
                pair = 0
            elif cur is not None and line:
                if pair % 2 == 0:
                    names[cur].append(line)
                pair += 1
    if at == 0:
        raise SystemExit("attribute-steps: %s: the run never reached the requested peak "
                         "(\"at 0\"): not the same command, or not deterministic" % path)
    total = 0
    for size, addrs in blocks:
        frames = []
        for a in addrs:
            mod, off = place(a - 1)
            if mod and mod.endswith("heapprof.so"):
                continue
            frames += names.get((mod, off), ["??"]) if mod else ["??"]
        total += size
        yield frames, size
    if at > total:
        yield ["(allocated before the profiler was ready, or while it recorded)"], at - total


def main(argv):
    if len(argv) != 5:
        print(__doc__, file=sys.stderr)
        return 2
    side, prog, kind, path = argv[1:]
    roots = (OURS if side == "ours" else UPSTREAM)[prog]
    program = OURS_PROGRAM if side == "ours" else UP_PROGRAM
    stacks = perf_stacks(path) if kind == "time" else heap_stacks(path)
    by = collections.Counter()
    per_root = collections.Counter()
    objects = collections.Counter()
    total = 0
    for frames, weight in stacks:
        step, circuit, root = attribute(frames, roots, program, side)
        by[(step, circuit)] += weight
        if root:
            per_root[root] += weight
        if kind == "heap":
            objects[(step, circuit, allocator(frames, side))] += weight
        total += weight
    order = [s for _, s, _ in roots]
    order = sorted(set(order), key=order.index) + ["program", "not attributed"]
    for step in order:
        for circuit in ("hash", "sig", "both"):
            w = by.get((step, circuit), 0)
            if w:
                print("%s\t%s\t%d\t%.4f" % (step, circuit, w, w / total if total else 0))
    print("total\t\t%d\t1.0000" % total)
    for pattern, step, _ in roots:
        print("root\t%s\t%s\t%d" % (step, pattern, per_root.get(pattern, 0)))
    for (step, circuit, where), w in sorted(objects.items(), key=lambda x: -x[1]):
        if w >= total / 1000:
            print("object\t%s\t%s\t%s\t%d" % (step, circuit, where, w))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
