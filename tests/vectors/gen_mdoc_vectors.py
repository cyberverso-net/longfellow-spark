#!/usr/bin/env python3
"""Generator for the mDoc circuit vectors (Phase D, block 1):
  mdoc_summary.txt   field <gf2_128|p256>
                     file <name> ok <path>
                     summary <name> <nl> <nt> <noutput> <ninput> <npublic>
                             <sfb> <id>
                     layer <name> <j> <logw> <nw> <nterms>
             in the format of circuit_summary.txt, for the harness
             circuit_kat: the four circuits of the two production
             archives of google/longfellow-zk at d5e6be7 chosen for the
             phase, parsed by the independent LFC2 reader of
             gen_circuit_vectors.py.

The archives (rust/applications/mdoc_zk/artifacts/circuits/<hash>.lfa2,
copied under tests/vectors/upstream/mdoc/) are zstd streams; decompressed,
each is an LFA2 archive (rust/core/proto/src/archive): the magic "LFA2",
the archive version byte 1, the circuit version as ULEB128, the combined
identifier (SHA-256 of the entries' circuit identifiers in order), four
UTF-8 strings with ULEB128 lengths (created_at, author, generator_tool,
description), the entry count, then per entry a name, a 32-byte circuit
identifier and a payload length, then the payloads. The entries are "sig"
(the P-256 signature circuit) and "hash" (the GF(2^128) hash circuit).
The archive's file name is its combined identifier.

The decompressed payloads are committed beside the archives as
<hash>_<entry>.lfc2 so that the harnesses and the command-line tools read
them directly. When zstd is available (the standard library module
compression.zstd, Python 3.14 and later, or the zstd command), this
generator decompresses the archives, checks the structure, the combined
identifier and the entries' identifiers against compute_id, and checks
that the committed .lfc2 files are the payloads byte for byte; without
zstd it says so on standard error and checks the committed files alone.
Either way the output is the same.

Usage: python3 -I gen_mdoc_vectors.py [output-directory]
Output is deterministic (no timestamps).
"""

import hashlib
import importlib.util
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).parent
MDOC = HERE / "upstream" / "mdoc"

ARCHIVES = [
    # (combined id, circuit version, number of attributes)
    ("8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121", 7, 1),
    ("137e5a75ce72735a37c8a72da1a8a0a5df8d13365c2ae3d2c2bd6a0e7197c7c6", 6, 1),
]
ENTRY_FIELD = {"sig": "p256", "hash": "gf2_128"}


def fail(msg: str) -> None:
    print(f"gen_mdoc_vectors: FAILED: {msg}", file=sys.stderr)
    sys.exit(1)


def load_sibling(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


GC = load_sibling("gen_circuit_vectors")


def decompress(raw: bytes):
    """The zstd stream, or None when no decompressor is available."""
    try:
        import compression.zstd as zstd  # Python 3.14 and later
        return zstd.decompress(raw)
    except ImportError:
        pass
    if shutil.which("zstd"):
        return subprocess.run(["zstd", "-d", "-c"], input=raw, check=True,
                              capture_output=True).stdout
    return None


def uleb(buf: bytes, p: int):
    v = 0
    s = 0
    while True:
        b = buf[p]
        p += 1
        v |= (b & 0x7F) << s
        s += 7
        if b < 0x80:
            return v, p


def utf8(buf: bytes, p: int):
    n, p = uleb(buf, p)
    return buf[p:p + n].decode("utf-8"), p + n


def parse_lfa2(data: bytes):
    """from_stream_lfa2_body of the production reader: returns the circuit
    version, the metadata and the entries (name, circuit id, payload)."""
    if data[:4] != b"LFA2":
        fail("archive: bad magic")
    p = 4
    if data[p] != 1:
        fail(f"archive: unsupported version {data[p]}")
    p += 1
    circuit_version, p = uleb(data, p)
    combined = data[p:p + 32]
    p += 32
    meta = {}
    for key in ("created_at", "author", "generator_tool", "description"):
        meta[key], p = utf8(data, p)
    n, p = uleb(data, p)
    heads = []
    for _ in range(n):
        name, p = utf8(data, p)
        cid = data[p:p + 32]
        p += 32
        length, p = uleb(data, p)
        heads.append((name, cid, length))
    entries = []
    for name, cid, length in heads:
        entries.append((name, cid, data[p:p + length]))
        p += length
    if p != len(data):
        fail("archive: trailing bytes")
    h = hashlib.sha256()
    for _, cid, _ in entries:
        h.update(cid)
    if h.digest() != combined:
        fail("archive: combined identifier mismatch")
    return circuit_version, combined, meta, entries


def check_archive(combined_hex: str, version: int):
    """Decompress and check the archive against the committed payloads;
    returns the entries' identifiers by name, or None without zstd."""
    raw = (MDOC / f"{combined_hex}.lfa2").read_bytes()
    data = decompress(raw)
    if data is None:
        print("gen_mdoc_vectors: no zstd decompressor; the committed .lfc2 "
              "files are checked alone", file=sys.stderr)
        return None
    circuit_version, combined, _, entries = parse_lfa2(data)
    if combined.hex() != combined_hex:
        fail(f"archive {combined_hex[:8]}: combined identifier is {combined.hex()}")
    if circuit_version != version:
        fail(f"archive {combined_hex[:8]}: circuit version {circuit_version}")
    if [name for name, _, _ in entries] != ["sig", "hash"]:
        fail(f"archive {combined_hex[:8]}: entries {[e[0] for e in entries]}")
    ids = {}
    for name, cid, payload in entries:
        committed = (MDOC / f"{combined_hex}_{name}.lfc2").read_bytes()
        if committed != payload:
            fail(f"archive {combined_hex[:8]}: committed {name}.lfc2 differs")
        ids[name] = cid
    return ids


def main() -> None:
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE
    out_dir.mkdir(parents=True, exist_ok=True)
    lines = [
        "# Phase D, block 1: the four circuits of the two production mDoc",
        "# archives of google/longfellow-zk at d5e6be7 (version 7 and 6, one",
        "# attribute), extracted from the .lfa2 archives under",
        "# tests/vectors/upstream/mdoc/ and parsed by the independent LFC2",
        "# reader of gen_circuit_vectors.py; the format of circuit_summary.txt.",
        "# Generated by gen_mdoc_vectors.py (this directory); do not edit.",
    ]
    for combined_hex, version, nattr in ARCHIVES:
        ids = check_archive(combined_hex, version)
        for entry in ("hash", "sig"):
            fname = ENTRY_FIELD[entry]
            fld = GC.FIELDS[fname]
            path = MDOC / f"{combined_hex}_{entry}.lfc2"
            status, circ, sfb, ident = GC.read_lfc2(fld, path.read_bytes())
            if status != "ok":
                fail(f"{combined_hex[:8]} {entry}: {status}")
            if ids is not None and ids[entry] != ident:
                fail(f"{combined_hex[:8]} {entry}: identifier differs from the archive's")
            name = f"mdoc_v{version}_{nattr}attr_{entry}"
            rel = path.relative_to(HERE.parent.parent)
            lines.append(f"field {fname}")
            lines.append(f"file {name} ok {rel}")
            emit = lines.append
            GC.emit_circuit(emit, fld, name, circ, sfb, ident)
    (out_dir / "mdoc_summary.txt").write_text("\n".join(lines) + "\n")
    print(f"gen_mdoc_vectors: wrote mdoc_summary.txt ({2 * len(ARCHIVES)} circuits) to {out_dir}")


if __name__ == "__main__":
    main()
