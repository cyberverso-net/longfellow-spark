#!/usr/bin/env python3
"""Generator for the Phase B circuit vectors (ADR 0048):
  circuit_lfc2.txt     tier 2: the Appendix B.3 circuits and a Z-assertion
                       circuit written in LFC2 in two valid encodings, and
                       the malformed cases with the status each must give
  circuit_summary.txt  tier 1: the two upstream circuit files parsed by the
                       reference below, their layers and identifiers
  interop.txt          tier 3: the two upstream proofs with the labels and
                       configurations of the upstream reference test

An independent LFC2 reader and writer, written from the production reader
and writer of google/longfellow-zk at d5e6be7
(rust/core/proto/src/reader/lfc2.rs, writer/lfc2.rs, uleb.rs, circuit.rs
compute_id), with the stricter rules of this project (ADR 0046): the
project's bounds, Well_Formed of the core, the identifier always checked.
The reader returns the status the SPARK loader must return. Before
anything is written, the generator checks that the identifier it
computes for each upstream file equals the one the file stores, so that
compute_id is anchored on upstream, and that its writer round-trips
through its reader to the term lists of gen_sumcheck_vectors.py.

File format ('#' comments, blanks separate fields, elements as big-endian
hex of the integer, 32 digits on GF(2^128), 64 on P-256, bytes as hex,
the identifier as 64 hex digits in memory order):
  field <gf2_128|p256>
  lfc2 <name> <status> <bytes>            Read gives this status (- for no bytes)
  file <name> <status> <path>             Read of the file gives this status
  summary <name> <nl> <nt> <noutput> <ninput> <npublic> <sfb> <id>
  layer <name> <j> <logw> <nw> <nterms>
  term <name> <i> <g> <h0> <h1> <k>       term i (1-based) of the circuit
Statuses are the lower-case values of Circuit_Status.

Usage: python3 -I gen_circuit_vectors.py [output-directory]
Output is deterministic (no timestamps).
"""

import hashlib
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).parent
UPSTREAM = HERE / "upstream" / "circuits"

MAX_WIRES = 2**24
MAX_LAYERS = 64
MAX_LOGW = 40
MAX_TERMS = 2**28
MAX_ULEB = 2**28 - 1


def fail(msg: str) -> None:
    print(f"gen_circuit_vectors: FAILED: {msg}", file=sys.stderr)
    sys.exit(1)


def load_sibling(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


SC = load_sibling("gen_sumcheck_vectors")

FIELDS = {
    "gf2_128": {"id": 4, "size": 16, "binary": True, "F": SC.GF2_128,
                "hx": lambda v: f"{v:032x}", "mod": None},
    "p256": {"id": 1, "size": 32, "binary": False, "F": SC.P256,
             "hx": lambda v: f"{v:064x}", "mod": SC.P256.P},
}


# ------------------------------------------------------------ integers

def uleb(v: int) -> bytes:
    if not 0 <= v <= MAX_ULEB:
        fail(f"ULEB128 value out of range: {v}")
    out = bytearray()
    while True:
        b = v & 0x7F
        v >>= 7
        if v:
            out.append(b | 0x80)
        else:
            out.append(b)
            return bytes(out)


def zigzag_enc(d: int) -> int:
    return (d << 1) if d >= 0 else (((-d - 1) << 1) | 1)


def zigzag_dec(v: int) -> int:
    return v // 2 if v % 2 == 0 else -(v // 2) - 1


def le64(n: int) -> bytes:
    return n.to_bytes(8, "little")


def ceil_lg2(n: int) -> int:
    k = 0
    while (1 << k) < n:
        k += 1
    return k


def elt_bytes(fld, v: int) -> bytes:
    return v.to_bytes(fld["size"], "little")


# ------------------------------------------------------------- writer

def compute_id(fld, circ, sfb: int) -> bytes:
    """compute_id of rust/core/proto/src/circuit.rs."""
    h = hashlib.sha256()
    if fld["binary"]:
        h.update(le64(2))
        h.update(le64(8 * fld["size"]))
    else:
        h.update(le64(1))
        h.update(elt_bytes(fld, fld["mod"] - 1))
    h.update(le64(circ["noutput"]))
    h.update(le64(ceil_lg2(circ["noutput"])))
    h.update(le64(1))
    h.update(le64(0))
    h.update(le64(len(circ["layers"])))
    h.update(le64(circ["ninput"]))
    h.update(le64(circ["npublic"]))
    h.update(le64(sfb))
    for logw, nw, terms in circ["layers"]:
        h.update(le64(nw))
        h.update(le64(logw))
        h.update(le64(len(terms)))
        for g, h0, h1, k in terms:
            h.update(le64(g))
            h.update(le64(h0))
            h.update(le64(h1))
            h.update(elt_bytes(fld, k))
    return h.digest()


def write_lfc2(fld, circ, sfb: int = 0, dedup: bool = True,
               ident: bytes | None = None) -> bytes:
    """The circuit in LFC2. dedup: one segment per distinct delta and a
    token per term (the shape of the upstream writer); otherwise one
    delta per term, one segment holding them all, one token."""
    consts: list[int] = []
    cidx: dict[int, int] = {}
    for _, _, terms in circ["layers"]:
        for *_, k in terms:
            if k not in cidx:
                cidx[k] = len(consts)
                consts.append(k)
    out = bytearray(b"LFC2")
    out += uleb(fld["id"]) + uleb(circ["noutput"]) + uleb(1)
    out += uleb(circ["npublic"]) + uleb(sfb) + uleb(circ["ninput"])
    out += uleb(len(circ["layers"]))
    out += uleb(len(consts))
    for k in consts:
        out += elt_bytes(fld, k)
    for logw, nw, terms in circ["layers"]:
        pg = ph0 = ph1 = 0
        deltas: list[tuple[int, int, int, int]] = []
        didx: dict[tuple[int, int, int, int], int] = {}
        seq: list[int] = []
        for g, h0, h1, k in terms:
            d = (zigzag_enc(g - pg), zigzag_enc(h0 - ph0),
                 zigzag_enc(h1 - ph1), cidx[k])
            pg, ph0, ph1 = g, h0, h1
            if dedup:
                if d not in didx:
                    didx[d] = len(deltas)
                    deltas.append(d)
                seq.append(didx[d])
            else:
                seq.append(len(deltas))
                deltas.append(d)
        out += uleb(logw) + uleb(nw)
        out += uleb(len(deltas))
        for d in deltas:
            out += b"".join(uleb(x) for x in d)
        if dedup:
            segments = [[i] for i in range(len(deltas))]
            tokens = seq
        else:
            segments = [seq]
            tokens = [0] if seq else []
        out += uleb(len(segments))
        for seg in segments:
            out += uleb(len(seg)) + b"".join(uleb(i) for i in seg)
        out += uleb(len(tokens)) + b"".join(uleb(t) for t in tokens)
    out += compute_id(fld, circ, sfb) if ident is None else ident
    return bytes(out)


# ------------------------------------------------------------- reader

class Reject(Exception):
    def __init__(self, status: str):
        super().__init__(status)
        self.status = status


class Cursor:
    def __init__(self, data: bytes):
        self.b = data
        self.pos = 0

    def remaining(self) -> int:
        return len(self.b) - self.pos

    def nat(self) -> int:
        acc = 0
        for i in range(4):
            if self.pos + i >= len(self.b):
                raise Reject("truncated")
            byte = self.b[self.pos + i]
            acc += (byte & 0x7F) << (7 * i)
            if byte < 0x80:
                self.pos += i + 1
                return acc
        raise Reject("bad_integer")

    def take(self, n: int) -> bytes:
        if self.remaining() < n:
            raise Reject("truncated")
        r = self.b[self.pos:self.pos + n]
        self.pos += n
        return r


def read_element(fld, cur: Cursor) -> int:
    raw = cur.take(fld["size"])
    v = int.from_bytes(raw, "little")
    if fld["mod"] is not None and v >= fld["mod"]:
        raise Reject("bad_element")
    return v


def parse_body(fld, cur: Cursor):
    """The walk of Circuit_Reader on a cursor: the header, the constants,
    the layers, the identifier, nothing after; raises Reject with the
    status. Returns (circuit, sfb, stored identifier)."""
    if cur.take(4) != b"LFC2":
        raise Reject("bad_magic")
    fid = cur.nat()
    noutput = cur.nat()
    if noutput > MAX_WIRES:
        raise Reject("bound_exceeded")
    if cur.nat() != 1:
        raise Reject("unsupported_copies")
    npublic = cur.nat()
    if npublic > MAX_WIRES:
        raise Reject("bound_exceeded")
    sfb = cur.nat()
    ninput = cur.nat()
    if ninput > MAX_WIRES:
        raise Reject("bound_exceeded")
    nl = cur.nat()
    if not 1 <= nl <= MAX_LAYERS:
        raise Reject("bound_exceeded")
    if fid != fld["id"]:
        raise Reject("field_mismatch")
    nconst = cur.nat()
    if nconst > cur.remaining() // fld["size"]:
        raise Reject("truncated")
    consts = [read_element(fld, cur) for _ in range(nconst)]
    layers = []
    total = 0
    for _ in range(nl):
        logw = cur.nat()
        if logw > MAX_LOGW:
            raise Reject("bound_exceeded")
        nw = cur.nat()
        if nw > MAX_WIRES:
            raise Reject("bound_exceeded")
        nd = cur.nat()
        if nd > cur.remaining() // 4:
            raise Reject("truncated")
        deltas = []
        for _ in range(nd):
            g, h0, h1, k = cur.nat(), cur.nat(), cur.nat(), cur.nat()
            if k >= nconst:
                raise Reject("bad_index")
            deltas.append((zigzag_dec(g), zigzag_dec(h0), zigzag_dec(h1), k))
        ns = cur.nat()
        if ns > cur.remaining():
            raise Reject("truncated")
        segments = []
        for _ in range(ns):
            ln = cur.nat()
            if ln > cur.remaining():
                raise Reject("truncated")
            seg = []
            for _ in range(ln):
                idx = cur.nat()
                if idx >= nd:
                    raise Reject("bad_index")
                seg.append(idx)
            segments.append(seg)
        ntok = cur.nat()
        terms = []
        g = h0 = h1 = 0
        for _ in range(ntok):
            tok = cur.nat()
            if tok >= ns:
                raise Reject("bad_index")
            if total + len(terms) + len(segments[tok]) > MAX_TERMS:
                raise Reject("bound_exceeded")
            for idx in segments[tok]:
                dg, dh0, dh1, k = deltas[idx]
                g, h0, h1 = g + dg, h0 + dh0, h1 + dh1
                for w in (g, h0, h1):
                    if not 0 <= w < MAX_WIRES:
                        raise Reject("bad_index")
                terms.append((g, h0, h1, consts[k]))
        total += len(terms)
        layers.append((logw, nw, terms))
    ident = cur.take(32)
    if cur.remaining():
        raise Reject("trailing_bytes")
    circ = {"noutput": noutput, "ninput": ninput, "npublic": npublic,
            "layers": layers}
    return circ, sfb, ident


def read_lfc2(fld, data: bytes):
    """(status, circuit or None, sfb, id): the rules of Circuit_Reader.Read
    in its order, the walk, Well_Formed, the identifier."""
    try:
        circ, sfb, ident = parse_body(fld, Cursor(data))
        if not well_formed(circ):
            raise Reject("not_well_formed")
        premises(circ)
        if compute_id(fld, circ, sfb) != ident:
            raise Reject("id_mismatch")
        return "ok", circ, sfb, ident
    except Reject as r:
        return r.status, None, None, None


def well_formed(circ) -> bool:
    if circ["npublic"] > circ["ninput"]:
        return False
    nv = circ["noutput"]
    for logw, nw, terms in circ["layers"]:
        if nw > (1 << logw):
            return False
        for g, h0, h1, _ in terms:
            if not (g < nv and h0 < nw and h1 < nw):
                return False
        nv = nw
    return circ["layers"][-1][1] == circ["ninput"]


def premises(circ) -> None:
    """Isolated and DeadEnd of upstream's Lean proofs (ADR 0064), in the
    order of Circuit_Reader: layer by layer from the output, each
    layer's assertions alone on their wires, then the reads of the
    layer above against them. An assertion is a term of constant 0."""
    layers = circ["layers"]
    for j, (_, _, terms) in enumerate(layers):
        mark = {}
        for i, (g, _, _, k) in enumerate(terms):
            if k == 0:
                if g in mark:
                    raise Reject("not_isolated")
                mark[g] = i
        for i, (g, _, _, _) in enumerate(terms):
            if mark.get(g, i) != i:
                raise Reject("not_isolated")
        if j > 0:
            for _, h0, h1, _ in layers[j - 1][2]:
                if h0 in mark or h1 in mark:
                    raise Reject("not_dead_end")


# ------------------------------------------------------------- output

def emit_circuit(emit, fld, name, circ, sfb, ident):
    nt = sum(len(t) for _, _, t in circ["layers"])
    emit(f"summary {name} {len(circ['layers'])} {nt} {circ['noutput']} "
         f"{circ['ninput']} {circ['npublic']} {sfb} {ident.hex()}")
    for j, (logw, nw, terms) in enumerate(circ["layers"]):
        emit(f"layer {name} {j} {logw} {nw} {len(terms)}")


def emit_terms(emit, fld, name, circ):
    i = 0
    for _, _, terms in circ["layers"]:
        for g, h0, h1, k in terms:
            i += 1
            emit(f"term {name} {i} {g} {h0} {h1} {fld['hx'](k)}")


def mutate(data: bytes, offset: int, value: int) -> bytes:
    b = bytearray(data)
    b[offset] = value
    return bytes(b)


def with_id(fld, data: bytes) -> bytes:
    """The bytes with their identifier recomputed when the body parses;
    otherwise unchanged (the structural status is then what is tested)."""
    try:
        circ, sfb, _ = parse_body(fld, Cursor(data))
    except Reject:
        return data
    return data[:-32] + compute_id(fld, circ, sfb)


def main() -> None:
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE
    out_dir.mkdir(parents=True, exist_ok=True)

    # ---- tier 1: the upstream files, anchoring compute_id
    summary: list[str] = []
    s_emit = summary.append
    s_emit("# Phase B tier 1 (ADR 0048): the two upstream circuit files of")
    s_emit("# google/longfellow-zk d5e6be7 (docs/specs/rust/tests/testdata),")
    s_emit("# copied unchanged under tests/vectors/upstream/circuits/ and parsed")
    s_emit("# by the independent LFC2 reader of gen_circuit_vectors.py; the")
    s_emit("# identifier each file stores equals the one the reference computes.")
    s_emit("# Generated by gen_circuit_vectors.py (this directory); do not edit.")
    for name, fname in (("sha256", "gf2_128"), ("ecdsa2", "p256")):
        fld = FIELDS[fname]
        path = UPSTREAM / f"{name}_circuit.lfc2"
        data = path.read_bytes()
        status, circ, sfb, ident = read_lfc2(fld, data)
        if status != "ok":
            fail(f"upstream {name}: {status}")
        if ident != data[-32:]:
            fail(f"upstream {name}: identifier differs")
        s_emit(f"field {fname}")
        s_emit(f"file {name} ok tests/vectors/upstream/circuits/{name}_circuit.lfc2")
        emit_circuit(s_emit, fld, name, circ, sfb, ident)
    (out_dir / "circuit_summary.txt").write_text("\n".join(summary) + "\n")

    # ---- tier 3: the interop cases, labels and configurations of
    # docs/specs/rust/tests/test_reference.rs; neither circuit has public
    # inputs, so the public input list is empty
    interop = [
        "# Phase B tier 3 (ADR 0048): the two upstream proofs, verified end to",
        "# end by Zk_Verifier on the circuit loaded from the file, under the",
        "# circuit's identifier, the label and the Ligero configuration of the",
        "# upstream reference test (docs/specs/rust/tests/test_reference.rs at",
        "# d5e6be7). Lines:",
        "#   interop <name> <field> <circuit> <proof> <label> <rate_inv> <nreq>",
        "#           <ncol> <npublic> <public inputs...> <status>",
        "#           <root refusal> <sumcheck refusal> <ligero refusal>",
        "# The harness also alters one byte of each accepted proof in its root,",
        "# its sumcheck part and its Ligero part and requires the three refusal",
        "# statuses recorded here, observed at the first run (every altered byte",
        "# is absorbed by the transcript and moves the chosen columns, so the",
        "# Merkle check fails first); a change of status is a regression to",
        "# look at even where the proof is still refused.",
        "# Generated by gen_circuit_vectors.py (this directory); do not edit.",
        "interop sha256 gf2_128 tests/vectors/upstream/circuits/sha256_circuit.lfc2 "
        "tests/vectors/upstream/circuits/sha256_proof.bin sha256_spec_test 3 16 256 0 ok "
        "merkle_failed merkle_failed merkle_failed",
        "interop ecdsa2 p256 tests/vectors/upstream/circuits/ecdsa2_circuit.lfc2 "
        "tests/vectors/upstream/circuits/ecdsa2_proof.bin ecdsa2_spec_test 4 16 256 0 ok "
        "merkle_failed merkle_failed merkle_failed",
    ]
    (out_dir / "interop.txt").write_text("\n".join(interop) + "\n")

    # ---- tier 2: the explicit circuits in LFC2, and the malformed cases
    lines: list[str] = []
    emit = lines.append
    emit("# Phase B tier 2 (ADR 0048): the Appendix B.3 circuits and the")
    emit("# Z-assertion circuit of gen_sumcheck_vectors.py written in LFC2 by")
    emit("# an independent writer, in two valid encodings (dedup: one segment")
    emit("# per distinct delta, as the upstream writer; plain: one delta per")
    emit("# term in one segment), each with its identifier; then malformed")
    emit("# files built from the dedup encoding, with the status each gives.")
    emit("# Generated by gen_circuit_vectors.py (this directory); do not edit.")
    circuits = {
        "gf2_128": [SC.sgonal_gf2_128(), SC.zcheck()],
        "p256": [SC.sgonal_p256()],
    }
    for fname, circs in circuits.items():
        fld = FIELDS[fname]
        emit(f"field {fname}")
        for circ in circs:
            for enc in ("dedup", "plain"):
                name = f"{circ['name']}_{enc}"
                data = write_lfc2(fld, circ, sfb=0, dedup=(enc == "dedup"))
                status, back, sfb, ident = read_lfc2(fld, data)
                if status != "ok" or back["layers"] != circ["layers"] \
                        or (back["noutput"], back["ninput"], back["npublic"]) \
                        != (circ["noutput"], circ["ninput"], circ["npublic"]):
                    fail(f"{name}: round trip ({status})")
                emit(f"lfc2 {name} ok {data.hex()}")
                emit_circuit(emit, fld, name, back, sfb, ident)
                emit_terms(emit, fld, name, back)

    # malformed cases on the GF(2^128) B.3.3 circuit, dedup encoding
    fld = FIELDS["gf2_128"]
    base_circ = SC.sgonal_gf2_128()
    base = write_lfc2(fld, base_circ)
    emit("field gf2_128")
    cases: list[tuple[str, str, bytes]] = []

    def case(name, want, data):
        got = read_lfc2(fld, data)[0]
        if got != want:
            fail(f"malformed {name}: reference gives {got}, intended {want}")
        cases.append((name, want, data))

    case("bad_magic", "bad_magic", b"LFC1" + base[4:])
    case("empty", "truncated", b"")
    case("magic_only", "truncated", base[:4])
    case("field_p256_in_gf", "field_mismatch", with_id(fld, mutate(base, 4, 1)))
    # header: magic(4) fid(1) nv(1) nc(1) npub(1) sfb(1) ninput(1) nl(1)
    case("ncopies_2", "unsupported_copies", mutate(base, 6, 2))
    case("noutput_over_max", "bound_exceeded",
         base[:5] + uleb(MAX_WIRES + 1) + base[6:])
    case("no_layer", "bound_exceeded", mutate(base, 10, 0))
    case("too_many_layers", "bound_exceeded", mutate(base, 10, MAX_LAYERS + 1))
    case("uleb_five_bytes", "bad_integer",
         base[:5] + b"\x80\x80\x80\x80\x01" + base[6:])
    # constants: count at 11, then 16 bytes each
    nconst = base[11]
    case("constant_count_beyond_bytes", "truncated", mutate(base, 11, 200))
    case("truncated_in_constants", "truncated", base[:12 + 8])
    # layer 0 starts after the constants
    l0 = 12 + 16 * nconst
    case("logw_over_max", "bound_exceeded", mutate(base, l0, MAX_LOGW + 1))
    case("nw_over_max", "bound_exceeded",
         base[:l0 + 1] + uleb(MAX_WIRES + 1) + base[l0 + 2:])
    nd = base[l0 + 2]
    # first delta: g h0 h1 k at l0 + 3 ..
    case("constant_index_out_of_range", "bad_index",
         mutate(base, l0 + 6, nconst))
    # segments: count at l0 + 3 + 4 * nd, first segment length then index
    seg0 = l0 + 3 + 4 * nd
    case("delta_index_out_of_range", "bad_index", mutate(base, seg0 + 2, nd))
    ns = base[seg0]
    tok0 = seg0 + 1 + 2 * ns
    case("token_out_of_range", "bad_index", mutate(base, tok0 + 1, ns))
    case("truncated_in_layer", "truncated", base[:tok0])
    case("truncated_before_id", "truncated", base[:-32])
    case("truncated_in_id", "truncated", base[:-1])
    case("trailing_byte", "trailing_bytes", base + b"\x00")
    case("wrong_id", "id_mismatch", mutate(base, len(base) - 1, base[-1] ^ 1))
    # well-formedness: a term reading wire 7 in a layer of width 5
    bad = SC.sgonal_gf2_128()
    logw, nw, terms = bad["layers"][0]
    bad["layers"][0] = (logw, nw, terms[:-1] + [(0, 0, 7, terms[-1][3])])
    case("wire_out_of_layer", "not_well_formed", write_lfc2(fld, bad))
    bad = SC.sgonal_gf2_128()
    logw, nw, terms = bad["layers"][0]
    bad["layers"][0] = (2, nw, terms)
    case("width_above_logw", "not_well_formed", write_lfc2(fld, bad))
    bad = SC.sgonal_gf2_128()
    bad["ninput"] = 5
    case("last_layer_not_ninput", "not_well_formed", write_lfc2(fld, bad))
    bad = SC.sgonal_gf2_128()
    bad["npublic"] = 5
    bad["ninput"] = 4
    case("npublic_above_ninput", "not_well_formed", write_lfc2(fld, bad))
    # the circuit premises (ADR 0064): an assertion sharing its wire, and
    # a term reading an assertion of the layer below
    bad = SC.zcheck()
    logw, nw, terms = bad["layers"][0]
    bad["layers"][0] = (logw, nw, terms + [(1, 2, 2, 1)])
    case("assertion_not_isolated", "not_isolated", write_lfc2(fld, bad))
    bad = SC.sgonal_gf2_128()
    logw, nw, terms = bad["layers"][1]
    bad["layers"][1] = (logw, nw, terms[:-1] + [(4, 0, 1, 0)])
    case("assertion_read", "not_dead_end", write_lfc2(fld, bad))
    # a negative prefix sum: a delta that takes g below zero
    neg = SC.sgonal_gf2_128()
    logw, nw, terms = neg["layers"][0]
    neg["layers"][0] = (logw, nw, [(0, 0, 0, 1)] + terms)
    neg_bytes = write_lfc2(fld, neg)
    # the first delta of layer 0 is (0, 0, 0); replace its g by zigzag(-1) = 1
    case("negative_wire", "bad_index", mutate(neg_bytes, l0 + 3, 1))
    for name, want, data in cases:
        emit(f"lfc2 {name} {want} {data.hex() or '-'}")
    # P-256: a constant at or above p is not an element
    fld = FIELDS["p256"]
    emit("field p256")
    circ = SC.sgonal_p256()
    data = write_lfc2(fld, circ)
    nonc = bytearray(data)
    nonc[12:12 + 32] = elt_bytes(fld, fld["mod"])
    got = read_lfc2(fld, bytes(nonc))[0]
    if got != "bad_element":
        fail(f"non-canonical constant: reference gives {got}")
    emit(f"lfc2 non_canonical_constant bad_element {bytes(nonc).hex()}")
    got = read_lfc2(fld, mutate(data, 4, 4))[0]
    if got != "field_mismatch":
        fail(f"field mismatch on p256: reference gives {got}")
    emit(f"lfc2 field_gf_in_p256 field_mismatch {with_id(fld, mutate(data, 4, 4)).hex()}")
    (out_dir / "circuit_lfc2.txt").write_text("\n".join(lines) + "\n")
    print(f"gen_circuit_vectors: wrote circuit_summary.txt, interop.txt and circuit_lfc2.txt "
          f"({len(cases) + 2} malformed cases) to {out_dir}")


if __name__ == "__main__":
    main()
