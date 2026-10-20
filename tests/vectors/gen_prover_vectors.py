#!/usr/bin/env python3
"""Generator for the Phase C prover vectors (ADR 0053), blocks 2 and 3:
  writer.txt           roundtrip <name> <field> <circuit> <proof> <rate_inv>
                                 <nreq> <ncol>
               the proof bytes, read by Zk_Verifier.Read_Proof on the
               circuit and written back by Proof_Writer, must be identical;
               <circuit> and <proof> are hex:<bytes> or path:<file relative
               to the repository root>.
  sumcheck_prover.txt  sumcheck <name> <field> <seed> <label> <root> <circuit>
                                <nwit> <witness...> <npads> <pads...> <proof>
               the pads of Section 6.5 drawn from SimpleRng (seed <seed>)
               in the order of ADR 0050 and the padded sumcheck proof
               (Section 6.6, in the order of Section 7.3) of the reference
               prover of this file on the transcript (<label>, <root>,
               the circuit identifier of <circuit>, the public inputs);
               Sumcheck_Prover under Simple_Rng must reproduce both.
  ligero_commit.txt    commit <name> <field> <seed> <rate_inv> <nreq> <ncol>
                              <circuit lfc2> <nin> <inputs...> <root>
                              <nrow> {<k> <row...>} <nidx> <idx...>
                              <npath> <path...>
               the Ligero commitment of Section 4.3 (ligero/prover.rs
               layout_tableau and commit) by the reference below on the
               witness vector (private inputs, then the pads of
               sumcheck_prover.txt drawn first from the same Simple_Rng):
               the Merkle root, the unencoded rows (k elements each, the
               systematic part of the encoded rows) and one batch opening
               (open_merkle_heap) for the given leaf indices.
                       root <name> <field> <seed> <rate_inv> <nreq> <ncol>
                            <circuit path> <nin> <inputs...> <root>
               the first 32 bytes of an upstream proof file: the root the
               commitment on the upstream inputs and seed must reproduce
               (ADR 0053 tier 1, the first byte-for-byte check against
               the shipped proofs).
  zk_prove.txt         prove <name> <field> <seed> <rate_inv> <nreq> <ncol>
                             <circuit lfc2> <nin> <inputs...> <status>
               the complete prover (Zk_Prover.Prove) on a small circuit:
               the status it must report (ok, input_length, not_satisfied,
               not_in_subfield, config_invalid) and, on ok, the proof must
               be accepted by Zk_Verifier under the case name as label
               (completeness, tested: ADR 0052); the bytes themselves are
               checked against the upstream files by the cli step.

The round-trip cases are every proof of the repository: the Appendix
B.3 proofs of draft-google-cfrg-libzk-03 (their bytes from
zk_proof_*.txt, their circuits written in LFC2 by gen_circuit_vectors.py)
and the two upstream proofs of google/longfellow-zk at d5e6be7 (files
under tests/vectors/upstream/circuits/). The round trip exercises the
writers of Sections 7.3, 7.4 and 7.5 against the readers, and the
run-length structure by position of ADR 0051 against the structure the
reference writer chose by value: on the two B.3 proofs (no subfield rows
on GF(2^128); every row a subfield row on P-256) and on the two upstream
proofs (85 subfield rows out of 213 for sha256).

The sumcheck cases are the B.3 circuits (quadratic on GF(2^128), s-gonal
on P-256) and the Z-assertion circuit of gen_circuit_vectors.py, each
with the seed of the upstream test (12345 on GF(2^128), 123456789 on
P-256) and a second seed; the root is the SHA-256 of the case name, since
the Merkle root is not available before block 4 and the sumcheck proof
depends on it only through the transcript. The reference prover below
transcribes ZkProver::commit (pads) and prove (sumcheck::prover.rs:
eval_round_poly, round_poly, bind, the term update) from the clone, with
SimpleRng of tests/test_reference.rs; it shares no code with the Ada
prover.

The commit cases are the same circuits and seeds under the B.3 Ligero
configuration (rate 4, 6 queries, 64 columns), plus one GF(2^128) case
with 8 queries and a subfield boundary that puts the first witness row
below it, so that the subfield sampler of the random prefix is
exercised. The reference transcribes layout_tableau and commit of
ligero/prover.rs, lagrange_matrix and encode_row (through
gen_ligero_vectors.py) and commit_merkle_heap and open_merkle_heap of
merkle.rs. The root cases take the root from the upstream proof files.

Usage: python3 -I gen_prover_vectors.py [output-directory]
Output is deterministic (no timestamps).
"""

import importlib.util
import random
import sys
from pathlib import Path

HERE = Path(__file__).parent


def fail(msg: str) -> None:
    print(f"gen_prover_vectors: FAILED: {msg}", file=sys.stderr)
    sys.exit(1)


def load_sibling(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + ".py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


GC = load_sibling("gen_circuit_vectors")
SC = GC.SC


def b3_proof(field: str, name: str):
    """The complete proof bytes and configuration of an Appendix B.3 case
    from zk_proof_<field>_<...>.txt: root (zk_proof line), sumcheck part,
    Ligero part and its configuration (zk_ligero line)."""
    path = HERE / (f"zk_proof_{field}_{'b3_2' if field == 'p256' else 'b3_3'}.txt")
    root = sumcheck = ligero = None
    cfg = None
    for line in path.read_text().splitlines():
        f = line.split()
        if not f or f[0].startswith("#"):
            continue
        if f[0] == "zk_proof" and f[1] == name:
            root = bytes.fromhex(f[3])
        elif f[0] == "zk_sumcheck" and f[1] == name:
            sumcheck = bytes.fromhex(f[2])
        elif f[0] == "zk_ligero" and f[1] == name:
            cfg = (int(f[2]), int(f[3]), int(f[4]))
            ligero = bytes.fromhex(f[5])
    if root is None or sumcheck is None or ligero is None:
        fail(f"{name}: incomplete zk_proof lines in {path.name}")
    return root + sumcheck + ligero, cfg


# ------------------------------------------------- the reference prover

TV = load_sibling("gen_transcript_vectors")

MAX_LOGW = 40


class SimpleRng:
    """SimpleRng of tests/test_reference.rs: one byte per step of the
    linear congruential generator, bits 32 to 39 of the new state."""

    def __init__(self, seed: int):
        self.state = seed & (2**64 - 1)

    def bytes(self, n: int) -> bytes:
        out = bytearray()
        for _ in range(n):
            self.state = (self.state * 6364136223846793005
                          + 1442695040888963407) & (2**64 - 1)
            out.append((self.state >> 32) & 0xFF)
        return bytes(out)


def sample_elt(fld, rng) -> int:
    """F::sample: 16 bytes on GF(2^128); 32 bytes below p on P-256."""
    while True:
        v = int.from_bytes(rng.bytes(fld["size"]), "little")
        if fld["mod"] is None or v < fld["mod"]:
            return v


def ceil_lg2(n: int) -> int:
    k = 0
    while (1 << k) < n:
        k += 1
    return k


def sample_pads(fld, circ, rng):
    """CircuitPad::sample, flattened in the pad order of Section 6.5."""
    F = fld["F"]
    pads = []
    for logw, _, _ in circ["layers"]:
        for _ in range(logw):
            pads += [sample_elt(fld, rng) for _ in range(4)]
        c0 = sample_elt(fld, rng)
        c1 = sample_elt(fld, rng)
        pads += [c0, c1, F.mul(c0, c1)]
    return pads


def eval_round_poly(F, terms, active, other, hand, x2):
    def ref(w, i):
        return w[i] if i < len(w) else 0
    one_minus_x2 = F.sub(1, x2)
    ev0 = ev1 = ev2 = 0
    for g, h0, h1, k in terms:
        h = (h0, h1)
        hb = h[hand]
        pair = hb & ~1
        w0 = ref(active, pair)
        w1 = ref(active, pair | 1)
        other_val = ref(other, h[1 - hand])
        coef = F.mul(k, other_val)
        wx2 = F.add(w0, F.mul(x2, F.sub(w1, w0)))
        if hb % 2 == 0:
            ev0 = F.add(ev0, F.mul(coef, w0))
            ev2 = F.add(ev2, F.mul(F.mul(coef, one_minus_x2), wx2))
        else:
            ev1 = F.add(ev1, F.mul(coef, w1))
            ev2 = F.add(ev2, F.mul(F.mul(coef, x2), wx2))
    return ev0, ev1, ev2


def sumcheck_prove(fld, circ, witness, pads, label: bytes, root: bytes,
                   circuit_id: bytes):
    """ZkProver::prove up to the sumcheck part: the transcript after the
    label, the root and the statement; sumcheck_prove of
    sumcheck/prover.rs; alpha_input drawn last. Returns the padded proof
    per layer in the pad order, the challenges and the bytes of Section
    7.3."""
    F = fld["F"]
    codec = TV.FieldCodec(fld["F"].name)
    segments, ok = SC.eval_circuit(F, circ, witness)
    if not ok:
        fail("reference prover: the inputs do not satisfy the circuit")
    t = TV.Transcript(label)
    t.write_bytes(root)
    t.write_bytes(circuit_id)
    for x in witness[:circ["npublic"]]:
        t.write_elt(codec.to_bytes(x))
    t.write_elt(codec.to_bytes(0))
    t.write0(sum(len(terms) for _, _, terms in circ["layers"]))
    for _ in range(MAX_LOGW):
        codec.sample(t)
    g = [codec.sample(t) for _ in range(MAX_LOGW)]
    logv = ceil_lg2(circ["noutput"])
    cur = [g[:logv], g[:logv]]
    x2 = F.P2
    proof_layers = []
    pad_off = 0
    for j, (logw, nw, terms) in enumerate(circ["layers"]):
        alpha = codec.sample(t)
        beta = codec.sample(t)
        bound = []
        for g_, h0, h1, k in terms:
            dot = SC.eq2(F, g_, logv, cur[0], cur[1], alpha)
            kk = F.mul(beta if k == 0 else k, dot)
            bound.append([0, h0, h1, kk])
        active = [list(segments[j + 1]), list(segments[j + 1])]
        hp = [[], []]
        chall = [[], []]
        for r in range(logw):
            for hand in range(2):
                ev0, _, ev2 = eval_round_poly(
                    F, [tuple(b) for b in bound], active[hand], active[1 - hand],
                    hand, x2)
                padded = (F.sub(ev0, pads[pad_off + 4 * r + 2 * hand]),
                          F.sub(ev2, pads[pad_off + 4 * r + 2 * hand + 1]))
                t.write_elt(codec.to_bytes(padded[0]))
                t.write_elt(codec.to_bytes(padded[1]))
                c = codec.sample(t)
                chall[hand].append(c)
                hp[hand].append(padded)
                active[hand] = SC.bind(F, active[hand], c)
                one_minus_c = F.sub(1, c)
                for b in bound:
                    if b[1 + hand] % 2 == 0:
                        b[3] = F.mul(b[3], one_minus_c)
                    else:
                        b[3] = F.mul(b[3], c)
                    b[1 + hand] //= 2
        nxt = [active[0][0] if active[0] else 0, active[1][0] if active[1] else 0]
        claims = (F.sub(nxt[0], pads[pad_off + 4 * logw]),
                  F.sub(nxt[1], pads[pad_off + 4 * logw + 1]))
        t.write_slice([codec.to_bytes(claims[0]), codec.to_bytes(claims[1])])
        layer = []
        for r in range(logw):
            layer += [hp[0][r][0], hp[0][r][1], hp[1][r][0], hp[1][r][1]]
        layer += list(claims)
        proof_layers.append(layer)
        logv = logw
        cur = chall
        pad_off += 4 * logw + 3
    alpha_input = codec.sample(t)
    out = bytearray()
    for (logw, _, _), layer in zip(circ["layers"], proof_layers):
        for r in range(logw):
            for i in (4 * r, 4 * r + 2, 4 * r + 1, 4 * r + 3):
                out += codec.to_bytes(layer[i])
        out += codec.to_bytes(layer[4 * logw]) + codec.to_bytes(layer[4 * logw + 1])
    return proof_layers, (g, cur, alpha_input), bytes(out)


def sumcheck_cases(lines):
    """Block 3 (ADR 0053 tier 2): the Appendix B.3 circuits and the
    Z-assertion circuit proved by the reference above with Simple_Rng and
    chosen seeds, an arbitrary root and the circuit's identifier; the
    pads and the bytes of Section 7.3 for the harness to reproduce."""
    import hashlib
    cases = [
        ("gf2_128", SC.sgonal_gf2_128(), [1, 0x6C, 5, 6], 12345),
        ("gf2_128", SC.sgonal_gf2_128(), [1, 0x6C, 5, 6], 7),
        ("gf2_128", SC.zcheck(), [1, 0, 7], 3),
        ("p256", SC.sgonal_p256(), [1, 45, 5, 6], 123456789),
        ("p256", SC.sgonal_p256(), [1, 45, 5, 6], 11),
    ]
    for fname, circ, witness, seed in cases:
        fld = GC.FIELDS[fname]
        lfc2 = GC.write_lfc2(fld, circ, sfb=0)
        ident = lfc2[-32:]
        name = f"{circ['name']}_{seed}"
        root = hashlib.sha256(name.encode()).digest()
        rng = SimpleRng(seed)
        pads = sample_pads(fld, circ, rng)
        _, _, proof_bytes = sumcheck_prove(fld, circ, witness, pads, name.encode(),
                                           root, ident)
        hx = fld["hx"]
        lines.append(
            f"sumcheck {name} {fname} {seed} {name} {root.hex()} {lfc2.hex()} "
            f"{len(witness)} " + " ".join(hx(w) for w in witness)
            + f" {len(pads)} " + " ".join(hx(p) for p in pads)
            + f" {proof_bytes.hex()}")


GL = load_sibling("gen_ligero_vectors")


def sample_sub(fld, glf, rng) -> int:
    """BinarySubfield::sample: 2 bytes on the basis of GF(2^16) in
    GF(2^128); on P-256 the field's own sampler (the field is its own
    subfield)."""
    if fld["binary"]:
        return glf.point(int.from_bytes(rng.bytes(2), "little"))
    return sample_elt(fld, rng)


def lqc_triples(circ):
    """generate_lqc_triples of zk/common.rs on the witness vector."""
    pi = circ["ninput"] - circ["npublic"]
    lqc = []
    for logw, _, _ in circ["layers"]:
        pi += 4 * logw
        lqc.append((pi, pi + 1, pi + 2))
        pi += 3
    return lqc


def ligero_commit(fld, geom, witness, lqc, sfb, rng):
    """layout_tableau and commit of ligero/prover.rs, commit_merkle_heap
    of merkle.rs: the unencoded rows, the encoded tableau, the nonces,
    the heap layers and the root. sfb is the boundary within the
    witness vector."""
    F = fld["F"]
    glf = GL.GF2128() if fld["binary"] else GL.P256()
    codec = TV.FieldCodec(F.name)
    ncol, nreq = geom["ncol"], geom["nreq"]
    block, dblock, wr = geom["block"], geom["dblock"], geom["wr"]
    pts = [glf.point(x) for x in range(ncol)]
    _, lb = GL.lagrange_matrix(glf, pts, block, ncol)
    _, ld = GL.lagrange_matrix(glf, pts, dblock, ncol)
    enc_b = lambda row: GL.encode_row(glf, lb, block, ncol, row)
    enc_d = lambda row: GL.encode_row(glf, ld, dblock, ncol, row)
    raw, tab = [], []
    # row 0, ILDT
    row = [sample_elt(fld, rng) for _ in range(block)]
    raw.append(row)
    tab.append(enc_b(row))
    # row 1, IDOT
    row = [sample_elt(fld, rng) for _ in range(dblock)]
    s = 0
    for v in row[nreq:nreq + wr]:
        s = F.add(s, v)
    row[nreq] = F.sub(row[nreq], s)
    raw.append(row)
    tab.append(enc_d(row))
    # row 2, IQUAD
    row = [sample_elt(fld, rng) for _ in range(dblock)]
    for j in range(wr):
        row[nreq + j] = 0
    raw.append(row)
    tab.append(enc_d(row))
    # witness rows
    nw = len(witness)
    for i in range(geom["nwrow"]):
        sub = (i + 1) * wr <= sfb
        row = [0] * block
        for k in range(nreq):
            row[k] = sample_sub(fld, glf, rng) if sub else sample_elt(fld, rng)
        start = i * wr
        for j in range(wr):
            if start + j < nw:
                row[nreq + j] = witness[start + j]
        raw.append(row)
        tab.append(enc_b(row))
    # quadratic constraint rows: x, y, z sampled per row index, placed
    # as three groups
    nq = len(lqc)
    groups = ([], [], [])
    for i in range(geom["nqt"]):
        start = i * wr
        for h in range(3):
            row = [0] * block
            for k in range(nreq):
                row[k] = sample_elt(fld, rng)
            for j in range(wr):
                if start + j < nq:
                    row[nreq + j] = witness[lqc[start + j][h]]
            groups[h].append(row)
    for h in range(3):
        for row in groups[h]:
            raw.append(row)
            tab.append(enc_b(row))
    if len(tab) != geom["nrow"]:
        fail("reference commit: row count")
    # nonces, then the leaves, then the heap
    nl = ncol - dblock
    nonces = [rng.bytes(32) for _ in range(nl)]
    leaves = []
    for j in range(nl):
        data = nonces[j] + b"".join(codec.to_bytes(tab[r][dblock + j])
                                    for r in range(geom["nrow"]))
        leaves.append(GL.sha256(data))
    layers = GL.merkle_heap(leaves)
    return raw, tab, nonces, leaves, layers, layers[1]


def commit_cases(lines):
    """Block 4 (ADR 0053 tier 2): the commitment of the reference above on
    the sumcheck cases' circuits and seeds under the B.3 configuration,
    plus a subfield case; the root, the unencoded rows and one opening."""
    cases = [
        ("gf2_128", SC.sgonal_gf2_128(), [1, 0x6C, 5, 6], 12345, (4, 6, 64), 0),
        ("gf2_128", SC.sgonal_gf2_128(), [1, 0x6C, 5, 6], 7, (4, 6, 64), 0),
        ("gf2_128", SC.sgonal_gf2_128(), [1, 0x6C, 5, 6], 5, (4, 8, 64), 3),
        ("gf2_128", SC.zcheck(), [1, 0, 7], 3, (4, 6, 64), 0),
        ("p256", SC.sgonal_p256(), [1, 45, 5, 6], 123456789, (4, 6, 64), 0),
        ("p256", SC.sgonal_p256(), [1, 45, 5, 6], 11, (4, 6, 64), 0),
    ]
    for fname, circ, inputs, seed, (rate_inv, nreq, ncol), sfb in cases:
        fld = GC.FIELDS[fname]
        lfc2 = GC.write_lfc2(fld, circ, sfb=sfb)
        name = f"{circ['name']}_{seed}" + ("_sub" if sfb else "")
        rng = SimpleRng(seed)
        pads = sample_pads(fld, circ, rng)
        witness = inputs[circ["npublic"]:] + pads
        lqc = lqc_triples(circ)
        geom = GL.geometry(rate_inv, nreq, ncol, len(witness), len(lqc))
        if geom is None:
            fail(f"commit case {name}: invalid configuration")
        geom["ncol"], geom["nreq"] = ncol, nreq
        sfb_w = max(sfb - circ["npublic"], 0)
        raw, tab, nonces, leaves, layers, root = ligero_commit(
            fld, geom, witness, lqc, sfb_w, rng)
        nl = ncol - geom["dblock"]
        idx = random.Random(seed).sample(range(nl), nreq)
        path = GL.merkle_open(layers, nl, idx)
        if not GL.merkle_verify(nl, root, idx, [leaves[i] for i in idx], path):
            fail(f"commit case {name}: the opening does not verify")
        hx = fld["hx"]
        rows = " ".join(f"{len(r)} " + " ".join(hx(v) for v in r) for r in raw)
        lines.append(
            f"commit {name} {fname} {seed} {rate_inv} {nreq} {ncol} {lfc2.hex()} "
            f"{len(inputs)} " + " ".join(hx(w) for w in inputs)
            + f" {root.hex()} {len(raw)} {rows} {len(idx)} "
            + " ".join(str(i) for i in idx)
            + f" {len(path)} " + " ".join(d.hex() for d in path))


def root_cases(lines):
    """Block 4 (ADR 0053 tier 1): the roots of the two upstream proofs,
    with the inputs of the upstream JSON files as elements."""
    import json
    cases = [
        ("sha256", "gf2_128", 12345, (3, 16, 256)),
        ("ecdsa2", "p256", 123456789, (4, 16, 256)),
    ]
    for name, fname, seed, (rate_inv, nreq, ncol) in cases:
        fld = GC.FIELDS[fname]
        base = f"tests/vectors/upstream/circuits/{name}"
        raw = json.loads((HERE / "upstream" / "circuits" / f"{name}_inputs.json")
                         .read_text())
        inputs = []
        for s in raw:
            v = int(s)
            if fld["mod"] is not None:
                v %= fld["mod"]
            elif v >= 2**128:
                fail(f"root case {name}: input does not fit 16 bytes")
            inputs.append(v)
        root = (HERE / "upstream" / "circuits" / f"{name}_proof.bin").read_bytes()[:32]
        hx = fld["hx"]
        lines.append(
            f"root {name} {fname} {seed} {rate_inv} {nreq} {ncol} "
            f"path:{base}_circuit.lfc2 {len(inputs)} "
            + " ".join(hx(w) for w in inputs) + f" {root.hex()}")


def prove_cases(lines):
    """Block 5 (ADR 0053): the complete prover on the small circuits, the
    statuses of ADR 0049 and completeness through Zk_Verifier."""
    cases = [
        ("gf2_128", SC.sgonal_gf2_128(), [1, 0x6C, 5, 6], 12345, (4, 6, 64), 0, "ok"),
        ("gf2_128", SC.sgonal_gf2_128(), [1, 0x6C, 5, 6], 7, (4, 6, 64), 0, "ok"),
        ("gf2_128", SC.zcheck(), [1, 0, 7], 3, (4, 6, 64), 0, "ok"),
        ("p256", SC.sgonal_p256(), [1, 45, 5, 6], 123456789, (4, 6, 64), 0, "ok"),
        ("p256", SC.sgonal_p256(), [1, 45, 5, 6], 11, (4, 6, 64), 0, "ok"),
        ("gf2_128", SC.sgonal_gf2_128(), [1, 0x6C, 5], 1, (4, 6, 64), 0,
         "input_length"),
        ("gf2_128", SC.sgonal_gf2_128(), [1, 0x6C, 5, 7], 1, (4, 6, 64), 0,
         "not_satisfied"),
        ("gf2_128", SC.zcheck(), [1, 1, 7], 1, (4, 6, 64), 0, "not_satisfied"),
        ("p256", SC.sgonal_p256(), [1, 45, 5, 7], 1, (4, 6, 64), 0,
         "not_satisfied"),
        # boundary 4 with WR 4: no witness row lies wholly below it, nothing
        # is projected, the proof is valid (as the reference's would be)
        ("gf2_128", SC.sgonal_gf2_128(), [1, 0x6C, 5, 6], 2, (4, 6, 64), 4, "ok"),
        # boundary 4 with WR 2: the first witness row (inputs 1 and 2) is
        # projected and 0x6c is not in GF(2^16)
        ("gf2_128", SC.sgonal_gf2_128(), [1, 0x6C, 5, 6], 1, (4, 8, 64), 4,
         "not_in_subfield"),
        # P-256 encodes by Lagrange: 8192 columns exceed the parity columns
        # one table holds. GF(2^128) encodes by the additive FFT (ADR 0057),
        # whose points must lie in GF(2^16): 70000 columns exceed it, as
        # can_encode of lch14_reed_solomon.rs refuses them.
        ("p256", SC.sgonal_p256(), [1, 45, 5, 7], 1, (1, 16, 8192), 0,
         "config_invalid"),
        ("gf2_128", SC.sgonal_gf2_128(), [1, 0x6C, 5, 6], 1, (2, 16, 70000), 0,
         "config_invalid"),
    ]
    seen = set()
    for fname, circ, inputs, seed, (rate_inv, nreq, ncol), sfb, status in cases:
        fld = GC.FIELDS[fname]
        lfc2 = GC.write_lfc2(fld, circ, sfb=sfb)
        name = f"{circ['name']}_{seed}_{status}"
        while name in seen:
            name += "_"
        seen.add(name)
        if status == "not_in_subfield":
            # the inputs below the boundary are not all in GF(2^16): the
            # basis injects 1 to 1, the others are wide elements
            glf = GL.GF2128()
            if all(w in {glf.point(x) for x in range(2**16)} for w in inputs[1:]):
                fail("prove case not_in_subfield: inputs lie in the subfield")
        hx = fld["hx"]
        lines.append(
            f"prove {name} {fname} {seed} {rate_inv} {nreq} {ncol} {lfc2.hex()} "
            f"{len(inputs)} " + " ".join(hx(w) for w in inputs) + f" {status}")


def main() -> None:
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE
    out_dir.mkdir(parents=True, exist_ok=True)
    sumcheck_lines = [
        "# Phase C, block 3 (ADR 0053, tier 2): the sumcheck prover of Section",
        "# 6.6 run by the reference prover of gen_prover_vectors.py on the",
        "# Appendix B.3 circuits and the Z-assertion circuit, with Simple_Rng",
        "# (the generator of the upstream reference test) under the given seed,",
        "# the label equal to the case name, an arbitrary root and the circuit's",
        "# identifier. Sumcheck_Prover must draw the same pads and produce the",
        "# same padded proof, written in the order of Section 7.3.",
        "#   sumcheck <name> <field> <seed> <label> <root> <circuit lfc2>",
        "#            <nwit> <witness...> <npads> <pads...> <proof bytes>",
        "# Generated by gen_prover_vectors.py (this directory); do not edit.",
    ]
    sumcheck_cases(sumcheck_lines)
    (out_dir / "sumcheck_prover.txt").write_text("\n".join(sumcheck_lines) + "\n")
    commit_lines = [
        "# Phase C, block 4 (ADR 0053): the Ligero commitment of Section 4.3.",
        "# commit lines (tier 2): the reference commitment of",
        "# gen_prover_vectors.py on the witness vector (private inputs, then",
        "# the pads drawn first from Simple_Rng under the seed) with the given",
        "# configuration and the circuit's subfield boundary: the Merkle root,",
        "# the unencoded rows (k elements each, equal to the systematic part of",
        "# the encoded rows) and one batch opening for the given leaf indices.",
        "#   commit <name> <field> <seed> <rate_inv> <nreq> <ncol> <circuit lfc2>",
        "#          <nin> <inputs...> <root> <nrow> {<k> <row...>} <nidx> <idx...>",
        "#          <npath> <path...>",
        "# root lines (tier 1): the first 32 bytes of the upstream proof files,",
        "# to be reproduced from the upstream inputs and seed.",
        "#   root <name> <field> <seed> <rate_inv> <nreq> <ncol> <circuit path>",
        "#        <nin> <inputs...> <root>",
        "# Generated by gen_prover_vectors.py (this directory); do not edit.",
    ]
    commit_cases(commit_lines)
    root_cases(commit_lines)
    (out_dir / "ligero_commit.txt").write_text("\n".join(commit_lines) + "\n")
    prove_lines = [
        "# Phase C, block 5 (ADR 0049, 0053): the complete prover Zk_Prover.Prove",
        "# on the small circuits, with Simple_Rng under the seed, the case name",
        "# as label and the circuit's identifier: the status it must report and,",
        "# on ok, acceptance of the proof by Zk_Verifier (completeness, tested).",
        "#   prove <name> <field> <seed> <rate_inv> <nreq> <ncol> <circuit lfc2>",
        "#         <nin> <inputs...> <status>",
        "# Generated by gen_prover_vectors.py (this directory); do not edit.",
    ]
    prove_cases(prove_lines)
    (out_dir / "zk_prove.txt").write_text("\n".join(prove_lines) + "\n")
    lines = [
        "# Phase C, block 2 (ADR 0053): the writers of Sections 7.3, 7.4 and 7.5",
        "# as inverses of the readers. Each proof of the repository, read by",
        "# Zk_Verifier.Read_Proof on its circuit and written back by Proof_Writer,",
        "# must give the same bytes; a mismatch is reported at its first offset.",
        "#   roundtrip <name> <field> <circuit> <proof> <rate_inv> <nreq> <ncol>",
        "# with <circuit> and <proof> as hex:<bytes> or path:<file>.",
        "# Generated by gen_prover_vectors.py (this directory); do not edit.",
    ]
    for field, circ in (("gf2_128", SC.sgonal_gf2_128()), ("p256", SC.sgonal_p256())):
        fld = GC.FIELDS[field]
        lfc2 = GC.write_lfc2(fld, circ, sfb=0)
        proof, cfg = b3_proof(field, circ["name"])
        lines.append(f"roundtrip {circ['name']} {field} hex:{lfc2.hex()} "
                     f"hex:{proof.hex()} {cfg[0]} {cfg[1]} {cfg[2]}")
    base = "tests/vectors/upstream/circuits"
    lines.append(f"roundtrip sha256 gf2_128 path:{base}/sha256_circuit.lfc2 "
                 f"path:{base}/sha256_proof.bin 3 16 256")
    lines.append(f"roundtrip ecdsa2 p256 path:{base}/ecdsa2_circuit.lfc2 "
                 f"path:{base}/ecdsa2_proof.bin 4 16 256")
    (out_dir / "writer.txt").write_text("\n".join(lines) + "\n")
    print(f"gen_prover_vectors: wrote ligero_commit.txt (6 commit and 2 root "
          f"cases), zk_prove.txt (12 cases), writer.txt (4 round trips) and "
          f"sumcheck_prover.txt (5 cases) to {out_dir}")


if __name__ == "__main__":
    main()
