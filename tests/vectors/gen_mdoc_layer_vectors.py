#!/usr/bin/env python3
"""Generator for the mDoc layer vectors (Phase D, block 5, ADR 0058):
  mdoc_layer.txt   head <name> <major> <n> <bytes>
               the CBOR head of a text (60) or byte (40) string of n bytes
               (Cbor_Encode.Head);
                   mac <name> <av> <ap>x6 <m>x3 <tag>x6
               the six legacy tags (mac.rs, push_legacy_macs) of the three
               32-byte messages under av and the six pads
               (Mdoc_Mac.Legacy_Tags);
                   e2 <name> <transcript> <doc_type> <digest>
               the device authentication digest of a session transcript and
               a document type (cbor/mdoc.rs, compute_transcript_hash;
               Device_Auth.Digest);
                   hash_inputs <name> <version> <n> {<id> <value>} <now>
                               <tag>x6 <av> <count> <digest>
               the public inputs of the hash circuit (legacy/public.rs,
               push_legacy_input_hash) for n attributes: their count and
               the SHA-256 of their little-endian bytes, 16 per element
               (Mdoc_Inputs.Hash_Inputs);
                   sig_inputs <name> <pkx> <pky> <e2> <tag>x6 <av> <digest>
               the 900 public inputs of the signature circuit
               (push_legacy_input_sig): the SHA-256 of their canonical
               little-endian bytes, 32 per element (Mdoc_Inputs.Sig_Inputs);
                   witness <name> <hash path> <sig path> <npublic> <ap>x6 <m>x3
               the ends of the hash circuit's witness in an upstream witness
               file: the six pads (its last six elements) and the three
               messages (its first 768 private elements, as bits)
               (Mdoc_Inputs.Witness_Parts); the same pads encoded at the end
               of the signature witness (Sig_Pads_Match, Place_Pads);
                   spec <index> <version> <n> <combined> <sig_id> <hash_id>
                        <rate> <nreq> <ncol> <rate> <nreq> <ncol>
               the rows of the table of specifications this project holds
               (zk_spec.rs, ZK_SPECS; Mdoc_Spec).

Elements of GF(2^128) are written as the 32 hex digits of their 16
little-endian bytes, elements of P-256 as the 64 hex digits of their 32
canonical little-endian bytes; byte strings as hex, "-" when empty.

The real cases come from upstream's artifacts under upstream/mdoc/ at
d5e6be7: the public parts of the two hash witness files and the signature
witness file are the public inputs of one run of upstream's prover on the
test case FAMILYNAME_MUSTERMANN_MDOC_3 of testcases/src/vectors.rs (the
attribute family_name with the text value "Mustermann", the date
2024-10-01T09:00:00Z, the document type org.iso.18013.5.1.mDL, a session
transcript of 143 bytes, the issuer key of that case), whose parameters
are the constants below. This generator rebuilds those public inputs from
the parameters with its own transcription of the builders and fails unless
they equal the files byte for byte, recomputes the six tags from the
witness ends and fails unless they equal the tags in the files: the check
that settles what the witness files are, made permanent. The synthetic
cases come from a fixed seed.

Usage: python3 -I gen_mdoc_layer_vectors.py [output-directory]
Output is deterministic.
"""

import hashlib
import importlib.util
import random
import sys
from pathlib import Path

HERE = Path(__file__).parent
MDOC = HERE / "upstream" / "mdoc"
OUT_DIR = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


GF = load("gen_gf2_128_vectors")

P256 = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF

# The two archives held (ADR 0055, ADR 0059): combined identifier, version,
# number of attributes, the two circuit identifiers (sig, hash), the two
# Ligero configurations (hash, sig) of ZK_SPECS.
SIG_ID = "2845210af05740e6e3e054762f9e35ff5fc4fb23088716e369f7cf73eb61df2d"
SPECS = [
    ("8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121", 7, 1,
     "58248d20ded3b19b0996e478dda6afacba794fa2b1f0802771430bc0dca7d106",
     (7, 132, 4151), (7, 132, 4096)),
    ("137e5a75ce72735a37c8a72da1a8a0a5df8d13365c2ae3d2c2bd6a0e7197c7c6", 6, 1,
     "039bed19b94d5d732e1de555fa5c5c4b9b189b8c7908d3f1ee4ecb9e72f38532",
     (4, 128, 4096), (4, 128, 2945)),
]

# The test case the witness files come from (FAMILYNAME_MUSTERMANN_MDOC_3).
CASE_PKX = 0xdc1c1f55cff4cd5c76cf4169278f7217667f86ee81d8669b63f2e19bc12a0c9f
CASE_PKY = 0x12355dd0385fed3bc33bedc9781b9aad47b33e4c24704b8d14288b1b3cb45c28
CASE_NOW = b"2024-10-01T09:00:00Z"
CASE_DOC_TYPE = b"org.iso.18013.5.1.mDL"
CASE_ATTR = (b"family_name", bytes.fromhex("6a4d75737465726d616e6e"))
CASE_TRANSCRIPT = bytes.fromhex(
    "83f6f6847142726f7773657248616e646f76657276315820f93ebac4ce4d9901b9ae"
    "a472145ae5421f8fbecbe5f0389683f59f08fcf90e455833a363636174016474797065"
    "016764657461696c73a1676261736555726c75687474703a2f2f6c6f63616c686f7374"
    "3a3830383058203c79914b7f81a1c2558fc81619dd4a074d32143e6cf6895fe47da156"
    "d1c5b0ae")


def fail(msg):
    print(f"gen_mdoc_layer_vectors: FAILED: {msg}", file=sys.stderr)
    sys.exit(1)


# ---------------------------------------------------------------- encodings

def gf_hex(v):
    return v.to_bytes(16, "little").hex()


def p_hex(v):
    return v.to_bytes(32, "little").hex()


def bytes_hex(b):
    return b.hex() if b else "-"


def gf_digest(elements):
    return hashlib.sha256(b"".join(e.to_bytes(16, "little") for e in elements)).hexdigest()


def p_digest(elements):
    return hashlib.sha256(b"".join(e.to_bytes(32, "little") for e in elements)).hexdigest()


# -------------------------------------------------- the builders transcribed

def head(major, n):
    if n <= 23:
        return bytes([major | n])
    if n <= 255:
        return bytes([major | 24, n])
    if n <= 65535:
        return bytes([major | 25]) + n.to_bytes(2, "big")
    return bytes([major | 26]) + n.to_bytes(4, "big")


def bits(v, n):
    return [(v >> k) & 1 for k in range(n)]


def raw_bytes(b):
    out = []
    for x in b:
        out += bits(x, 8)
    return out


def hash_inputs(version, attrs, now, tags, av):
    out = [1]
    for ident, value in attrs:
        if version >= 7:
            vbuf = head(0x60, len(ident)) + ident
            out += raw_bytes(vbuf) + [0] * ((32 - len(vbuf)) * 8)
            out += raw_bytes(value) + [0] * ((64 - len(value)) * 8)
            out += bits(1 + 17 + 1 + len(ident), 8)
            out += bits(len(value) + 12 + 1, 8)
        else:
            vbuf = head(0x60, len(ident)) + ident + head(0x60, 12) + b"elementValue" + value
            out += raw_bytes(vbuf) + [0] * ((96 - len(vbuf)) * 8)
            out += bits(len(vbuf), 8)
    out += raw_bytes(now) + [2] * ((20 - len(now)) * 8)
    out += list(tags) + [av]
    return out


def sig_inputs(pkx, pky, e2, tags, av):
    out = [1, pkx, pky, e2]
    for t in tags:
        out += bits(t, 128)
    out += bits(av, 128)
    return out


def legacy_tags(av, ap, msgs):
    tags = []
    for i in range(3):
        m0 = int.from_bytes(msgs[i][:16], "little")
        m1 = int.from_bytes(msgs[i][16:], "little")
        tags.append(GF.mul(av ^ ap[i][0], m0))
        tags.append(GF.mul(av ^ ap[i][1], m1))
    return tags


def e2_digest(transcript, doc_type):
    auth = (bytes([0x84, 0x74]) + b"DeviceAuthentication" + transcript
            + head(0x60, len(doc_type)) + doc_type + bytes([0xD8, 0x18, 0x41, 0xA0]))
    payload = bytes([0xD8, 0x18]) + head(0x40, len(auth)) + auth
    sig1 = (bytes([0x84, 0x6A]) + b"Signature1" + bytes([0x43, 0xA1, 0x01, 0x26, 0x40])
            + head(0x40, len(payload)) + payload)
    return hashlib.sha256(sig1).digest()


def hash_count(version, n):
    return 1 + n * (784 if version >= 7 else 776) + 160 + 7


# ------------------------------------------------------------------ the cases

def main():
    lines = ["# mDoc layer vectors (ADR 0058), written by gen_mdoc_layer_vectors.py;",
             "# the real cases from upstream's witness files at d5e6be7, the others",
             "# from a fixed seed. Do not edit by hand."]
    rng = random.Random(20261108)

    # The CBOR heads.
    for n in [0, 1, 23, 24, 100, 255, 256, 1000, 65535, 65536, 70000]:
        for major in (0x60, 0x40):
            lines.append(f"head n{n}_{major:02x} {major:02x} {n} {head(major, n).hex()}")

    # The specifications.
    for index, (combined, version, nattr, hash_id, hcfg, scfg) in enumerate(SPECS, 1):
        if hashlib.sha256(bytes.fromhex(SIG_ID) + bytes.fromhex(hash_id)).hexdigest() != combined:
            fail(f"the combined identifier of {combined} is not SHA-256 (sig || hash)")
        lines.append(f"spec {index} {version} {nattr} {combined} {SIG_ID} {hash_id} "
                     f"{hcfg[0]} {hcfg[1]} {hcfg[2]} {scfg[0]} {scfg[1]} {scfg[2]}")

    # The real cases: the witness files of both archives.
    real_e2 = e2_digest(CASE_TRANSCRIPT, CASE_DOC_TYPE)
    e2_le = int.from_bytes(real_e2, "big")
    if e2_le >= P256:
        fail("the test case's e2 is not below p")
    for combined, version, nattr, hash_id, hcfg, scfg in SPECS:
        tag = f"v{version}"
        hw = (MDOC / f"{combined}_hash_witness.bin").read_bytes()
        sw = (MDOC / f"{combined}_sig_witness.bin").read_bytes()
        npub = hash_count(version, 1)
        H = [int.from_bytes(hw[16 * i:16 * i + 16], "little") for i in range(len(hw) // 16)]
        S = [int.from_bytes(sw[32 * i:32 * i + 32], "little") for i in range(900)]
        av = H[npub - 1]
        tags = H[npub - 7:npub - 1]
        # The public inputs of the hash circuit, rebuilt.
        rebuilt = hash_inputs(version, [CASE_ATTR], CASE_NOW, tags, av)
        if rebuilt != H[:npub]:
            fail(f"{tag}: the hash public inputs rebuilt differ from the witness file")
        lines.append(f"hash_inputs real_{tag} {version} 1 {CASE_ATTR[0].hex()} {CASE_ATTR[1].hex()} "
                     f"{CASE_NOW.hex()} {' '.join(gf_hex(t) for t in tags)} {gf_hex(av)} {npub} "
                     f"{hashlib.sha256(hw[:16 * npub]).hexdigest()}")
        # The public inputs of the signature circuit, rebuilt.
        if S[1] != CASE_PKX or S[2] != CASE_PKY:
            fail(f"{tag}: the issuer key in the signature witness is not the test case's")
        if S[3] != e2_le:
            fail(f"{tag}: e2 in the signature witness is not the test case's")
        if sig_inputs(CASE_PKX, CASE_PKY, e2_le, tags, av) != S:
            fail(f"{tag}: the signature public inputs rebuilt differ from the witness file")
        lines.append(f"sig_inputs real_{tag} {p_hex(CASE_PKX)} {p_hex(CASE_PKY)} {p_hex(e2_le)} "
                     f"{' '.join(gf_hex(t) for t in tags)} {gf_hex(av)} "
                     f"{hashlib.sha256(sw[:32 * 900]).hexdigest()}")
        # The ends of the witness, and the tags recomputed from them.
        priv = H[npub:]
        ap = [[priv[-6 + 2 * i], priv[-6 + 2 * i + 1]] for i in range(3)]
        msgs = []
        for i in range(3):
            chunk = priv[256 * i:256 * (i + 1)]
            if any(e not in (0, 1) for e in chunk):
                fail(f"{tag}: a message element of the witness is not a bit")
            msgs.append(bytes(sum(chunk[8 * j + k] << k for k in range(8)) for j in range(32)))
        if legacy_tags(av, ap, msgs) != tags:
            fail(f"{tag}: the tags recomputed from the witness differ from the file's")
        # The pads and the halves of the messages at the end of the signature
        # witness, as elements of two bits: 2 v - 3.
        S_all = [int.from_bytes(sw[32 * i:32 * i + 32], "little") for i in range(len(sw) // 32)]

        def plucked(v):
            return [(2 * ((v >> (2 * k)) & 3) - 3) % P256 for k in range(64)]
        tail = []
        for i in range(3):
            m = int.from_bytes(msgs[i], "little")
            tail += plucked(ap[i][0]) + plucked(ap[i][1]) + plucked(m & ((1 << 128) - 1)) + plucked(m >> 128)
        if S_all[-768:] != tail:
            fail(f"{tag}: the tail of the signature witness is not the pads and the messages")
        aps = " ".join(gf_hex(ap[i][h]) for i in range(3) for h in range(2))
        ms = " ".join(m.hex() for m in msgs)
        lines.append(f"witness real_{tag} tests/vectors/upstream/mdoc/{combined}_hash_witness.bin "
                     f"tests/vectors/upstream/mdoc/{combined}_sig_witness.bin {npub} {aps} {ms}")
        lines.append(f"mac real_{tag} {gf_hex(av)} {aps} {ms} {' '.join(gf_hex(t) for t in tags)}")
    lines.append(f"e2 real {CASE_TRANSCRIPT.hex()} {CASE_DOC_TYPE.hex()} {real_e2.hex()}")

    # Synthetic tags.
    for k in range(4):
        av = rng.getrandbits(128)
        ap = [[rng.getrandbits(128), rng.getrandbits(128)] for _ in range(3)]
        msgs = [rng.getrandbits(256).to_bytes(32, "little") for _ in range(3)]
        if k == 3:
            av, ap[0][0] = 0, 0
        tags = legacy_tags(av, ap, msgs)
        aps = " ".join(gf_hex(ap[i][h]) for i in range(3) for h in range(2))
        lines.append(f"mac rand{k} {gf_hex(av)} {aps} {' '.join(m.hex() for m in msgs)} "
                     f"{' '.join(gf_hex(t) for t in tags)}")

    # Synthetic digests: an empty transcript, a long document type (a head
    # of two bytes), a document type above 255 bytes (a head of three
    # bytes), a transcript above 255 bytes (a head of three bytes).
    for name, tr, doc in [("empty", b"", b"a"),
                          ("long_doc", bytes(rng.getrandbits(8) for _ in range(40)), b"x" * 30),
                          ("longer_doc", bytes(rng.getrandbits(8) for _ in range(40)), b"y" * 300),
                          ("long_transcript", bytes(rng.getrandbits(8) for _ in range(300)),
                           CASE_DOC_TYPE)]:
        lines.append(f"e2 {name} {bytes_hex(tr)} {bytes_hex(doc)} {e2_digest(tr, doc).hex()}")

    # Synthetic public inputs of the hash circuit.
    def hash_case(name, version, attrs, now):
        av = rng.getrandbits(128)
        tags = [rng.getrandbits(128) for _ in range(6)]
        elements = hash_inputs(version, attrs, now, tags, av)
        if len(elements) != hash_count(version, len(attrs)):
            fail(f"{name}: the count formula is wrong")
        pieces = " ".join(f"{bytes_hex(i)} {bytes_hex(v)}" for i, v in attrs)
        lines.append(f"hash_inputs {name} {version} {len(attrs)} {pieces} {bytes_hex(now)} "
                     f"{' '.join(gf_hex(t) for t in tags)} {gf_hex(av)} {len(elements)} "
                     f"{gf_digest(elements)}")

    age = (b"age_over_18", bytes([0xF5]))
    hash_case("age_v7", 7, [age], b"2025-04-30T00:00:00Z")
    hash_case("age_v6", 6, [age], b"2025-04-30T00:00:00Z")
    hash_case("short_now_v7", 7, [age], b"2025-04-30")
    hash_case("long_id_v7", 7, [(b"x" * 24, bytes(rng.getrandbits(8) for _ in range(64)))],
              b"2025-04-30T00:00:00Z")
    hash_case("two_attrs_v7", 7, [age, (b"issuing_country", bytes.fromhex("624445"))],
              b"2025-04-30T00:00:00Z")
    hash_case("two_attrs_v6", 6, [age, CASE_ATTR], b"2025-04-30T00:00:00Z")
    hash_case("no_attrs_v7", 7, [], b"2025-04-30T00:00:00Z")

    # Synthetic public inputs of the signature circuit.
    for k in range(2):
        pkx, pky, e2 = (rng.getrandbits(256) % P256 for _ in range(3))
        av = rng.getrandbits(128)
        tags = [rng.getrandbits(128) for _ in range(6)]
        lines.append(f"sig_inputs rand{k} {p_hex(pkx)} {p_hex(pky)} {p_hex(e2)} "
                     f"{' '.join(gf_hex(t) for t in tags)} {gf_hex(av)} "
                     f"{p_digest(sig_inputs(pkx, pky, e2, tags, av))}")

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    (OUT_DIR / "mdoc_layer.txt").write_text("\n".join(lines) + "\n")
    print(f"gen_mdoc_layer_vectors: {len(lines) - 3} cases written to {OUT_DIR / 'mdoc_layer.txt'}")


if __name__ == "__main__":
    main()
