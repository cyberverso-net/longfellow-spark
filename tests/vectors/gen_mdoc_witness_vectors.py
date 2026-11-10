#!/usr/bin/env python3
"""Known-answer vectors for Mdoc_Witness (Phase D, block 6, ADR 0086): an
independent Python transcription of upstream's witness builders for the
mDoc proof of age (runtime/src/concrete/legacy/private.rs at d5e6be7:
push_witness_hash, push_witness_attrs, push_witness_sig, with the
encodings of concrete/builder.rs), run on upstream's 38 test documents
(upstream/mdoc/testcases/) and on synthetic documents built here.

The transcription reuses the parse, the SHA-256 trace and the document
builder of gen_mdoc_parse_vectors.py, the ECDSA witness of
gen_ecdsa_witness_vectors.py and the subfield basis of
gen_gf2_128_vectors.py.

Before writing anything the script checks its own transcription against
upstream's witness files of both archives (upstream/mdoc/): both witnesses
built from FAMILYNAME_MUSTERMANN_MDOC_3 under the pads mac_ap the hash
witness file holds must equal the files' private parts, element by
element; it fails otherwise.

usage: gen_mdoc_witness_vectors.py [OUT_DIR]   (default: this directory)

Output: mdoc_witness.txt. Format: '#' comments and blank lines are skipped;
one case per line, fields separated by blanks; an attribute is
<id_hex>:<value_hex>, the identifier's bytes and the value's CBOR:
  witness_file <case> <archive> <version> <npub_hash> <npub_sig> <attr>
                                        both witnesses built from the test
                                        case under the pads of the archive's
                                        hash witness file equal the files'
                                        private parts (the harness compares)
  witness <case> <version> <n> <attr>... <hash_digest> <sig_digest>
                                        the digests of both witnesses of the
                                        test case at the version, with the n
                                        attributes, under the fixed pads
  witness_reject <case> <version> <n> <attr>... <status>
                                        a refusal on a test case
  witness_hex <name> <hex> <version> <n> <attr>... <hash_digest> <sig_digest>
                                        a synthetic document, parsed with an
                                        empty transcript and the document
                                        type "x", under the key of the
                                        archives' test case
  reject_hex <name> <hex> <version> <n> <attr>... <status>
                                        a synthetic document refused; the
                                        order_* cases are the 24 orders of
                                        the four entries of an item, at
                                        version 6 refused unless
                                        elementValue follows
                                        elementIdentifier (#150)

The fixed pads: pad H of message I (I = 0 .. 2, H = 0 .. 1) is the element
whose 16 little-endian bytes are ((16 (2 I + H) + K) 7 + 1) mod 256 for
K = 0 .. 15. The digests are the SHA-256 of the elements as little-endian
bytes, 16 each for the hash witness and 32 for the signature witness.
"""
import hashlib
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_mdoc_parse_vectors as mp   # noqa: E402
import gen_ecdsa_witness_vectors as ew   # noqa: E402
from gen_gf2_128_vectors import UPSTREAM_SUBFIELD_BASIS as BASIS   # noqa: E402

MDOC_DIR = HERE / "upstream" / "mdoc"
V7 = "8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121"
V6 = "137e5a75ce72735a37c8a72da1a8a0a5df8d13365c2ae3d2c2bd6a0e7197c7c6"
CASE = "FAMILYNAME_MUSTERMANN_MDOC_3"
CASE_ATTR = (b"family_name", bytes.fromhex("6a4d75737465726d616e6e"))
NPUB_HASH = {7: 952, 6: 944}
NPUB_SIG = 900
P = ew.P
Q = ew.Q
MAX_ITEM_BYTES = 2 * 64 - 9
MAX_ATTRIBUTES = 4
MAX_ID_LEN = 64
MAX_VALUE_LEN = 96


def fail(msg):
    print(f"gen_mdoc_witness_vectors: {msg}", file=sys.stderr)
    sys.exit(1)


# ---------------------------------------------------------------------------
# The encodings of builder.rs, over GF(2^128) elements as integers.
# ---------------------------------------------------------------------------

def inject(x):
    """The subfield element of the 16-bit value x: the xor of the basis
    elements at its set bits."""
    e = 0
    for i in range(16):
        if (x >> i) & 1:
            e ^= BASIS[i]
    return e


def bits(v, n):
    return [(v >> k) & 1 for k in range(n)]


def raw_bytes(b):
    out = []
    for x in b:
        out += bits(x, 8)
    return out


def v32_legacy(x):
    """push_v32_legacy: eight 4-bit chunks, least significant first, the
    chunk c as the subfield element with bits (c << 1) ^ 15."""
    return [inject(((x >> (4 * k)) & 15) << 1 ^ 15) for k in range(8)]


def block_trace(h, block):
    """One block's 184 words: w[16..63], (e_i, a_i) interleaved, the new
    state; and the new state."""
    w, e, a, h1 = mp.compress_traced(h, block)
    out = []
    for x in w:
        out += v32_legacy(x)
    for i in range(64):
        out += v32_legacy(e[i]) + v32_legacy(a[i])
    for x in h1:
        out += v32_legacy(x)
    return out, h1


def value_header_len(v):
    """val_header_len of private.rs: the head of the request's value."""
    if not v:
        return 0
    b = v[0]
    if b == 0xD9:
        return 5 if len(v) > 3 and v[3] in (0x78, 0x58) else 4
    if 0x60 <= b <= 0x77 or 0x40 <= b <= 0x57:
        return 1
    if b in (0x78, 0x58):
        return 2
    if b in (0x79, 0x59):
        return 3
    return 0


def find_item(p, mdoc, ident):
    for i, it in enumerate(p["items"]):
        if mdoc[it["name_start"]:it["name_start"] + it["name_len"]] == ident:
            return i
    return None


def hash_witness(version, mdoc, p, attrs, pads):
    """The private inputs of the hash circuit, or a status string."""
    mb = mp.max_blocks(version)
    w = []
    for v in (p["issuer_sig_digest"], p["device_pk_x"], p["device_pk_y"]):
        w += bits(int.from_bytes(v, "big"), 256)
    wrapped = mdoc[p["mso_start"]:p["mso_start"] + p["mso_len"]]
    message = mp.SIGNING_HEADER + bytes([0x59]) + p["mso_len"].to_bytes(2, "big") + wrapped
    nb, padded = mp.pad_message(message, mb)
    w += bits(nb, 8)
    w += raw_bytes(padded[18:])
    h = list(mp.H0)
    for b in range(mb):
        t, h = block_trace(h, padded[64 * b:64 * b + 64])
        w += t
    for k in ("valid_from_offset", "valid_until_offset", "device_key_info_offset", "value_digests_offset"):
        w += bits(p[k], 12)
    for ident, value in attrs:
        i = find_item(p, mdoc, ident)
        if i is None:
            return "attribute_not_found"
        it = p["items"][i]
        if it["item_len"] > MAX_ITEM_BYTES:
            return "attribute_too_long"
        perm = it["permutation"]
        if version < 7 and (perm >> 6) & 3 != ((perm >> 4) & 3) + 1:
            # The version 6 circuit checks the identifier's text, the key
            # elementValue and the value as one span (#150).
            return "item_order_unsupported"
        item = mdoc[it["item_start"]:it["item_start"] + it["item_len"]]
        nb2, pad2 = mp.pad_message(item, 2)
        w += raw_bytes(pad2)
        h2 = list(mp.H0)
        for b in range(2):
            t, h2 = block_trace(h2, pad2[64 * b:64 * b + 64])
            w += t
        w += bits(it["digest_offset"], 12)
        perm = it["permutation"]
        slot_ei, slot_ev = (perm >> 4) & 3, (perm >> 6) & 3
        if version < 7:
            val_len = max(len(value) - value_header_len(value), 0)
            ei_pos, ei_len = it["slot"][slot_ei] + 18, len(ident) + val_len + 13
            ev_pos, ev_len = it["slot"][slot_ev] + 1, val_len
        else:
            ei_pos, ei_len = it["slot"][slot_ei], it["length"][slot_ei]
            ev_pos, ev_len = it["slot"][slot_ev], it["length"][slot_ev]
        for v in (ei_pos, ei_len, ev_pos, ev_len):
            w += bits(v, 12)
        if version >= 7:
            for s in range(1, 4):
                w += bits(it["slot"][s], 12)
            for s in range(4):
                w += bits(it["length"][s], 12)
            w += bits(perm, 8)
    for i in range(3):
        w += [pads[i][0], pads[i][1]]
    return w


def plucked_128(v):
    """push_plucked_128_legacy: the 64 two-bit chunks, least significant
    first, as 2 v - 3."""
    return [(2 * ((v >> (2 * k)) & 3) - 3) % P for k in range(64)]


def sig_witness(p, pk, pads):
    """The private inputs of the signature circuit, or a status string."""
    e_i, r_i, s_i = (int.from_bytes(p[k], "big") for k in ("issuer_sig_digest", "issuer_sig_r", "issuer_sig_s"))
    e_d, r_d, s_d = (int.from_bytes(p[k], "big") for k in ("device_sig_digest", "device_sig_r", "device_sig_s"))
    x_n, y_n = int.from_bytes(p["device_pk_x"], "big"), int.from_bytes(p["device_pk_y"], "big")
    if s_i >= Q or s_d >= Q:
        return "signature_not_canonical"
    dev = (x_n % P, y_n % P)
    w = [e_i % P, dev[0], dev[1]]
    w += ew.legacy_witness(pk, e_i, r_i, s_i)
    w += ew.legacy_witness(dev, e_d, r_d, s_d)
    for i, v in enumerate((e_i, x_n, y_n)):
        w += plucked_128(pads[i][0]) + plucked_128(pads[i][1])
        w += plucked_128(v & ((1 << 128) - 1)) + plucked_128(v >> 128)
    return w


def hash_digest(w):
    h = hashlib.sha256()
    for v in w:
        h.update(v.to_bytes(16, "little"))
    return h.hexdigest()


def sig_digest(w):
    h = hashlib.sha256()
    for v in w:
        h.update(v.to_bytes(32, "little"))
    return h.hexdigest()


def fixed_pads():
    return [[int.from_bytes(bytes(((16 * (2 * i + h) + k) * 7 + 1) % 256 for k in range(16)), "little")
             for h in range(2)] for i in range(3)]


# ---------------------------------------------------------------------------
# Upstream's test cases and witness files.
# ---------------------------------------------------------------------------

def request_of(name):
    d = mp.CASES_DIR / name
    req = dict(line.split(" ", 1) for line in (d / "request.txt").read_text().splitlines() if line)
    return (int(req["pkx"], 16), int(req["pky"], 16)), req["doc_type"].encode()


def sig_elements(path):
    b = path.read_bytes()
    return [int.from_bytes(b[32 * i:32 * i + 32], "little") for i in range(len(b) // 32)]


def check_files(archive, version, mdoc, transcript, doc_type, pk):
    """Both witnesses of the case against the archive's files."""
    hash_priv = mp.witness_elements(MDOC_DIR / f"{archive}_hash_witness.bin")[NPUB_HASH[version]:]
    sig_priv = sig_elements(MDOC_DIR / f"{archive}_sig_witness.bin")[NPUB_SIG:]
    pads = [[hash_priv[-6 + 2 * i], hash_priv[-5 + 2 * i]] for i in range(3)]
    p = mp.parse_mdoc(mdoc, transcript, doc_type, version)
    wh = hash_witness(version, mdoc, p, [CASE_ATTR], pads)
    if wh != hash_priv:
        first = next(i for i in range(min(len(wh), len(hash_priv))) if wh[i] != hash_priv[i]) \
            if len(wh) == len(hash_priv) else -1
        fail(f"{archive}: the hash witness differs from the file ({len(wh)} vs {len(hash_priv)} elements, first at {first})")
    ws = sig_witness(p, pk, pads)
    if ws != sig_priv:
        fail(f"{archive}: the signature witness differs from the file")


def attr(ident, value):
    return f"{ident.hex()}:{value.hex()}"


def choose_attributes(p, mdoc, count):
    """Up to count items that fit the request's bounds and pad into two
    blocks, preferring the identifiers upstream's tests request, with the
    item's own value."""
    prefer = [b"age_over_18", b"family_name", b"birth_date", b"height", b"issue_date"]
    items = []
    for it in p["items"]:
        ident = mdoc[it["name_start"]:it["name_start"] + it["name_len"]]
        value = mdoc[it["value_start"]:it["value_start"] + it["value_len"]]
        if it["item_len"] <= MAX_ITEM_BYTES and len(ident) <= MAX_ID_LEN and 0 < len(value) <= MAX_VALUE_LEN:
            items.append((ident, value))
    items.sort(key=lambda a: (prefer.index(a[0]) if a[0] in prefer else len(prefer), a[0]))
    return items[:count]


# ---------------------------------------------------------------------------

def main():
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE
    lines = []
    w = lines.append

    mdoc, transcript, doc_type = mp.load_case(CASE)
    case_pk, _ = request_of(CASE)
    check_files(V7, 7, mdoc, transcript, doc_type, case_pk)
    check_files(V6, 6, mdoc, transcript, doc_type, case_pk)

    w("# Known-answer vectors for Mdoc_Witness (block 6, ADR 0086), from an")
    w("#   independent Python transcription of upstream's witness builders at")
    w("#   d5e6be7, checked against the four witness files of both archives before")
    w("#   writing. Generated by gen_mdoc_witness_vectors.py; do not edit.")
    w("#")
    w("# The archives: both witnesses built from the test case under the files' pads")
    w("#   equal the files' private parts.")
    w(f"witness_file {CASE} {V7} 7 {NPUB_HASH[7]} {NPUB_SIG} {attr(*CASE_ATTR)}")
    w(f"witness_file {CASE} {V6} 6 {NPUB_HASH[6]} {NPUB_SIG} {attr(*CASE_ATTR)}")
    w("#")
    w("# The 38 test documents at both versions, under the fixed pads: one or two")
    w("#   attributes each, the full four on the archives' case, three on another;")
    w("#   a document whose MSO exceeds the version's capacity has no row there,")
    w("#   and one whose item does not hold elementValue right after")
    w("#   elementIdentifier is refused at version 6 (item_order_unsupported).")
    pads = fixed_pads()
    counts = {CASE: 4, "BIRTHDATE_1971_09_01_MDOC_3": 3}
    rows = 0
    order_rejects = 0
    for name in mp.case_names():
        mdoc, transcript, doc_type = mp.load_case(name)
        pk, _ = request_of(name)
        for version in (7, 6):
            try:
                p = mp.parse_mdoc(mdoc, transcript, doc_type, version)
            except mp.ParseError:
                continue
            attrs = choose_attributes(p, mdoc, counts.get(name, 2 if version == 7 else 1))
            if not attrs:
                fail(f"{name}: no attribute fits")
            wh = hash_witness(version, mdoc, p, attrs, pads)
            if wh == "item_order_unsupported":
                w(f"witness_reject {name} {version} {len(attrs)} {' '.join(attr(*a) for a in attrs)} {wh}")
                order_rejects += 1
                continue
            ws = sig_witness(p, pk, pads)
            if isinstance(wh, str) or isinstance(ws, str):
                fail(f"{name} v{version}: {wh if isinstance(wh, str) else ws}")
            w(f"witness {name} {version} {len(attrs)} {' '.join(attr(*a) for a in attrs)} "
              f"{hash_digest(wh)} {sig_digest(ws)}")
            rows += 1
    w("#")
    w("# The refusals on test cases: an identifier the document does not hold,")
    w("#   alone and after one it holds.")
    w(f"witness_reject {CASE} 7 1 {attr(b'nope', bytes([0xF5]))} attribute_not_found")
    w(f"witness_reject {CASE} 6 2 {attr(*CASE_ATTR)} {attr(b'age_over_99', bytes([0xF5]))} attribute_not_found")
    w("#")
    w("# Synthetic documents (the builder of gen_mdoc_parse_vectors.py, both")
    w("#   signatures set to r = 1 and s = 2): an item of 119 bytes, the largest that")
    w("#   pads into two blocks, accepted; one of 120 bytes refused; a signature")
    w("#   value s equal to the group order refused, the issuer's and the device's.")
    zero_sig = bytes([0x58, 0x40]) + bytes(64)
    one_two = bytes([0x58, 0x40]) + (1).to_bytes(32, "big") + (2).to_bytes(32, "big")
    big_s = bytes([0x58, 0x40]) + (1).to_bytes(32, "big") + Q.to_bytes(32, "big")

    def synthetic(value_len, issuer_sig=one_two, device_sig=one_two):
        doc = mp.make_doc(items=[mp.make_item(value=mp.enc_bytes(bytes(range(value_len))))])
        if doc.count(zero_sig) != 2:
            fail("synthetic: the two signatures are not where expected")
        doc = doc.replace(zero_sig, issuer_sig, 1).replace(zero_sig, device_sig, 1)
        return doc

    def item_len_of(doc):
        p = mp.parse_mdoc(doc, b"", b"x", 7)
        return p["items"][0]["item_len"]

    fits = synthetic(35)
    too_long = synthetic(36)
    if item_len_of(fits) != MAX_ITEM_BYTES or item_len_of(too_long) != MAX_ITEM_BYTES + 1:
        fail(f"synthetic: item lengths {item_len_of(fits)} and {item_len_of(too_long)}")
    syn_attr = attr(b"family_name", mp.enc_bytes(bytes(range(35))))
    p = mp.parse_mdoc(fits, b"", b"x", 7)
    w(f"witness_hex item_119 {fits.hex()} 7 1 {syn_attr} "
      f"{hash_digest(hash_witness(7, fits, p, [(b'family_name', mp.enc_bytes(bytes(range(35))))], pads))} "
      f"{sig_digest(sig_witness(p, case_pk, pads))}")
    w(f"reject_hex item_120 {too_long.hex()} 7 1 {attr(b'family_name', mp.enc_bytes(bytes(range(36))))} attribute_too_long")
    small = mp.enc_text("Mustermann")
    small_attr = attr(b"family_name", small)
    w(f"reject_hex issuer_s_is_q {synthetic_text(big_s, one_two).hex()} 7 1 {small_attr} signature_not_canonical")
    w(f"reject_hex device_s_is_q {synthetic_text(one_two, big_s).hex()} 7 1 {small_attr} signature_not_canonical")
    w("#")
    w("# The 24 orders of the four entries of an item, synthetic: at version 7 every")
    w("#   order is accepted; at version 6 the six orders where elementValue follows")
    w("#   elementIdentifier are accepted and the eighteen others refused.")
    import itertools
    names = ["digestID", "random", "elementIdentifier", "elementValue"]
    accepted6 = 0
    for order in itertools.permutations(names):
        doc = synthetic_order(list(order), one_two)
        label = "".join(n[0] if n != "elementValue" else "v" for n in order)
        for version in (7, 6):
            p = mp.parse_mdoc(doc, b"", b"x", version)
            wh = hash_witness(version, doc, p, [(b"family_name", small)], pads)
            if isinstance(wh, str):
                if version != 6 or wh != "item_order_unsupported":
                    fail(f"order {label} v{version}: {wh}")
                w(f"reject_hex order_{label} {doc.hex()} {version} 1 {small_attr} {wh}")
            else:
                if version == 6:
                    accepted6 += 1
                w(f"witness_hex order_{label} {doc.hex()} {version} 1 {small_attr} "
                  f"{hash_digest(wh)} {sig_digest(sig_witness(p, case_pk, pads))}")
    if accepted6 != 6:
        fail(f"{accepted6} orders accepted at version 6, expected 6")

    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "mdoc_witness.txt").write_text("\n".join(lines) + "\n")
    print(f"gen_mdoc_witness_vectors: {rows} witness rows, {order_rejects} documents refused at version 6"
          f" for the order of the item's entries, written to {out_dir / 'mdoc_witness.txt'}")


def synthetic_order(key_names, sig):
    """A synthetic document whose item has its four entries in the given
    order, both signatures set to sig."""
    zero_sig = bytes([0x58, 0x40]) + bytes(64)
    doc = mp.make_doc(items=[mp.make_item(key_names=key_names)])
    if doc.count(zero_sig) != 2:
        fail("synthetic: the two signatures are not where expected")
    return doc.replace(zero_sig, sig, 1).replace(zero_sig, sig, 1)


def synthetic_text(issuer_sig, device_sig):
    zero_sig = bytes([0x58, 0x40]) + bytes(64)
    doc = mp.make_doc()
    if doc.count(zero_sig) != 2:
        fail("synthetic: the two signatures are not where expected")
    return doc.replace(zero_sig, issuer_sig, 1).replace(zero_sig, device_sig, 1)


if __name__ == "__main__":
    main()
