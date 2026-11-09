#!/usr/bin/env python3
"""Known-answer vectors for Cbor_Parse, Mdoc_Parse and Sha256.Trace (Phase D,
block 6, ADR 0086): an independent Python transcription of upstream's CBOR
parser (circuits/src/cbor/parse.rs at d5e6be7), of parse_mdoc
(circuits/src/cbor/mdoc.rs) and of the SHA-256 trace
(circuits/sha256/src/concrete.rs, sha256msg/src/concrete.rs), run on
upstream's 38 test documents (upstream/mdoc/testcases/) and on synthetic
documents and CBOR items built here.

Before writing anything the script checks its own transcription against
upstream's hash witness files of both archives (upstream/mdoc/): the 768
bits of the three bound values, the eight bits of the block count and the
four 12-bit offsets at the front of the private part must equal what the
transcription reads off FAMILYNAME_MUSTERMANN_MDOC_3; it fails otherwise.

usage: gen_mdoc_parse_vectors.py [OUT_DIR]   (default: this directory)

Output: mdoc_parse.txt. Format: '#' comments and blank lines are skipped;
one case per line, fields separated by blanks:
  cbor <name> <hex> <n> <digest>            the table of a CBOR item: n
                                            elements, the SHA-256 of its rows
  cbor_reject <name> <hex> <status>         the status of a refused item
  trace <hex> <blocks> <n_blocks> <digest>  the padded message over blocks
                                            blocks and the trace of every
                                            block, digested
  parse <case> <version> ok <fields...>     upstream's test case parsed at the
                                            version: the seven values, the
                                            MSO range, the five offsets, the
                                            item count and the digest of the
                                            items' rows
  parse <case> <version> <status>           a test case refused
  item <case> <version> <i> <id> <fields...> item i of a case, in clear, with
                                            the identifier (hex) Find_Item
                                            must map to i
  parse_reject <name> <hex> <version> <status> [<cbor_status>]
                                            a synthetic document refused
  parse_hex <name> <hex> <version> <fields...>
                                            a synthetic document accepted
  find_hex <name> <hex> <id> <index>        Find_Item on a synthetic document:
                                            the first item with the
                                            identifier, 0 if none
  witness_front <case> <archive> <version> <npub>
                                            the front of the hash witness
                                            file of the archive equals the
                                            parse of the case
"""
import hashlib
import struct
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MDOC_DIR = HERE / "upstream" / "mdoc"
CASES_DIR = MDOC_DIR / "testcases"
V7 = "8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121"
V6 = "137e5a75ce72735a37c8a72da1a8a0a5df8d13365c2ae3d2c2bd6a0e7197c7c6"

MAX_BYTES = 262_144
MAX_DEPTH = 16
MAX_ELEMENTS = 4_096
MAX_ITEMS = 256

KINDS = ["unsigned_int", "negative_int", "byte_string", "text_string",
         "array_kind", "map_kind", "tag", "simple", "float_16", "float_32",
         "float_64"]


def fail(msg):
    print("gen_mdoc_parse_vectors: " + msg, file=sys.stderr)
    sys.exit(1)


# ---------------------------------------------------------------------------
# The CBOR parser, as Cbor_Parse: a table of elements with positions relative
# to the parsed bytes, the statuses of upstream's parse_exact and the bounds.
# ---------------------------------------------------------------------------

class CborError(Exception):
    def __init__(self, status):
        super().__init__(status)
        self.status = status


def is_utf8(b):
    try:
        b.decode("utf-8")
        return True
    except UnicodeDecodeError:
        return False


def parse_exact(data):
    """The table (a list of dicts, index 1 first) or a CborError."""
    n = len(data)
    if n > MAX_BYTES:
        raise CborError("length_too_large")
    elems = []   # dicts with kind,start,content,stop,value,count,parent,child,next
    stack = []   # [container index, remaining, last child]
    off = 0
    while True:
        if len(elems) == MAX_ELEMENTS:
            raise CborError("too_many_elements")
        if off >= n:
            raise CborError("truncated")
        b = data[off]
        major, info = b >> 5, b & 0x1F
        if info < 24:
            arg, extra = info, 0
        elif info == 24:
            extra = 1
        elif info == 25:
            extra = 2
        elif info == 26:
            extra = 4
        elif info == 27:
            extra = 8
        else:
            raise CborError("reserved_info")
        if n - off < 1 + extra:
            raise CborError("truncated")
        if extra:
            arg = int.from_bytes(data[off + 1:off + 1 + extra], "big")
        hl = 1 + extra
        parent = stack[-1][0] if stack else 0
        idx = len(elems) + 1
        e = dict(kind=None, start=off, content=off + hl, stop=off + hl,
                 value=arg, count=0, parent=parent, child=0, next=0)
        items = 0
        if major == 0:
            e["kind"] = "unsigned_int"
        elif major == 1:
            e["kind"] = "negative_int"
        elif major in (2, 3):
            if arg > n - e["content"]:
                raise CborError("length_too_large" if arg > MAX_BYTES else "truncated")
            e["stop"] = e["content"] + arg
            if major == 2:
                e["kind"] = "byte_string"
            else:
                e["kind"] = "text_string"
                if arg > 0 and not is_utf8(data[e["content"]:e["stop"]]):
                    raise CborError("not_utf8")
        elif major == 4:
            if arg > MAX_ELEMENTS:
                raise CborError("too_many_elements")
            e["kind"] = "array_kind"
            items = arg
        elif major == 5:
            if arg > MAX_ELEMENTS // 2:
                raise CborError("too_many_elements")
            e["kind"] = "map_kind"
            items = 2 * arg
        elif major == 6:
            e["kind"] = "tag"
            items = 1
        else:
            e["kind"] = {25: "float_16", 26: "float_32", 27: "float_64"}.get(info, "simple")
        e["count"] = items
        elems.append(e)
        if stack:
            if stack[-1][2] == 0:
                elems[stack[-1][0] - 1]["child"] = idx
            else:
                elems[stack[-1][2] - 1]["next"] = idx
            stack[-1][2] = idx
        if items > 0:
            if len(stack) == MAX_DEPTH:
                raise CborError("too_deep")
            off = e["content"]
            e["stop"] = n
            stack.append([idx, items, 0])
        else:
            off = e["stop"]
            while stack:
                stack[-1][1] -= 1
                if stack[-1][1] > 0:
                    break
                elems[stack[-1][0] - 1]["stop"] = off
                stack.pop()
            if not stack:
                break
    if off != n:
        raise CborError("trailing_bytes")
    return elems


def table_digest(elems):
    rows = "".join("{kind} {start} {content} {stop} {value} {count} {parent} {child} {next}\n".format(**e)
                   for e in elems)
    return hashlib.sha256(rows.encode()).hexdigest()


# Accessors over the table, as Cbor_Parse's.

def el(elems, i):
    return elems[i - 1]


def array_item(elems, a, i):
    if el(elems, a)["kind"] != "array_kind":
        return 0
    c = el(elems, a)["child"]
    for _ in range(i):
        if c == 0:
            break
        c = el(elems, c)["next"]
    return c


def text_bytes(elems, data, e):
    x = el(elems, e)
    return data[x["content"]:x["stop"]]


def map_entry(elems, data, m, key_bytes=None, int_key=None):
    """(key_el, val_el, lookup) as Map_Text_Entry / Map_Int_Entry."""
    x = el(elems, m)
    if x["kind"] != "map_kind":
        return 0, 0, "not_a_map"
    found = None
    k = x["child"]
    while k:
        v = el(elems, k)["next"]
        if v == 0:
            break
        ke = el(elems, k)
        match = False
        if key_bytes is not None:
            match = ke["kind"] == "text_string" and data[ke["content"]:ke["stop"]] == key_bytes
        else:
            neg, mag = int_key
            match = ke["kind"] == ("negative_int" if neg else "unsigned_int") and ke["value"] == mag
        if match:
            if found is not None:
                return 0, 0, "duplicate"
            found = (k, v)
        k = el(elems, v)["next"]
    if found is None:
        return 0, 0, "missing"
    return found[0], found[1], "found"


def tag_child(elems, e, n):
    x = el(elems, e)
    return x["child"] if x["kind"] == "tag" and x["value"] == n else 0


# ---------------------------------------------------------------------------
# SHA-256 with its trace (FIPS 180-4; upstream's sha256/concrete.rs).
# ---------------------------------------------------------------------------

K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]
H0 = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]
M32 = 0xFFFFFFFF


def rotr(x, n):
    return ((x >> n) | (x << (32 - n))) & M32


def compress_traced(h, block):
    w = list(struct.unpack(">16I", block)) + [0] * 48
    for i in range(16, 64):
        s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3)
        s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10)
        w[i] = (w[i - 16] + s0 + w[i - 7] + s1) & M32
    a, b, c, d, e, f, g, hh = h
    oute, outa = [], []
    for i in range(64):
        t1 = (hh + (rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25)) + ((e & f) ^ (~e & g)) + K[i] + w[i]) & M32
        t2 = ((rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22)) + ((a & b) ^ (a & c) ^ (b & c))) & M32
        hh, g, f, e, d, c, b, a = g, f, e, (d + t1) & M32, c, b, a, (t1 + t2) & M32
        oute.append(e)
        outa.append(a)
    h1 = [(x + y) & M32 for x, y in zip(h, [a, b, c, d, e, f, g, hh])]
    return w[16:], oute, outa, h1


def pad_message(msg, blocks):
    """(n_blocks, padded of blocks*64 bytes); None if it does not fit."""
    if len(msg) + 9 > 64 * blocks:
        return None
    n_blocks = (len(msg) + 9 + 63) // 64
    padded = bytearray(msg) + b"\x80"
    padded += b"\x00" * (64 * n_blocks - 8 - len(padded))
    padded += (8 * len(msg)).to_bytes(8, "big")
    padded += b"\x00" * (64 * blocks - len(padded))
    return n_blocks, bytes(padded)


def trace_digest(padded, blocks):
    h = list(H0)
    d = hashlib.sha256()
    d.update(padded)
    for i in range(blocks):
        w, e, a, h1 = compress_traced(h, padded[64 * i:64 * i + 64])
        for word in w + e + a + h1:
            d.update(word.to_bytes(4, "big"))
        h = h1
    return d.hexdigest()


# ---------------------------------------------------------------------------
# parse_mdoc, as Mdoc_Parse (upstream's order of checks and statuses).
# ---------------------------------------------------------------------------

class ParseError(Exception):
    def __init__(self, status, detail="ok"):
        super().__init__(status)
        self.status = status
        self.detail = detail


SIGNING_HEADER = bytes([0x84, 0x6A]) + b"Signature1" + bytes([0x43, 0xA1, 0x01, 0x26, 0x40])
DEVICE_AUTH_HEADER = bytes([0x84, 0x74]) + b"DeviceAuthentication"


def cbor_head(major, n):
    if n < 24:
        return bytes([(major << 5) | n])
    if n < 256:
        return bytes([(major << 5) | 24, n])
    if n < 65536:
        return bytes([(major << 5) | 25]) + n.to_bytes(2, "big")
    return bytes([(major << 5) | 26]) + n.to_bytes(4, "big")


def device_auth_digest(transcript, doc_type):
    da = DEVICE_AUTH_HEADER + transcript + cbor_head(3, len(doc_type)) + doc_type + bytes([0xD8, 0x18, 0x41, 0xA0])
    payload = bytes([0xD8, 0x18]) + cbor_head(2, len(da)) + da
    return hashlib.sha256(SIGNING_HEADER + cbor_head(2, len(payload)) + payload).digest()


def max_blocks(version):
    return 35 if version == 6 else 40


def need_value(elems, data, m, key):
    if m == 0:
        raise ParseError("unexpected_type")
    k, v, r = map_entry(elems, data, m, key_bytes=key.encode())
    if r == "found":
        return v
    raise ParseError({"missing": "missing_field", "duplicate": "duplicate_field",
                      "not_a_map": "unexpected_type"}[r])


def need_key(elems, data, m, key):
    if m == 0:
        raise ParseError("unexpected_type")
    k, v, r = map_entry(elems, data, m, key_bytes=key.encode())
    if r == "found":
        return el(elems, k)["start"], v
    raise ParseError({"missing": "missing_field", "duplicate": "duplicate_field",
                      "not_a_map": "unexpected_type"}[r])


def cose_array(elems, e):
    if e == 0:
        raise ParseError("unexpected_type")
    if el(elems, e)["kind"] == "array_kind":
        return e
    a = tag_child(elems, e, 18)
    if a == 0 or el(elems, a)["kind"] != "array_kind":
        raise ParseError("unexpected_type")
    return a


def need_bytes_item(elems, arr, i):
    if arr == 0:
        raise ParseError("unexpected_type")
    bs = array_item(elems, arr, i)
    if bs == 0:
        raise ParseError("missing_field")
    if el(elems, bs)["kind"] != "byte_string":
        raise ParseError("unexpected_type")
    return bs


def signature(elems, data, bs):
    x = el(elems, bs)
    if x["stop"] - x["content"] != 64:
        raise ParseError("invalid_length")
    b = data[x["content"]:x["stop"]]
    return b[:32], b[32:]


def coordinate(elems, data, m, mag):
    """required_device_coordinate: at each matching key, a second match is
    DuplicateField and a value that is not a byte string UnexpectedType, in
    the order of the pairs."""
    if m == 0 or el(elems, m)["kind"] != "map_kind":
        raise ParseError("unexpected_type")
    found = None
    k = el(elems, m)["child"]
    while k:
        v = el(elems, k)["next"]
        if v == 0:
            break
        ke = el(elems, k)
        if ke["kind"] == "negative_int" and ke["value"] == mag:
            if found is not None:
                raise ParseError("duplicate_field")
            x = el(elems, v)
            if x["kind"] != "byte_string":
                raise ParseError("unexpected_type")
            b = data[x["content"]:x["stop"]]
            # Nat::from_bytes_be: reversed and resized to 32 bytes
            found = b[-32:].rjust(32, b"\x00")
        k = el(elems, v)["next"]
    if found is None:
        raise ParseError("missing_field")
    return found


def validate_mso_layout(wrapped, map_len, version):
    if 18 + 2 + len(wrapped) > 64 * max_blocks(version) - 9 or len(wrapped) > 65535:
        raise ParseError("too_big")
    if map_len < 256 or wrapped[:3] != bytes([0xD8, 0x18, 0x59]) or len(wrapped) != map_len + 5:
        raise ParseError("unsupported_encoding")
    if int.from_bytes(wrapped[3:5], "big") != map_len:
        raise ParseError("unsupported_encoding")


def one_item(mdoc, root, item_el, ns_el, mso, mso_map, vd):
    bs = tag_child(root, item_el, 24)
    if bs == 0 or el(root, bs)["kind"] != "byte_string":
        raise ParseError("unexpected_type")
    it = {}
    it["item_start"] = el(root, item_el)["start"]
    it["item_len"] = el(root, item_el)["stop"] - el(root, item_el)["start"]
    inner_first = el(root, bs)["content"]
    inner = mdoc[inner_first:el(root, bs)["stop"]]
    try:
        tab = parse_exact(inner)
    except CborError as e:
        raise ParseError("cbor_item", e.status)
    id_el = need_value(tab, inner, 1, "elementIdentifier")
    if el(tab, id_el)["kind"] != "text_string":
        raise ParseError("unexpected_type")
    it["name_start"] = inner_first + el(tab, id_el)["content"]
    it["name_len"] = el(tab, id_el)["stop"] - el(tab, id_el)["content"]
    val_el = need_value(tab, inner, 1, "elementValue")
    it["value_start"] = inner_first + el(tab, val_el)["start"]
    it["value_len"] = el(tab, val_el)["stop"] - el(tab, val_el)["start"]
    if el(tab, 1)["kind"] != "map_kind":
        raise ParseError("unexpected_type")
    if el(tab, 1)["count"] != 8:
        raise ParseError("invalid_length")
    slot_of = [4, 4, 4, 4]
    length = [0, 0, 0, 0]
    digest_id = None
    k = el(tab, 1)["child"]
    pair = 0
    first_key_start = 0
    while k and pair < 4:
        v = el(tab, k)["next"]
        if v == 0:
            break
        ke = el(tab, k)
        if ke["kind"] != "text_string":
            raise ParseError("unexpected_type")
        length[pair] = el(tab, v)["stop"] - ke["start"]
        key = inner[ke["content"]:ke["stop"]]
        names = [b"digestID", b"random", b"elementIdentifier", b"elementValue"]
        if key in names:
            s = names.index(key)
            if slot_of[s] != 4:
                raise ParseError("duplicate_field")
            slot_of[s] = pair
            if s == 0:
                ve = el(tab, v)
                if ve["kind"] == "unsigned_int":
                    digest_id = ve["value"]
                elif ve["kind"] == "negative_int":
                    raise ParseError("invalid_value")
                else:
                    raise ParseError("unexpected_type")
        else:
            raise ParseError("unknown_field")
        if pair == 0:
            first_key_start = ke["start"]
        pair += 1
        k = el(tab, v)["next"]
    if 4 in slot_of or digest_id is None:
        raise ParseError("missing_field")
    it["permutation"] = (slot_of[3] << 6) | (slot_of[2] << 4) | (slot_of[1] << 2) | slot_of[0]
    prefix = it["item_len"] - len(inner)
    slots = [prefix + first_key_start]
    for i in range(1, 4):
        slots.append(slots[i - 1] + length[i - 1])
    it["slot"] = slots
    it["length"] = length
    it["digest_id"] = digest_id
    ns_name = text_bytes(root, mdoc, ns_el)
    k2, ns_map, r = map_entry(mso, mso_map, vd, key_bytes=ns_name)
    if r != "found":
        raise ParseError({"missing": "missing_field", "duplicate": "duplicate_field",
                          "not_a_map": "unexpected_type"}[r])
    k3, dv, r = map_entry(mso, mso_map, ns_map, int_key=(False, digest_id))
    if r != "found":
        raise ParseError({"missing": "missing_field", "duplicate": "duplicate_field",
                          "not_a_map": "unexpected_type"}[r])
    it["digest_offset"] = el(mso, dv)["start"]
    return it


def parse_mdoc(mdoc, transcript, doc_type, version):
    try:
        root = parse_exact(mdoc)
    except CborError as e:
        raise ParseError("cbor_root", e.status)
    p = {}
    docs = need_value(root, mdoc, 1, "documents")
    if el(root, docs)["kind"] != "array_kind":
        raise ParseError("unexpected_type")
    doc0 = array_item(root, docs, 0)
    if doc0 == 0:
        raise ParseError("missing_field")
    issuer_signed = need_value(root, mdoc, doc0, "issuerSigned")
    issuer_auth = need_value(root, mdoc, issuer_signed, "issuerAuth")
    auth_arr = cose_array(root, issuer_auth)
    mso_bs = need_bytes_item(root, auth_arr, 2)
    mso_start = el(root, mso_bs)["content"]
    mso_len = el(root, mso_bs)["stop"] - mso_start
    wrapped = mdoc[mso_start:mso_start + mso_len]
    try:
        wrap = parse_exact(wrapped)
    except CborError as e:
        raise ParseError("cbor_mso_wrapper", e.status)
    tc = tag_child(wrap, 1, 24)
    if tc == 0:
        raise ParseError("invalid_value")
    if el(wrap, tc)["kind"] != "byte_string":
        raise ParseError("unexpected_type")
    map_len = el(wrap, tc)["stop"] - el(wrap, tc)["content"]
    validate_mso_layout(wrapped, map_len, version)
    p["mso_start"], p["mso_len"] = mso_start, mso_len
    message = SIGNING_HEADER + bytes([0x59]) + mso_len.to_bytes(2, "big") + wrapped
    p["issuer_sig_digest"] = hashlib.sha256(message).digest()
    p["message_len"] = len(message)
    mso_map = mdoc[mso_start + 5:mso_start + mso_len]
    try:
        mso = parse_exact(mso_map)
    except CborError as e:
        raise ParseError("cbor_mso_map", e.status)
    dki = need_value(mso, mso_map, 1, "deviceKeyInfo")
    dk = need_value(mso, mso_map, dki, "deviceKey")
    p["device_pk_x"] = coordinate(mso, mso_map, dk, 1)
    p["device_pk_y"] = coordinate(mso, mso_map, dk, 2)
    sig_bs = need_bytes_item(root, auth_arr, 3)
    p["issuer_sig_r"], p["issuer_sig_s"] = signature(root, mdoc, sig_bs)
    device_signed = need_value(root, mdoc, doc0, "deviceSigned")
    device_auth = need_value(root, mdoc, device_signed, "deviceAuth")
    device_sig = need_value(root, mdoc, device_auth, "deviceSignature")
    dev_arr = cose_array(root, device_sig)
    sig_bs = need_bytes_item(root, dev_arr, 3)
    p["device_sig_r"], p["device_sig_s"] = signature(root, mdoc, sig_bs)
    p["device_sig_digest"] = device_auth_digest(transcript, doc_type)
    p["doc_type_offset"], _ = need_key(mso, mso_map, 1, "docType")
    validity = need_value(mso, mso_map, 1, "validityInfo")
    p["valid_from_offset"], _ = need_key(mso, mso_map, validity, "validFrom")
    p["valid_until_offset"], _ = need_key(mso, mso_map, validity, "validUntil")
    p["device_key_info_offset"], _ = need_key(mso, mso_map, 1, "deviceKeyInfo")
    p["value_digests_offset"], vd = need_key(mso, mso_map, 1, "valueDigests")
    namespaces = need_value(root, mdoc, issuer_signed, "nameSpaces")
    if el(root, namespaces)["kind"] != "map_kind":
        raise ParseError("unexpected_type")
    items = []
    seen = []
    k = el(root, namespaces)["child"]
    while k:
        v = el(root, k)["next"]
        if v == 0:
            break
        if el(root, k)["kind"] != "text_string":
            raise ParseError("unexpected_type")
        name = text_bytes(root, mdoc, k)
        if name in seen:
            raise ParseError("duplicate_field")
        seen.append(name)
        if el(root, v)["kind"] != "array_kind":
            raise ParseError("unexpected_type")
        item_el = el(root, v)["child"]
        while item_el:
            if len(items) == MAX_ITEMS:
                raise ParseError("too_many_items")
            items.append(one_item(mdoc, root, item_el, k, mso, mso_map, vd))
            item_el = el(root, item_el)["next"]
        k = el(root, v)["next"]
    p["items"] = items
    return p


def item_row(it):
    return "{name_start} {name_len} {value_start} {value_len} {item_start} {item_len} {s0} {s1} {s2} {s3} {l0} {l1} {l2} {l3} {permutation} {digest_offset} {digest_id}".format(
        s0=it["slot"][0], s1=it["slot"][1], s2=it["slot"][2], s3=it["slot"][3],
        l0=it["length"][0], l1=it["length"][1], l2=it["length"][2], l3=it["length"][3], **it)


def items_digest(items):
    return hashlib.sha256("".join(item_row(it) + "\n" for it in items).encode()).hexdigest()


def parse_fields(p):
    hx = lambda b: b.hex()
    return " ".join([
        hx(p["issuer_sig_digest"]), hx(p["device_pk_x"]), hx(p["device_pk_y"]),
        hx(p["issuer_sig_r"]), hx(p["issuer_sig_s"]), hx(p["device_sig_digest"]),
        hx(p["device_sig_r"]), hx(p["device_sig_s"]),
        str(p["mso_start"]), str(p["mso_len"]),
        str(p["doc_type_offset"]), str(p["valid_from_offset"]), str(p["valid_until_offset"]),
        str(p["device_key_info_offset"]), str(p["value_digests_offset"]),
        str(len(p["items"])), items_digest(p["items"])])


# ---------------------------------------------------------------------------
# Upstream's test cases and witness files.
# ---------------------------------------------------------------------------

def load_case(name):
    d = CASES_DIR / name
    req = dict(line.split(" ", 1) for line in (d / "request.txt").read_text().splitlines() if line)
    return (d / "mdoc.bin").read_bytes(), (d / "transcript.bin").read_bytes(), req["doc_type"].encode()


def case_names():
    return sorted(p.name for p in CASES_DIR.iterdir() if p.is_dir() and (p / "mdoc.bin").exists())


def witness_elements(path):
    b = path.read_bytes()
    return [int.from_bytes(b[16 * i:16 * i + 16], "little") for i in range(len(b) // 16)]


def check_witness_front(archive, version, npub, p):
    """The front of the private part of the hash witness against the parse."""
    elems = witness_elements(MDOC_DIR / f"{archive}_hash_witness.bin")
    priv = elems[npub:]
    bits = []
    for v in (p["issuer_sig_digest"], p["device_pk_x"], p["device_pk_y"]):
        n = int.from_bytes(v, "big")
        bits += [(n >> k) & 1 for k in range(256)]
    if priv[:768] != bits:
        fail(f"{archive}: the 768 bits of the bound values differ from the parse")
    nblocks = (p["message_len"] + 9 + 63) // 64
    if priv[768:776] != [(nblocks >> k) & 1 for k in range(8)]:
        fail(f"{archive}: nblocks differs: file {priv[768:776]}, parse {nblocks}")
    mb = max_blocks(version)
    off_pos = 768 + 8 + (mb * 64 - 18) * 8 + mb * 1472
    offs = priv[off_pos:off_pos + 48]
    want = []
    for v in (p["valid_from_offset"], p["valid_until_offset"], p["device_key_info_offset"], p["value_digests_offset"]):
        want += [(v >> k) & 1 for k in range(12)]
    if offs != want:
        fail(f"{archive}: the four offsets differ from the parse")


# ---------------------------------------------------------------------------
# Synthetic documents: a CBOR encoder and a builder with knobs.
# ---------------------------------------------------------------------------

def enc_uint(n):
    return cbor_head(0, n)


def enc_nint(n):
    """n negative: -1 - n encoded."""
    return cbor_head(1, -1 - n)


def enc_bytes(b):
    return cbor_head(2, len(b)) + b


def enc_text(s):
    b = s.encode() if isinstance(s, str) else s
    return cbor_head(3, len(b)) + b


def enc_array(items):
    return cbor_head(4, len(items)) + b"".join(items)


def enc_map(pairs):
    return cbor_head(5, len(pairs)) + b"".join(k + v for k, v in pairs)


def enc_tag(n, inner):
    return cbor_head(6, n) + inner


def tag24(b):
    return enc_tag(24, enc_bytes(b))


def make_item(entries=None, digest_id=7, key_names=None, value=None):
    """An IssuerSignedItem map: entries in order; defaults to the four."""
    value = value if value is not None else enc_text("Mustermann")
    if entries is None:
        names = key_names or ["digestID", "random", "elementIdentifier", "elementValue"]
        value_of = {"digestID": enc_uint(digest_id) if digest_id >= 0 else enc_nint(digest_id),
                    "random": enc_bytes(bytes(range(16))),
                    "elementIdentifier": enc_text("family_name"),
                    "elementValue": value}
        entries = [(n, value_of[n]) for n in names]
    return enc_map([(enc_text(k), v) for k, v in entries])


def make_mso_map(map_len=300, ns="org.iso.18013.5.1", digest_id=7, pad_key="pad", doc_type="org.iso.18013.5.1.mDL"):
    base = [
        (enc_text("docType"), enc_text(doc_type)),
        (enc_text("validityInfo"), enc_map([(enc_text("validFrom"), enc_text("2024-01-01T00:00:00Z")),
                                             (enc_text("validUntil"), enc_text("2034-01-01T00:00:00Z"))])),
        (enc_text("deviceKeyInfo"), enc_map([(enc_text("deviceKey"),
                                               enc_map([(enc_nint(-2), enc_bytes(bytes([1] * 32))),
                                                        (enc_nint(-3), enc_bytes(bytes([2] * 32)))]))])),
        (enc_text("valueDigests"), enc_map([(enc_text(ns), enc_map([(enc_uint(digest_id), enc_bytes(bytes(32)))]))])),
    ]
    # pad to the wanted length with a byte string under pad_key (its head
    # grows at 24 and 256 bytes, so a one-byte entry "q" fills the gaps)
    for extra in ([], [(enc_text("q"), enc_uint(0))]):
        for fill in range(0, map_len + 8):
            cand = enc_map(base + extra + [(enc_text(pad_key), enc_bytes(bytes(fill)))])
            if len(cand) == map_len:
                return cand
            if len(cand) > map_len:
                break
    fail(f"make_mso_map: no map of {map_len} bytes")


def make_doc(mso_map=None, wrapped=None, items=None, ns="org.iso.18013.5.1", sig_len=64,
             dev_sig_len=64, tag18=False, extra_root=None, dup_documents=False, no_device=False,
             dup_namespace=False):
    mso_map = mso_map if mso_map is not None else make_mso_map()
    if wrapped is None:
        wrapped = bytes([0xD8, 0x18, 0x59]) + len(mso_map).to_bytes(2, "big") + mso_map
    items = items if items is not None else [make_item()]
    cose = enc_array([enc_bytes(bytes([0xA1, 0x01, 0x26])), enc_map([]), enc_bytes(wrapped), enc_bytes(bytes(sig_len))])
    if tag18:
        cose = enc_tag(18, cose)
    ns_pairs = [(enc_text(ns), enc_array([tag24(i) for i in items]))]
    if dup_namespace:
        ns_pairs.append((enc_text(ns), enc_array([])))
    issuer_signed = enc_map([(enc_text("nameSpaces"), enc_map(ns_pairs)), (enc_text("issuerAuth"), cose)])
    dev_cose = enc_array([enc_bytes(bytes([0xA1, 0x01, 0x26])), enc_map([]), enc_bytes(b""), enc_bytes(bytes(dev_sig_len))])
    doc_pairs = [(enc_text("issuerSigned"), issuer_signed)]
    if not no_device:
        doc_pairs.append((enc_text("deviceSigned"), enc_map([(enc_text("deviceAuth"),
                                                               enc_map([(enc_text("deviceSignature"), dev_cose)]))])))
    doc0 = enc_map(doc_pairs)
    root_pairs = [(enc_text("documents"), enc_array([doc0]))]
    if dup_documents:
        root_pairs.append((enc_text("documents"), enc_array([])))
    if extra_root:
        root_pairs += extra_root
    return enc_map(root_pairs)


# ---------------------------------------------------------------------------

def main():
    out_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else HERE
    lines = []
    w = lines.append
    w("# Known-answer vectors for Cbor_Parse, Mdoc_Parse and Sha256.Trace (block 6b,")
    w("#   ADR 0086), from an independent Python transcription of upstream's parser,")
    w("#   parse_mdoc and SHA-256 trace at d5e6be7, checked against the hash witness")
    w("#   files of both archives before writing. Generated by")
    w("#   gen_mdoc_parse_vectors.py; do not edit.")
    w("#")

    # --- CBOR items: positives (table digests) and negatives (statuses)
    w("# CBOR items: the table of elements, digested; and the refusals.")
    cbor_ok = [
        ("uint0", bytes([0x00])),
        ("uint24", bytes([0x18, 0x18])),
        ("uint64max", bytes([0x1B]) + b"\xff" * 8),
        ("nint1", bytes([0x20])),
        ("nint_big", bytes([0x3B]) + b"\xff" * 8),
        ("bytes_empty", bytes([0x40])),
        ("text", enc_text("Mustermann")),
        ("text_utf8", enc_text("Müller€")),
        ("array_empty", bytes([0x80])),
        ("array", enc_array([enc_uint(1), enc_text("a"), enc_bytes(b"\x01\x02")])),
        ("map", enc_map([(enc_text("a"), enc_uint(1)), (enc_nint(-2), enc_bytes(b"x"))])),
        ("map_empty", bytes([0xA0])),
        ("tag24", tag24(enc_uint(5))),
        ("nested", enc_array([enc_array([enc_array([enc_uint(1)])]), enc_map([(enc_uint(1), enc_array([]))])])),
        ("simple", bytes([0xF5])),
        ("simple24", bytes([0xF8, 0x20])),
        ("float16", bytes([0xF9, 0x3C, 0x00])),
        ("float32", bytes([0xFA, 0x3F, 0x80, 0x00, 0x00])),
        ("float64", bytes([0xFB, 0x3F, 0xF0, 0, 0, 0, 0, 0, 0])),
        ("depth16", bytes([0x81]) * 16 + bytes([0x00])),
        ("array4095", bytes([0x99, 0x0F, 0xFF]) + bytes(4095)),
        ("len2", bytes([0x59, 0x01, 0x00]) + bytes(256)),
        ("len4", bytes([0x5A, 0x00, 0x01, 0x00, 0x00]) + bytes(65536)),
    ]
    for name, data in cbor_ok:
        tab = parse_exact(data)
        w(f"cbor {name} {data.hex()} {len(tab)} {table_digest(tab)}")
    cbor_bad = [
        ("empty", b"", "truncated"),
        ("head_cut", bytes([0x19, 0x01]), "truncated"),
        ("string_cut", bytes([0x43, 0x01]), "truncated"),
        ("array_cut", bytes([0x82, 0x01]), "truncated"),
        ("indefinite_bytes", bytes([0x5F, 0x41, 0x00, 0xFF]), "reserved_info"),
        ("indefinite_array", bytes([0x9F, 0xFF]), "reserved_info"),
        ("info28", bytes([0x1C]), "reserved_info"),
        ("simple_info28", bytes([0xFC]), "reserved_info"),
        ("length_huge", bytes([0x5B, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x01]), "length_too_large"),
        ("bad_utf8", bytes([0x62, 0xC3, 0x28]), "not_utf8"),
        ("overlong", bytes([0x62, 0xC0, 0x80]), "not_utf8"),
        ("surrogate", bytes([0x63, 0xED, 0xA0, 0x80]), "not_utf8"),
        ("trailing", bytes([0x01, 0xFF]), "trailing_bytes"),
        ("trailing_map", bytes([0xA0, 0x00]), "trailing_bytes"),
        ("depth17", bytes([0x81]) * 17 + bytes([0x00]), "too_deep"),
        ("array4097", bytes([0x99, 0x10, 0x01]) + bytes(4097), "too_many_elements"),
        ("map2049", bytes([0xB9, 0x08, 0x01]), "too_many_elements"),
        ("elements4097", bytes([0x99, 0x10, 0x00]) + bytes(4096), "too_many_elements"),
    ]
    for name, data, status in cbor_bad:
        try:
            parse_exact(data)
            fail(f"cbor {name}: accepted, expected {status}")
        except CborError as e:
            if e.status != status:
                fail(f"cbor {name}: got {e.status}, expected {status}")
        w(f"cbor_reject {name} {data.hex() if data else '-'} {status}")
    w("#")

    # --- SHA-256 traces
    w("# SHA-256 with its trace over a fixed number of blocks (the zero blocks")
    w("#   compressed too); the digest covers the padded bytes and every block's")
    w("#   w[16..63], e[0..63], a[0..63], h1[0..7] as big-endian words.")
    for msg, blocks in [(b"", 1), (b"abc", 1), (b"abc", 2), (bytes(55), 1), (bytes(56), 2),
                        (bytes(range(200)), 4), (bytes(range(256)) * 9, 40), (bytes(119), 2)]:
        n_blocks, padded = pad_message(msg, blocks)
        w(f"trace {msg.hex() if msg else '-'} {blocks} {n_blocks} {trace_digest(padded, blocks)}")
    w("#")

    # --- the 38 cases
    w("# Upstream's 38 test documents, parsed at version 7 (and the Mustermann")
    w("#   document at version 6 as well): the seven values, the MSO range, the")
    w("#   five offsets, the item count, the digest of the items' rows.")
    parsed = {}
    for name in case_names():
        mdoc, tr, dt = load_case(name)
        for version in ([7, 6] if name == "FAMILYNAME_MUSTERMANN_MDOC_3" else [7]):
            try:
                p = parse_mdoc(mdoc, tr, dt, version)
                parsed[(name, version)] = p
                w(f"parse {name} {version} ok {parse_fields(p)}")
            except ParseError as e:
                w(f"parse {name} {version} {e.status}")
    w("#")
    w("# The items of the Mustermann document, in clear: name_start name_len")
    w("#   value_start value_len item_start item_len slot0..3 length0..3")
    w("#   permutation digest_offset digest_id.")
    p = parsed[("FAMILYNAME_MUSTERMANN_MDOC_3", 7)]
    mdoc_m, _, _ = load_case("FAMILYNAME_MUSTERMANN_MDOC_3")
    for i, it in enumerate(p["items"], 1):
        ident = mdoc_m[it["name_start"]:it["name_start"] + it["name_len"]]
        w(f"item FAMILYNAME_MUSTERMANN_MDOC_3 7 {i} {ident.hex()} {item_row(it)}")
    w("#")
    # the self-check against the witness files, then the lines
    check_witness_front(V7, 7, 952, parsed[("FAMILYNAME_MUSTERMANN_MDOC_3", 7)])
    check_witness_front(V6, 6, 944, parsed[("FAMILYNAME_MUSTERMANN_MDOC_3", 6)])
    w("# The front of the private part of upstream's hash witness files: the 768")
    w("#   bits of the bound values, the 8 bits of the block count, the four 12-bit")
    w("#   offsets, equal to the parse of the Mustermann document.")
    w(f"witness_front FAMILYNAME_MUSTERMANN_MDOC_3 {V7} 7 952")
    w(f"witness_front FAMILYNAME_MUSTERMANN_MDOC_3 {V6} 6 944")
    w("#")

    # --- synthetic documents
    w("# Synthetic documents: accepted (parse_hex) and refused (parse_reject),")
    w("#   with the transcript empty and the document type \"x\".")
    good = [
        ("minimal", make_doc()),
        ("tag18_cose", make_doc(tag18=True)),
        ("two_items", make_doc(items=[make_item(digest_id=7), make_item(digest_id=7, key_names=["elementValue", "digestID", "random", "elementIdentifier"])])),
        ("permuted_item", make_doc(items=[make_item(key_names=["random", "elementIdentifier", "elementValue", "digestID"])])),
        ("item_256_bytes", make_doc(items=[make_item(value=enc_bytes(bytes(200)))])),
        ("items_256", make_doc(items=[make_item()] * 256)),
        ("mso_2300_v7", make_doc(mso_map=make_mso_map(map_len=2300))),
        ("coordinate_31", make_doc(mso_map=None)),
    ]
    # the 31-byte coordinate: rebuild the MSO map by hand
    short_coord_map = make_mso_map()
    good = [g for g in good if g[0] != "coordinate_31"]
    for name, doc in good:
        p = parse_mdoc(doc, b"", b"x", 7)
        w(f"parse_hex {name} {doc.hex()} 7 {parse_fields(p)}")
    # Find_Item: the first item with the identifier, or 0
    two = dict(good)["two_items"]
    w(f"find_hex two_items_first {two.hex()} {b'family_name'.hex()} 1")
    w(f"find_hex two_items_missing {two.hex()} {b'given_name'.hex()} 0")
    w(f"find_hex two_items_prefix {two.hex()} {b'family_nam'.hex()} 0")
    bad = [
        ("truncated_root", make_doc()[:-3], 7, "cbor_root", "truncated"),
        ("trailing_root", make_doc() + b"\x00", 7, "cbor_root", "trailing_bytes"),
        ("indefinite_root", bytes([0xBF, 0xFF]), 7, "cbor_root", "reserved_info"),
        ("root_not_map", bytes([0x80]), 7, "unexpected_type", None),
        ("no_documents", enc_map([(enc_text("x"), enc_uint(1))]), 7, "missing_field", None),
        ("dup_documents", make_doc(dup_documents=True), 7, "duplicate_field", None),
        ("documents_not_array", enc_map([(enc_text("documents"), enc_uint(0))]), 7, "unexpected_type", None),
        ("documents_empty", enc_map([(enc_text("documents"), enc_array([]))]), 7, "missing_field", None),
        ("no_device_signed", make_doc(no_device=True), 7, "missing_field", None),
        ("issuer_sig_63", make_doc(sig_len=63), 7, "invalid_length", None),
        ("device_sig_63", make_doc(dev_sig_len=63), 7, "invalid_length", None),
        ("mso_map_255", make_doc(mso_map=make_mso_map(map_len=255, doc_type="x", pad_key="p")), 7, "unsupported_encoding", None),
        ("mso_2300_v6", make_doc(mso_map=make_mso_map(map_len=2300)), 6, "too_big", None),
        ("mso_too_big_v7", make_doc(mso_map=make_mso_map(map_len=2527)), 7, "too_big", None),
        ("mso_not_tag24", make_doc(wrapped=tag24(bytes(300))[0:0] + enc_tag(25, enc_bytes(make_mso_map()))), 7, "invalid_value", None),
        ("mso_head_too_long", make_doc(wrapped=bytes([0xD8, 0x18, 0x59, 0x01, 0x2D]) + make_mso_map(map_len=300)), 7, "cbor_mso_wrapper", "truncated"),
        ("mso_head_too_short", make_doc(wrapped=bytes([0xD8, 0x18, 0x59, 0x01, 0x2B]) + make_mso_map(map_len=300)), 7, "cbor_mso_wrapper", "trailing_bytes"),
        ("item_five_entries", make_doc(items=[make_item(entries=[("digestID", enc_uint(7)), ("random", enc_bytes(b"r")), ("elementIdentifier", enc_text("family_name")), ("elementValue", enc_text("M")), ("extra", enc_uint(1))])]), 7, "invalid_length", None),
        ("item_unknown_key", make_doc(items=[make_item(entries=[("digestID", enc_uint(7)), ("random", enc_bytes(b"r")), ("elementIdentifier", enc_text("family_name")), ("elementValuf", enc_text("M"))])]), 7, "missing_field", None),
        ("item_unknown_key_4", make_doc(items=[make_item(entries=[("digestID", enc_uint(7)), ("randum", enc_bytes(b"r")), ("elementIdentifier", enc_text("family_name")), ("elementValue", enc_text("M"))])]), 7, "unknown_field", None),
        ("item_dup_digest_id", make_doc(items=[make_item(entries=[("digestID", enc_uint(7)), ("digestID", enc_uint(7)), ("elementIdentifier", enc_text("family_name")), ("elementValue", enc_text("M"))])]), 7, "duplicate_field", None),
        ("item_negative_digest_id", make_doc(items=[make_item(digest_id=-1)]), 7, "invalid_value", None),
        ("item_digest_missing_in_mso", make_doc(items=[make_item(digest_id=8)]), 7, "missing_field", None),
        ("item_not_tag24", make_doc(items=[]) , 7, None, None),
        ("dup_namespace", make_doc(dup_namespace=True), 7, "duplicate_field", None),
        ("items_257", make_doc(items=[make_item()] * 257), 7, "too_many_items", None),
        ("item_map_trailing", make_doc(items=[make_item() + b"\x00"]), 7, "cbor_item", "trailing_bytes"),
        ("mso_map_trailing", make_doc(mso_map=bytes([0xA0]) + bytes(299)), 7, "cbor_mso_map", "trailing_bytes"),
    ]
    for name, doc, version, status, detail in bad:
        if status is None:
            # an accepted edge: no items at all
            p = parse_mdoc(doc, b"", b"x", version)
            w(f"parse_hex {name} {doc.hex()} {version} {parse_fields(p)}")
            continue
        try:
            parse_mdoc(doc, b"", b"x", version)
            fail(f"{name}: accepted, expected {status}")
        except ParseError as e:
            if e.status != status or (detail and e.detail != detail):
                fail(f"{name}: got {e.status}/{e.detail}, expected {status}/{detail}")
            w(f"parse_reject {name} {doc.hex()} {version} {status}" + (f" {detail}" if detail else ""))
    # a coordinate above 32 bytes keeps its last 32 and one below is left-padded,
    # as upstream's from_bytes_be reads them; distinguishable bytes
    mso_base_pairs = [
        (enc_text("docType"), enc_text("org.iso.18013.5.1.mDL")),
        (enc_text("validityInfo"), enc_map([(enc_text("validFrom"), enc_text("2024-01-01T00:00:00Z")),
                                             (enc_text("validUntil"), enc_text("2034-01-01T00:00:00Z"))])),
        (enc_text("deviceKeyInfo"), enc_map([(enc_text("deviceKey"),
                                               enc_map([(enc_nint(-2), enc_bytes(bytes(range(1, 34)))),
                                                        (enc_nint(-3), enc_bytes(bytes(range(101, 132))))]))])),
        (enc_text("valueDigests"), enc_map([(enc_text("org.iso.18013.5.1"), enc_map([(enc_uint(7), enc_bytes(bytes(32)))]))])),
        (enc_text("pad"), enc_bytes(bytes(150))),
    ]
    # x of 33 bytes 1..33 keeps 2..33 (the last 32); y of 31 bytes 101..131
    # is left-padded with one zero
    doc = make_doc(mso_map=enc_map(mso_base_pairs))
    p = parse_mdoc(doc, b"", b"x", 7)
    if p["device_pk_x"] != bytes(range(2, 34)):
        fail("coordinate_33_31: the last 32 bytes of x were not kept")
    if p["device_pk_y"] != bytes([0]) + bytes(range(101, 132)):
        fail("coordinate_33_31: y was not left-padded")
    w(f"parse_hex coordinate_33_31 {doc.hex()} 7 {parse_fields(p)}")

    # two -2 keys: the first value not a byte string is UnexpectedType at
    # once (upstream's order); two byte strings are DuplicateField
    def key_map(x_entries):
        pairs = list(mso_base_pairs)
        pairs[2] = (enc_text("deviceKeyInfo"), enc_map([(enc_text("deviceKey"),
                     enc_map(x_entries + [(enc_nint(-3), enc_bytes(bytes(32)))]))]))
        return enc_map(pairs)
    for name, entries, status in [
        ("coordinate_first_not_bytes", [(enc_nint(-2), enc_uint(1)), (enc_nint(-2), enc_bytes(bytes(32)))], "unexpected_type"),
        ("coordinate_duplicate", [(enc_nint(-2), enc_bytes(bytes(32))), (enc_nint(-2), enc_bytes(bytes(32)))], "duplicate_field"),
        ("coordinate_missing", [], "missing_field"),
    ]:
        doc = make_doc(mso_map=key_map(entries))
        try:
            parse_mdoc(doc, b"", b"x", 7)
            fail(f"{name}: accepted")
        except ParseError as e:
            if e.status != status:
                fail(f"{name}: got {e.status}, expected {status}")
        w(f"parse_reject {name} {doc.hex()} 7 {status}")

    out = out_dir / "mdoc_parse.txt"
    out.write_text("\n".join(lines) + "\n")
    print(f"wrote {out} ({sum(1 for l in lines if l and not l.startswith('#'))} cases)")


if __name__ == "__main__":
    main()
