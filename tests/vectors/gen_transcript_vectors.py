#!/usr/bin/env python3
"""Generator for the stage 4 (transcript) known-answer vectors:
  sha256.txt          sha256 <message> <digest>
  aes256.txt          aes256 <key> <block> <ciphertext>
  transcript_fs.txt   the Appendix B.2 steps, as a script (see below)
  zk_proof_p256_b3_2.txt, zk_proof_gf2_128_b3_3.txt
                      label, root, circuit identifier and sumcheck part
                      of the two Appendix B.3 proofs

Independent reference of the Fiat-Shamir transcript of IETF
draft-google-cfrg-libzk-03, Sections 3.1 to 3.4: SHA-256 from hashlib,
AES-256 single-block encryption written here from FIPS 197 (the S-box
computed from the field inverse and the affine map, not copied), the
FsPrf counter mode, the TLV codec, nat, choose and the prime-field
sampler written from the draft's text. No third-party package.

The cases are copied constants from the standards, not recomputed
values: FIPS 180-4 examples and CAVP SHA256ShortMsg cases for SHA-256;
FIPS 197 Appendix C.3 and NIST SP 800-38A Appendix F.5.5 (CTR-AES256,
each counter block as a single-block encryption) for AES-256. The
generator recomputes every one of them and aborts with a non-zero exit
status on any mismatch, so a wrong constant and a wrong reference are
both caught before the files are written.

Appendix B.2 of the draft is reproduced in full by the transcript
written here, from the constants copied out of the draft: the 48 field
elements, the 24 nat results and the 6 choose lists (B.2.1 to B.2.5,
chained). Any mismatch aborts. The vector file then carries the steps as
a script the harness replays on the library's transcript, with the
draft's values as printed (big-endian integers for the elements).

Appendix B.3 gives two complete proofs. Their root (the first 32 bytes)
and sumcheck part (the next 4 logw + 2 elements per layer, Section 7.5
and 7.3) are copied here from the "Complete Proof Serialization" blocks
of B.3.2 and B.3.3, with the labels of the upstream unit tests and the
all-zero circuit identifier they use. Before writing them out, the
generator reads the sumcheck part into the pad order of Section 6.5 and
compares it with the padded proof of the tier 3 recording of the same
circuit (tests/vectors/upstream/, ADR 0027), then replays the transcript
of zk/verifier.rs with its own transcript (label, root, statement,
begin_circuit, per layer begin_layer, round_poly, end_layer, then
alpha_input) and compares every challenge with the recording. Any
mismatch aborts. The harness sumcheck_kat does the same with the
library's reader and Replay_Challenges (ADR 0032).

Usage: python3 -I gen_transcript_vectors.py [output-directory]
Output is deterministic (no timestamps).
"""

import hashlib
import sys
from pathlib import Path

# ----------------------------------------------------------------------
# AES-256, FIPS 197, from scratch
# ----------------------------------------------------------------------


def gf_mul(a, b):
    """Multiplication in GF(2^8) modulo x^8 + x^4 + x^3 + x + 1."""
    r = 0
    while b:
        if b & 1:
            r ^= a
        a <<= 1
        if a & 0x100:
            a ^= 0x11B
        b >>= 1
    return r


def gf_inv(a):
    if a == 0:
        return 0
    for x in range(1, 256):
        if gf_mul(a, x) == 1:
            return x
    raise AssertionError("no inverse")


def make_sbox():
    """FIPS 197 Section 5.1.1: inverse in GF(2^8), then the affine map."""
    box = []
    for a in range(256):
        b = gf_inv(a)
        s = 0
        for i in range(8):
            bit = (
                (b >> i)
                ^ (b >> ((i + 4) % 8))
                ^ (b >> ((i + 5) % 8))
                ^ (b >> ((i + 6) % 8))
                ^ (b >> ((i + 7) % 8))
                ^ (0x63 >> i)
            ) & 1
            s |= bit << i
        box.append(s)
    return box


SBOX = make_sbox()

# The first row of the S-box as printed in FIPS 197 Figure 7, as a
# guard against a wrong affine map.
assert SBOX[:16] == [
    0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5,
    0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
], "S-box first row disagrees with FIPS 197 Figure 7"


def xtime(a):
    a <<= 1
    return (a ^ 0x1B) & 0xFF if a & 0x100 else a


def expand_key(key):
    """FIPS 197 Section 5.2 for Nk = 8: 60 words, 15 round keys."""
    assert len(key) == 32
    w = [list(key[4 * i:4 * i + 4]) for i in range(8)]
    rcon = 1
    for i in range(8, 60):
        t = list(w[i - 1])
        if i % 8 == 0:
            t = t[1:] + t[:1]
            t = [SBOX[b] for b in t]
            t[0] ^= rcon
            rcon = xtime(rcon)
        elif i % 8 == 4:
            t = [SBOX[b] for b in t]
        w.append([w[i - 8][j] ^ t[j] for j in range(4)])
    return [sum((w[4 * r + c] for c in range(4)), []) for r in range(15)]


def encrypt_block(round_keys, block):
    """FIPS 197 Section 5.1; the state is column-major, s[r][c] at 4c + r."""
    assert len(block) == 16
    s = [block[i] ^ round_keys[0][i] for i in range(16)]
    for rnd in range(1, 15):
        s = [SBOX[b] for b in s]
        s = [s[4 * ((c + r) % 4) + r] for c in range(4) for r in range(4)]
        if rnd != 14:
            out = []
            for c in range(4):
                a = s[4 * c:4 * c + 4]
                out += [
                    xtime(a[0]) ^ xtime(a[1]) ^ a[1] ^ a[2] ^ a[3],
                    a[0] ^ xtime(a[1]) ^ xtime(a[2]) ^ a[2] ^ a[3],
                    a[0] ^ a[1] ^ xtime(a[2]) ^ xtime(a[3]) ^ a[3],
                    xtime(a[0]) ^ a[0] ^ a[1] ^ a[2] ^ xtime(a[3]),
                ]
            s = out
        s = [s[i] ^ round_keys[rnd][i] for i in range(16)]
    return bytes(s)


def aes256_encrypt(key, block):
    return encrypt_block(expand_key(key), block)


# ----------------------------------------------------------------------
# The transcript, draft Sections 3.1 to 3.4
# ----------------------------------------------------------------------


class FsPrf:
    """Section 3.1.1: Block[i] = AES256(SEED, ID(i)), ID(i) the 16-byte
    little-endian encoding of i from 0; unread bytes of a block are kept."""

    def __init__(self, seed):
        self.round_keys = expand_key(seed)
        self.counter = 0
        self.buffer = b""

    def get(self, n):
        out = b""
        while len(out) < n:
            if not self.buffer:
                block = self.counter.to_bytes(16, "little")
                self.buffer = encrypt_block(self.round_keys, block)
                self.counter += 1
            take = min(n - len(out), len(self.buffer))
            out += self.buffer[:take]
            self.buffer = self.buffer[take:]
        return out


class Transcript:
    """Sections 3.1 and 3.2: SHA-256 accumulator, generator discarded on
    every write, seeded by the digest of everything absorbed so far."""

    def __init__(self, label):
        self.hash = hashlib.sha256()
        self.gen = None
        self.write_bytes(label)

    def absorb(self, data):
        self.gen = None
        self.hash.update(data)

    def write_bytes(self, data):
        self.absorb(b"\x00")
        self.absorb(len(data).to_bytes(8, "little"))
        self.absorb(data)

    def write0(self, n):
        self.write_bytes(bytes(n))

    def write_elt(self, elt_bytes):
        self.absorb(b"\x01")
        self.absorb(elt_bytes)

    def write_slice(self, elts):
        self.absorb(b"\x02")
        self.absorb(len(elts).to_bytes(8, "little"))
        for e in elts:
            self.absorb(e)

    def bytes(self, n):
        if self.gen is None:
            self.gen = FsPrf(self.hash.digest())
        return self.gen.get(n)

    def nat(self, n):
        """Section 3.4.1."""
        assert n > 0
        length = (n.bit_length() + 7) // 8
        mask = 0
        while (n & mask) != n:
            mask = (mask << 1) | 1
        while True:
            r = int.from_bytes(self.bytes(length), "little") & mask
            if r < n:
                return r

    def choose(self, n, k):
        """Section 3.4.2."""
        if n == 0 or k == 0:
            return []
        assert n >= k
        a = list(range(n))
        res = []
        for i in range(k):
            j = i + self.nat(n - i)
            a[i], a[j] = a[j], a[i]
            res.append(a[i])
        return res

    def field_elt(self, p):
        """Section 3.4.3, prime field: 32 bytes little-endian, rejected
        at or above p."""
        while True:
            v = int.from_bytes(self.bytes(32), "little")
            if v < p:
                return v


# ----------------------------------------------------------------------
# Appendix B.2: the 4-word prime field and the five chained steps
# ----------------------------------------------------------------------

# The prime of B.2 (the secp256k1 prime, 2^256 - 2^32 - 977); elements
# are written as 32 bytes little-endian (Section 7.2.1).
B2_P = 115792089237316195423570985008687907853269984665640564039457584007908834671663
assert B2_P == 2**256 - 2**32 - 977


def b2_elt_bytes(v):
    return v.to_bytes(32, "little")


B2_1_ELEMENTS = [
    "8b297f0bffd583c6c6b6796385d5fd20a08665733b833970ebdd1054bbbc1b14",
    "0667c08ad7f38efec5f30dc8aa4f20d749cdcf96d63a770f9810ac5c0ca8dcb1",
    "c8037fc12d4da00b5dc7597e3042f33f72a06f970cb71fb6b103ebb5419d8a6b",
    "fbbcfa1eac48728fbfdacc1c21e2f78119457e0846337e46140e38e62856c4c5",
    "5358ae603691cc759faeb572fb6642654ea1c3dbc8f81d00276dd8c4df95aa58",
    "5266158c3c895dede5a23b6ce85a9f564b8059ebfcd1741f54497ec58189873e",
    "3ecea4b2343c007fc32f2aff40dc7320945f101ecae5d52494db21ad326e9739",
    "6462dd575e6b874118607212feec7ce5417ae3bf0f2e86604596f35d48bbaea2",
    "6d56c703c369edea3595db6b958241580ae9b4a76fead961413ed9e9e5852dcd",
    "6d31073cee650212a71b7b13e9f951e00ef3b14a008a79dd95047b26a4a83d06",
    "1b9e2a6666da63c43e52227d91a8a7f0bd5311f63c2e3a18839133375639e6cb",
    "332ea49dd23dd4745631ecbb15696192b1fa127256baf7a0483fd27db6f09a48",
    "43e735927ccbdc4d5ce912675d638d6d3dc8eef3def34504304e938846f157d6",
    "dc4a8868ae75e733a7257a8589230392a98d78594836dfccd01304742b5b3ad5",
    "976353931711c634f2691e507b119fd7f6e653d419a2620676122db08db18765",
    "332729ab436dca654866a9382deaee0add6fb7e90a80261f1488e56598e8bc99",
]

B2_2_ELEMENTS = [
    "609db3e9a8f548df038519fa46cef23eb8c6553d3c1f698604e60a51613a738e",
    "1cb69cb31999eb88e83c7586aac53f5e3286b084b0cf9e43619b48df01e0a310",
    "3bf36e3ddc690a1b12b417628c115959b373d056c90c42dc2417baf46f538868",
    "e336594f29dcda52e48896517b5cdb2d062ffd861ab02db5f8ca197aacc635f6",
    "c1f396a8bad16bb0f57da6d380402a25b571bd4691226d11449a741440e325c8",
    "5195336ec73751de066e3a8939b40c3c5555f1a513486dfc50dcf4c2d47e6ff2",
    "8dcf872f3ded2b7ed1d1ee9a2b125bedc6eacd3c09b3a4a5286d8fc2fc3a6634",
    "950dd2ef7be25eab686a6688497962ee4ad521da12b9ff3d8e56ad9435885b12",
    "e14389d1d8448678cac33fdbc9aab20dba019e75149d170dd2f353891cd4b84f",
    "e84906c09cd6423865baf64e48027cc598d52bdb90b17524c87ea892e53b5200",
    "493cea587f1ec5622c04221cd6e5a41c26c1c1c24c0375f7aaa367d9678d83bc",
    "5aca0010aced30bcb3b84a7f10ea39c4269ab7c92fcb6cff52958d8921ef2cc5",
    "4498fa8340f41467c0fa813bd0ca83ef6e1c4b85c7b1168a94339fd9e8296139",
    "f9a95b738a8e775421b1baa503abbeed2d283b236ebba25e1954b3c993d30a3d",
    "98178711d03a0b1204ebb56b37bd3a2724dfb08e4dc925609391768b126d21f2",
    "79251f49534f5c4b10b798b2dbf6e80a3b07593f616ce6a9617ccc61040aac78",
]

B2_3_ELEMENTS = [
    "ae1a921288590205fc24543303ff527476359b8db4a983b2886a133b02f3217e",
    "8c5d52a04b295f9fdb45ab66100fa00ca32c9634aa87cbbdb2bc3e1912459feb",
    "12f82963b5b242156f6e9eb756eddee7652b60c7d6394403f7bd995e0b9bcd9c",
    "880aa50b049b3939055deb7933749d338bb3fb5f64a9adf95019e6cfc232995c",
    "f8558f693f0fa6df20a37147a898fb4c678831f566d80113bbe2cdcd18285da2",
    "bbcc8d9b46f88bc8c6cec0ad2d5e49508b7db91d548548eddc61800de1329e1c",
    "479a17244398caae8155a73438a22583df7de10a8a2e12ad53ddd3bc7305fac9",
    "9ba1917f1227932250288a843f64b4e7b7f47a5fbc16c111f6e1f76235ccf38c",
    "d1582138045d1636fb7f677c9e8a4a4143ce2b2bb54fb4f49fb0ad1fee5df6b4",
    "05331e5b8508f79c017a8dfbbb805f3f8c5e3e4bc417e44849b9212439646331",
    "b6b95862194ca52dcaa9ee651b7fc5b708f43feae108bb9a7f95213f4d069048",
    "e86b1602f0a54c4e237867ebaf05e7581464fd238e50f6ed9c3cea63909c8e60",
    "b7280439f3b21b113ff29cefe39292d5e2d137709c3d3cec36473a0f97a24e62",
    "beaa5e08257d232506fb3e46c6daa29e0859c34c7d0cd673bc6706ee261ae059",
    "0691ead55728cd087a1952b22b6628ba4e26fbefc8debeec5e6fbc3a16f637be",
    "47dc31f6d8bc9c44290781176df3e4b95ac8793a4a42fa5859c564d92d6d5af5",
]

B2_4_NAT_ARGS = [
    1, 1, 1, 2, 2, 2, 7, 7, 7, 7, 32, 32, 32, 32, 256, 256, 256, 256,
    1000, 10000, 60000, 65535, 100000, 100000,
]
B2_4_NAT_RESULTS = [
    0, 0, 0, 0, 0, 0, 3, 0, 4, 5, 10, 30, 27, 22, 100, 189, 3, 92,
    999, 3105, 40886, 51590, 56367, 10678,
]

B2_5_CHOOSE = [
    (31, 20, [10, 29, 30, 11, 4, 15, 16, 28, 19, 21, 25, 18, 17, 3, 5, 23,
              24, 22, 6, 1]),
    (32, 20, [3, 17, 18, 8, 30, 7, 14, 19, 25, 23, 12, 4, 31, 16, 0, 6, 20,
              27, 11, 10]),
    (63, 20, [9, 56, 61, 45, 35, 53, 51, 3, 39, 32, 31, 6, 59, 58, 54, 22,
              27, 62, 55, 19]),
    (64, 20, [12, 52, 39, 17, 51, 38, 58, 2, 28, 27, 46, 63, 61, 50, 40,
              55, 47, 13, 56, 32]),
    (1000, 20, [157, 668, 572, 138, 913, 994, 797, 249, 440, 723, 489, 241,
                383, 108, 710, 341, 406, 585, 42, 692]),
    (65535, 20, [40745, 48408, 17108, 44500, 53993, 10008, 24910, 52200,
                 61265, 54989, 41237, 25958, 28697, 61187, 34729, 3525,
                 9005, 38627, 9724, 12169]),
]


def b2_script():
    """Replay Appendix B.2 on the transcript above, checking every value
    against the draft, and return the script lines for the harness."""
    lines = []
    t = Transcript(b"test")
    lines.append("reset " + b"test".hex())

    def elements(expected, where):
        for i, want in enumerate(expected):
            got = t.field_elt(B2_P)
            if "%064x" % got != want:
                fail("%s element %d: got %064x" % (where, i, got))
            lines.append("elt " + want)

    data = bytes(range(100))
    t.write_bytes(data)
    lines.append("write_bytes " + data.hex())
    elements(B2_1_ELEMENTS, "B.2.1")

    t.write_elt(b2_elt_bytes(7))
    lines.append("write_elt " + b2_elt_bytes(7).hex())
    elements(B2_2_ELEMENTS, "B.2.2")

    arr = [b2_elt_bytes(8), b2_elt_bytes(9)]
    t.write_slice(arr)
    lines.append("write_slice 2 " + (arr[0] + arr[1]).hex())
    elements(B2_3_ELEMENTS, "B.2.3")

    t.write_bytes(b"nats")
    lines.append("write_bytes " + b"nats".hex())
    for n, want in zip(B2_4_NAT_ARGS, B2_4_NAT_RESULTS):
        got = t.nat(n)
        if got != want:
            fail("B.2.4 nat(%d): got %d, draft says %d" % (n, got, want))
        lines.append("nat %d %d" % (n, want))

    t.write_bytes(b"choose")
    lines.append("write_bytes " + b"choose".hex())
    for m, k, want in B2_5_CHOOSE:
        got = t.choose(m, k)
        if got != want:
            fail("B.2.5 choose(%d, %d): got %s" % (m, k, got))
        lines.append("choose %d %d %s" % (m, k, ",".join(str(x) for x in want)))
    return lines


# ----------------------------------------------------------------------
# Appendix B.3: the two proofs against the tier 3 recordings
# ----------------------------------------------------------------------

P256_P = 2**256 - 2**224 + 2**192 + 2**96 - 1
MAX_LOGW = 40
ZERO_CIRCUIT_ID = bytes(32)

# label, root, sumcheck part (hex), field, recording file; the sumcheck
# part is the 768 (384) bytes that follow the root in the complete
# serialisation of B.3.2 (B.3.3). Stage 5 (ADR 0040): the configuration
# (RATE_INV, NREQ, NCOL), the Merkle nonces listed in B.3.1 and the
# Ligero part, the 4652 (2632) bytes that follow the sumcheck part to
# the end of the serialisation (Section 7.4).
B3_PROOFS = [
    {
        "name": "b3_2_sgonal",
        "field": "p256",
        "label": b"sgonal_test_vector_p256",
        "root": "803aba51698a4bc4dddaa74b1d9971b8ec7c49c4847a7ff18e41dd476edf9b04",
        "sumcheck": (
            "ed0282f97ed9c5be6ced2c1092a34579d9786d1de4dc5404c4d3435f84bbc1a0"
            "ea352432ab6ad5b2e46e1b126c18103748824fb252ac17406898c6c27d70fb3b"
            "87b96f0d4c7992b03e160e17b0c98efba101daca039575c793b6bedd4dd10541"
            "e2d6701be3e75c019a63fa1595741b3e25c7e111014a4dd792bb47e6aec01aa3"
            "9da1d23e9ac2386889efe3a024a6622bede3f862a41d8267dadbfb491901a6e6"
            "845b0503dab880fc756684f4bf3e71acf1eacb596aa6bc9364eaa0e2c3093dfe"
            "bde19129e45b77c16d27405766a2bd5db5203ab0c116a253127f666354b1cf97"
            "c71fa6fc3f90016fa778aea298eaf379f34b043b5da3bd161fec2530eddbfb0e"
            "247e4e615f4469abd04fa996ecf232e6fde51763eacb87dacc10b5b2aabf9979"
            "0c745c33d07537d414be750e6c0dedc14b72b4e5e86be92a7aa87606ad2e8d01"
            "d1b1306672a1ab21cd6f676272baadfac7b2fb453daef8415e2f38128f833f6c"
            "7b8579a9a4c6f1cc6517bba16e904726ed462896a797dae48f817b81be630a95"
            "629f60d183eedd9a4c433ef2f0a4a4294ad5690f2c07b3385e3f2e73fb2abbe3"
            "e75148bc1051abd7ce21c46f42517911c2c790cc2101ee85fa50620b644f12b8"
            "fc0c9f8522fecaee7c284b7e7006c88df35d1c4f6bae0268751507872f47780c"
            "4bfe833a7a0b6f4f403d0d1b58bf891a48083a78ac5e473f7e012b388fe2f443"
            "3099d256c6b153cfc422d6f48f6229a7107ca4d5dda7d7ffc033ef3ba2269179"
            "089e4889f379d1f97f03b3f0b3206245781dd6841f820fd931ad42fd8a1f4407"
            "7dbd42f7ea2d3c4d5ecc85e5688c2a5f67abe0a456390b85f9fc2d13a5ca8640"
            "23e611c6b1ba75967bcbb2f2a8c142a7044e9c54b96a09981fe5b674815e9fd7"
            "d8a8d76169e11800edceb9928ec62feb70f0e3593fed2ab0d545f29b1d2ea20c"
            "fd8320f828609d5e45cf0dff488401e170d2945ed7559c49f5de2bc7f063f4d6"
            "3d400922fd141c40d4a74abf045e1b7af4b50ea1fe5fb215cdd286e4ba0e9708"
            "bde5320999b8682f9ef6c05744395290815697ca993103f0c0a7704730a05212"
        ),
        "recording": "upstream/sumcheck_core_p256_b3_2_sgonal.txt",
        "config": (4, 6, 64),
        "nonces": [
            "d406ef8c46fd239545520a5363d67d61bad1750d37b087c1e3611a12d47e477f",
            "5fe986cae604828cae4bfbbc7415d64cd5e755848755a0d9d3120ad46eea8d86",
            "0fa8593d45fef897767ce05ec5feac76d8f21910bc0ada856aeaa777629048ef",
            "63619b9a06c668a2414e46f859a2fdb1ba63e8718fa6ce4bf532b2fb0b8ff4ef",
            "c9e35514c0ff4b62cb9730116947bef69325f3a4c1c6553b7bd161754f8008d8",
            "057ec47e747c61954419b634dec16eb6adfeafb1a0e9fafbb2a9c85fcf9bced4",
        ],
        "ligero": (
            "76b5b1ff2c0f08b364e0c90463874b7a76aead588a0578abd97995a7acc018fa"
            "a3616f94202b67601ace16cfa22118b6d3c358a9602db7b4c41cf3cad18f0c45"
            "016e975539c3308d01c6398983c249a7d7ef16b56c075d2e5768ce4548dcc4e8"
            "9a69487862c72b530ad0c86d0254b5324e20a9fbbe424505cf354e3e8ef74eca"
            "ca42ce218f8ebddeaf17a46e31016bff10c73496d511ca71d3ee15fdbb7a3904"
            "bfae54b1581beb69cc2b0c890fbb74baa431eec4cef4ad02df96f82bd5ac46c4"
            "e26c97007a5377b096adaf4679a39b6322eefeaf4d2a596964457f7e40d658af"
            "1a489d73d0f0d9aebd01703f10423f096f352b2eceba178e81e9917eaa5f1df0"
            "fc7b7dff769848968a09789ab02a54b6c1176e34a9a8f1da2cf19ae2c37d05a5"
            "42407401e53e23a3c2f1c0427578f71933f335ef419a3804338629c5b05220ff"
            "077d527eeb62fa14e6410ddd2bfd704eabf68ae2eff1c3df789acd0b651dddfa"
            "7569c524daad94e3b0c16c5bfe9ae509c138e1c6164c18b17047b6aa08d4b490"
            "b227ebe71d884fd6b6c64b3aedf6a184e8f2364ce58365210b22f9be3527f219"
            "e97845a53f0d975f26e97125bb2125223f9a86202ac62ca3c4e650295d2eda82"
            "4aaee83318308714b3c37ba11b7f4c92c1a53eb9279c473610e2ce9dacf55993"
            "f1cb794852fe80c1be4f203c82422826a72eb7ce93a806f709d998504f785cbf"
            "cce45c56c3ee3154074e99a3c2e53fea547119ea179ec7d0bfe784556b25d7d6"
            "e56fe095b33f2d05e5ac1b8c3fd581811c57648bbef03dad260649070a2446c8"
            "592f3e7693a2f1e9ee86473788840517e38d6bc99e2919b3994a6b6a35efb0b6"
            "a37225353d4663a61636cfcd81ae2164027586165b804d3ff9e818774b6dce75"
            "b32aa849cc964bdaef98457cf2abf90544087d3eaf9dff4897285934cfb6ce49"
            "298d4479739de6f80581c0398ba30cffed7b093c3bc2074b558059a7db87ade7"
            "6ad0348c4ec12499b8d0d3e03a354d27eb901485cea2b58edf01e0859e694c70"
            "4bb12f2d28227166b476d676f009e4e302fda4ca5ec0692dede769ae800be3e6"
            "14f3f5ff2552fc2528c94b24fcf74f8b61e0ea76903dca73afb62b35b9fac7dc"
            "0bcaad0c17267683aac5e823cd6dbd796f3210dea30491d5bd2d8dd6daabda79"
            "213dc3956200cacee1dc8319a3de252f3fb8df6079cc2f4be51c873be5f66681"
            "03c9d8a4a5c505bcdd14174eeb1f3c82c156d2d3bc57f68501b9d5ba5af10372"
            "797b1a93d738c013c0625833861ffdfaf7a9b0e00f8a33a41f87d72100f75b4b"
            "70e8ded7b9a0f44f954915faf6bfc721b367698abcc6b33be195e2a99a326997"
            "af0568a9f0e5b65984ec416b715d9f2b2b9ad742eb051fd7c29d0f1c955050b5"
            "c38dd1c85c09b1e080ff0dc9c8f10de0d86d07ddbb98267f3c3bf27ae62bac92"
            "2a62ecbe8c8e1a78b1c19ab25dbf95c52ac077a2610063ac19382d149a18e54a"
            "b3b7a843250a186d8540184df41bd5a6be7e3660ef28bba8bb9f4407dbd3b638"
            "a30e4a18c7f60404ec06872065179fc55a1195ced24ef2b3798a28acbfbc320a"
            "c4d8b1850e6bfb3d3a5730d29bd3f93d6530cccc5f669a058bf14590ce383f60"
            "93a386a01cfa72cc429a3d127939fbb73778a8ce92202c29ccdb61fedef35cb7"
            "d6cbc98d559f81afd81a472dc8cfbf47074731f18ee4b8871ec5c7508328ad16"
            "319c11de3dd35de85e9000a8c8dd77947a60221cc16b8278d4b03bf6858c252c"
            "1c19b7fbb432c39fe6db2f04bc7e7ffbda7afef966eaffc1a10e271f688c6f5f"
            "c95328f94196dff3a42b5e7c4960b5e457aa322afeaddf2dd4cc756e7379bf32"
            "66faf76c4153d4bfbef3fcd2fad88b1e7e7d78246cbfa96b7f9edbedf02d210d"
            "c247ed0fd14218243eb3c6cd0866cd2cd49f84a567c780b1d15ad44e5ecb916b"
            "0819bb8d57ac002a7b007a35c4fdd3fa48694131a637482f781666a3d69c5010"
            "d406ef8c46fd239545520a5363d67d61bad1750d37b087c1e3611a12d47e477f"
            "5fe986cae604828cae4bfbbc7415d64cd5e755848755a0d9d3120ad46eea8d86"
            "0fa8593d45fef897767ce05ec5feac76d8f21910bc0ada856aeaa777629048ef"
            "63619b9a06c668a2414e46f859a2fdb1ba63e8718fa6ce4bf532b2fb0b8ff4ef"
            "c9e35514c0ff4b62cb9730116947bef69325f3a4c1c6553b7bd161754f8008d8"
            "057ec47e747c61954419b634dec16eb6adfeafb1a0e9fafbb2a9c85fcf9bced4"
            "00000000540000002b520d64d1a48758b4e6b56b93cda7b71767e41aa21bc5a4"
            "02f968032a5d990b35d916cce85bc34911ea5f3413ae54313eb9ac0de227c114"
            "4dfc0835d6ac56fb37cda5179524c5390e72928bf48c4d7f2c6ead37d9cbf9b5"
            "3f4219ed6ba49b8620a6a6ea318ea301b442a8be1c6198b0950ff8e748772dd2"
            "08758a9b6d4ada5bb54472abd5aef2cf83f64227b8e8528f6883130523388ac2"
            "49501c5678fce39ee6098cf92e675f98ca0fd7f16d83f18879a6a54196a2bf0c"
            "c8222d791e9870ab8444ab45f7abf52736bd00b8e1583f31faf872d474aab750"
            "3100adaa4eabed15dd194b4ce7576b58e33ca6c044b104545764d9af7b7708cb"
            "8a9d7d2eb82564c24b9ec487aca878ac6f243cf89dccff327fa5c61698a0f14f"
            "33ddfadccd7748482c72c5234b5a2663256ac36644692aaeab1038b87c40be58"
            "2d28d495f9042be70a724e89c5462323ca1dca74273a6f2bd8f8b1f51c7da4f0"
            "f66732d4040d29c916ac01b6e1f7cd411a8783caf37f0b8fc60c330c6fe1377f"
            "956273ebd37c6aa2acb55ed76b7589c4e4ab006085057f301369f9b4407745ec"
            "25420dad03bc2c134efe1ad4dd9ef9f03a617f79c69a4d90e44c2ccf48ac1ea1"
            "f7450fe7b1603ec96e70400ec7ed1d645e13161a9c42a7aee7922a3910d9c7a4"
            "a2375849375f8c408d7ce8eedc7fd61082f91483d4ae597530423109fae058b9"
            "0f43f63f397e1afe4ad76b9d73be712c9ce50c5feaa4ccff48f9053f130a04ce"
            "e5121781f4ca524e9bc381bf627dcac1aabb1cb6781b4510874f60a8e1c18801"
            "6e6b49f67827c9512b3f2b3d412b35b3e371e6f40014d975f54c54e0f404d6cb"
            "999196504009a891b0f2710df5054a387cdc5cb7bb147f154e1d335197824102"
            "34e6e1f001e511e3896b61ac9e75d111da33a0c3c91414f37ba8b169809e7354"
            "53e9698f643af6f1b76feb3f50f8e65f42e8803d2f128e36928c021a8a8e8411"
            "a9f02d36efc09a1f71cee349a36dc6162254eb04210eb08cae8e955a5720891f"
            "d89f5b7bd61c0e0bf62471a70e8f8ca8addde0aba195388d60452fa98ec72d5a"
            "a4751a3a820db5e869cc80f2f9a62d18f7367d1c1ad339dfd5760dc9c11b244a"
            "52d7275349a721d80939f2143bed6891a68b950946453c7efb8c885974e6e250"
            "9b63aa59278e30b78659f736c5a6f84e9c0e5cfb04de3a06a35e3be04e7d9bf8"
            "5ee025cf5b4ed1a5038ab30e6d304245c6d5573a3ead0da8de3375985a8c32ca"
            "06658532f827ca216d8d24c4ce16ae39361b877bf4cd0994394144bb8e52737e"
            "d70732eea60cf5aec5f474bed7baa5124ec1e454c818da069aee55b9e36b4680"
            "7b460d5ee2684d650c3ebbe7d5425186e6a63ef2497b4e9028976991850310fa"
            "ab526bf6a3f0c9800c655aa5bff7cabc560f82d4e885c496d3111025215121ad"
            "ff4a55487783399b76d3a0e7376fede3865e3558f219d82fc60207d921549c85"
            "8dfc8c08fddb61e51c776e9650ef8c757f9d52c64793e3b30c87e18bdf0de670"
            "ddfdfe3785026ea7acabc069bca44ee228d707a03d78d0ef64a1a5c9bf5a66d9"
            "a5fcc8168954fb699cd74f4568007e9d7d147ea2cabe9e85e00425f60dc89530"
            "9529d6251a295d883cae2f92cc200a5bcd6616d8125517d95366ce99e151d51a"
            "3b43784537c55ca470dc003aa92f72a706d9558711fe3cce3603f40d90d041cf"
            "58b8f3b93d2079b55104ccf9694dcc2dc7b38cd7b3395db8a0b6e570c6f7fbad"
            "44d44111ef8cbc38c66a26571835f13d66eabd68de56a707508e850b1d8057d3"
            "bb0389833dd4b0060c0437a75418bcea0ad4d0907c22ebac99ea69f04015635f"
            "fd217672b5531e2d6484572c4093462c7464f9af152fabe10b8515a160750e24"
            "6302e640d837778443985dabcab9a19e9ebfbabb1d511f8fbd1ce7d163c6bc85"
            "513a3954876f064d855de13479202a87c513db6f43efcf3fe734c740606c1aa4"
            "3d5c42a3807a8c06e25c4952bbb951b4d58269d67016e301b8660cae3bf4ebe5"
            "56cbc7ba99b0b020cb52faffffc9ba2f9cd6d88e91cabbed8f9c325785b98851"
            "13198b52bd28324c1f332b82accf2055642c4af0cae07c1bf46f9cafecd81d1a"
            "efe8e3b777f19ecdd3a6e921faae6e1d8e20764e12dc1d02917ae0dfeb1cdad1"
            "07c1744b980c9405d8d3ff53869e77c1e299d419216ad68894fcee7e4328b3b3"
            "47abd813f9a833f32cf932591570bebfe056b5b98ffb614e576192a4d4af8b74"
            "0216d833d7334eb9eab0334c635f86c681d6c9c9327f179963b6982b1853eb50"
            "e7d57b760c190735ccd5835d669b10fb5ac684d3086abb77b5252aff7d2b7f80"
            "8561a7a54af2573e605ecf373e1f3d5525b83dc45bf33a8cc79fd3114c1d4d94"
            "395f0e9611ae3021839f6f81c072ef6b6044e735c5f269a23686f9d566a26782"
            "c12bf5db4660330f123a54d70aa6e55d6293da388a73ecf15f6693cd86dd8352"
            "5003b1cdd22bf5af0bb25ea5ded5c5bff67a06284c9236883eb6aa4b8ea0d94c"
            "588a777b54da4bade065be29ce4d1c1a91d24624562f20cd7e6b4ec25fc0699c"
            "2cc4c815b8c3bd973bb93d0811afd518e7db3c94ef99331a0eab493f88c47f14"
            "c47dde5b647628baa1743fffba43b69fa5a7004ed8b061d0bf599cd7a880d204"
            "85b51c51bd3de82f01123357546eddfdd002223cfb33f23e97b9df42a04379be"
            "4447b2a6c30eaa849e9179e334561b05c83d9a489cc5b4e4ee00c5668a89631c"
            "6cd1b5add22e5fdf680b4755841fb5e1e806b7cc6709d94e3d9fe184388f17f2"
            "6a947d58a95881c73bf7ec078cb3c6c8bee6b48e898da3dade41a871977e54a1"
            "047038edb550b7eadd781888e15d7796940d0999c3104bdebbfbbe716c584f3b"
            "d31326de132ec74bcbd1294f9b6ab57eba429b36c242ef34d36bbaec8d428828"
            "69f26949568a7bbee76b77f54f40002eaa717071e002a8a29dd7fd6ebd7df381"
            "1e090ac3117df4e30e8868b26d4cf4c3437b1a53f14bf515798fe3a5001a7bfc"
            "0a8caeef488175e9d8836a28ba65461462c16ab66c0a8d8148f3b84c0a6a4cba"
            "fa900bc09c4f319f578644ff618d50496d2b2d1e63f8232b263308bb55afcb77"
            "232f210c1677d84df6d9309fc40e551b15458c635b5c3edbf88aceb4973d9fdb"
            "c2750b1fff5f96ac8c54dc83bdbdec3dc01d34e510509377e69eff08ad3d5b12"
            "0c72e8a432e627982b11b6dec534a3423bb529c527637171825bc1990501ee48"
            "0b23711803a4a3c48372fb266759c496ad4d6a56299f7b379a783d07aa30cc45"
            "b1f0094995a5aa0791f4b5309f43295fbb71a20e0bc4addb75589d8e577650b1"
            "109b969f8ffe6f26b957c263f38419bb67e4e651adba049a41fa861772f036c1"
            "72ecf3d8742590996ee4951e608b384c1e6764c1618de6548d239a6325fbed92"
            "33f6e0da4e1775d718a1e5f744b2858f67c585a54c912e7ea58dfb58d1ed2ebb"
            "7149f6f1019e0ec86e64c3e70fba3f0b8462a5401655ecf7386e9f7040098995"
            "fd83be5336c1c9b063458f3a327bd5d5753e73a96fc2f86a2610f18e3fb51731"
            "09c65bb95bb2232785241f472597ba75969369ee893dfeaeee6307256db5a8fd"
            "3294cee178863db9c8dbe711aef2f709da7cc9be00aba6e43266acc4870b69b4"
            "74f3639e5d04c3064ee652fc5ea5afee2d5f7d7e2d1a3a95868c9f2524934ba5"
            "3673cd1e76ea8390f07b9d73bedf84a753b37d8c5d3e64652c9fe6bd238e5433"
            "eaac08ff61ea34c3cfcfb6882485766a2658338a60dac5d934899cad1a05688b"
            "8244e51b29ecfb1c0b000000ed0aea43f9d6715158ff3048e550629bada9ff6c"
            "99b48d9af59f83236ea427401c22d30673117dfd8c17e7caa1c432f72a661c5e"
            "cdac243925674d3b168d33b9f29bda3f42a9180c278f91064af6b79e4a251721"
            "7e457d488e88111c19eaf1aa239215789d94305bd5a975e397af5b5419443803"
            "bb8a7f63c9450c80a96bffcde555370e8c6bb3a0f2d2ffa3e41d00c6ee362d64"
            "fa8afa3ffeea6bd8a964cab8911b768452b297bb3bc7930eb61c5ad38dc7aa31"
            "0c8368131733f4ce4bea67f4ad5b85bbedc01b9fc28afdee1d52d8204d6b3fb8"
            "323b3836a858fdc1cf9e7e7ad6fd1e4e8bf95277824ab90310ae2402c4665cf7"
            "6a478a4726ab63e0ff55ef853e6ed3030d04b66028e7e2b56d12c0fc42aef74d"
            "0a19ca21bc77143b589e5bc8dffeb34ffa0084c67395ec2f3aea8e4c1c1f9644"
            "482f364e8471931422be6eb6562d371f966b11e9e0d2c850537f83992f43de66"
            "9d091b472a5a242731a0156c"
        ),
    },
    {
        "name": "b3_3_quadratic",
        "field": "gf2_128",
        "label": b"sgonal_test_vector_gf2_128",
        "root": "30dafd53c4f2441bb8457cd84fa69b3a822fbda58a46527d5cec8ce1903bc504",
        "sumcheck": (
            "6240c86a95637590efc064be3f0e9d28fc212291b18e5e3afed5099df504c647"
            "8aaa530725347ed936fb115880fe03f394808f716d78e8dd8dde5b5bd3f2f489"
            "a71c546509defd48dfb6650b3095fd6737451138f90326c07013cb02076ecab7"
            "4c74af12fafa59cd8fdf6ae0315d1a5ee40de4c200b7d051bbfb98626e86ccdc"
            "c4f2995317ebb77628e811cb190156e6b9cf8cfb4fc62b478e49e262e6f4453f"
            "6e6c5298fc74b14cd2a9ef3ff9872f67452f9012a79e6517347af882d1e0bd70"
            "113cb1307823bf2e57b45515cfce5e8b0c33e9a941524ba5355f0c444d961383"
            "47da64051e89579e5ee002b8346d1b53c26c695f208d5f5b784f90e4ae33b7bb"
            "e9e0d29e9e2ad103933ab99a684b7611ed1a15977f59e2d60d05a2cf24212ff2"
            "0c59ea4f435404b9fa889934fd8d550807142c664890f7d0a9ba27ea040d03eb"
            "fd4bf8ce06ff90509700bcde7042d213adb43c2fb1f46143226c273b09bd650b"
            "ab9b3aec6cd5419edb1bcd616911c2b3898d07c5faf9fa121da18a01f5a1ea9b"
        ),
        "recording": "upstream/sumcheck_core_gf2_128_b3_3_quadratic.txt",
        "config": (4, 6, 64),
        "nonces": [
            "7ef857289b65bef3539deca0df3f44c67bd0f86b02afddd2eaf2df6b9ba36497",
            "33946263e6da1ec940a9047547a6296f465821313eeb867d988aed265b82eb53",
            "87b402da5412750ec00175350a9579b1f458b668155ba582d31b5d71331f2d41",
            "978ee556b7e529dea3e0fbbde3d83fcb11871c478dd3ddb15fc27e628487950e",
            "1c320449d0bed51ad492d371d066d55c4db059a1c59c267094ae3087746b1e61",
            "c809ce332b7354d1e4b593f335d980dc1f0579e171a0bd092761a12006f3b544",
        ],
        "ligero": (
            "3edfb458a51019d7ab9d3f0890c1c216c1e4e2b2c087cea41515e0dbe8ae74b8"
            "923bc6f7ec3396c391e422f440d9b9f85a2e47a8c43682f41bea847fac6ddaa2"
            "46dab1978ee40772bb75fa4571a773bb3a7e1947eeec8d74b7c42a800a0de3c8"
            "463fcf42223b5204c34bb261d8708e96695648bbb4bd534dd3a852032a5a23c6"
            "41e66955d62f95d2bf6acdc16e401aeb355b55f6c7df1fa5493e152633dd67b0"
            "5451e156baed83c4b6b154e44779cd30d382b43cfb918db00d0f7e6ed000ede9"
            "1460ec372a93c7263f54666cdf2d558e0a56f62914e46eaee62b19e1b5ba179b"
            "b96044de94a5964acc4ff7c175f25be4fed23d1096414f307104eaf47e9c756a"
            "54fbf66e974c607946b689560486601c6d351ce7925a6ffe3d960ace99b9b5fd"
            "bbb2ca9d8b56736af217f21ed813e517fe4f3c78fcafa0b47a01307fef9dc4d2"
            "c9fe979532e97d1452034d904db212ffea8c152cdab17bafd8037d519dabe985"
            "091844be5d630ebba0ba17765839c35543e40162c66ae7b73f9d018c463aaa60"
            "34545321a445e83fb706b03f4971bc2c28d529d36c5440c2942e9c22908e5a2f"
            "2347e19b793e15e0852686e29a2029977b3ba6c346ecf3bceca062b5130ac652"
            "925cbca1da5f99528742bfd37d32710296363d2d2dda271eafe8ffdab7f2c378"
            "fb56de4804e8dfb0887e504f5b3c0a1c040a91e4ed07a35a487be0f1c1221d2d"
            "3950c7db515c5e4c557d2508fc8d13c70efc9f99e667f8a0995b9d2b3f15a3b2"
            "9493a370aa72bece76d5c1614ccac7f8a4427a0cbcf38d7b46249e13ff8a38de"
            "34baf543b88990809ff36271f33a9c62c4d79ddfb271ec6554430c7eff2ddb38"
            "0a11f45d772d5f61d051f6c9a4bf188fad665105add63a91c89f9847ea498fd4"
            "d148fcb439d216593fd6cda35cdd541b70dc213c9ac9f172336743b5d9b9f009"
            "2358436be52d50ba60e7d7c9c4d75415527f4c04647f433b02b7955421a405ed"
            "7ef857289b65bef3539deca0df3f44c67bd0f86b02afddd2eaf2df6b9ba36497"
            "33946263e6da1ec940a9047547a6296f465821313eeb867d988aed265b82eb53"
            "87b402da5412750ec00175350a9579b1f458b668155ba582d31b5d71331f2d41"
            "978ee556b7e529dea3e0fbbde3d83fcb11871c478dd3ddb15fc27e628487950e"
            "1c320449d0bed51ad492d371d066d55c4db059a1c59c267094ae3087746b1e61"
            "c809ce332b7354d1e4b593f335d980dc1f0579e171a0bd092761a12006f3b544"
            "5400000084517983aa1a7acab37c5181b97ddb5d183e7a30b7e9884798a1ad13"
            "33c2c14c61fd3a7d917c0e4537af67339705ac87e322061e9a147d45067342f4"
            "18a655334b4588edccadd095e883e9aaecffd81c02e951c856dc5ec383fb28cc"
            "228ccc269c71ba2bf849a9d61bae28f935d474eb5b163f1bee4bbe0dee075869"
            "b0335e5fe98780182348b1ba71767cc88958065a0403e65c7f95d6de372aced9"
            "4abd8bbd885d0f6d38451210d7fddbb8523ad24204fbd51152f5ac27a948e9e3"
            "788f14e7179ad246b576448614fecb01c2d4dd83ee2f5adbaf7750e986c03086"
            "a13f5be9a5e12e9ff31e8450b0c7623113a70837c5310991f2344e058687333d"
            "18893813a17939ad8bac01008f045c5711e2bfff6b16d4ed928a078e4a55eb72"
            "c65500f6f4ef4d02b4363836cdf4e9c82b761e1824c54d7285c1a5f0b3996af3"
            "088c52df6b9e746c73043aa4262717e733d508761dcac98315686357b39624b9"
            "912a2bb18e692e87b31ad3f26bd3b3246a678f6b9be9272611c21b6fbb1962e1"
            "473c76089d9b039fd9b32adb3a614f9644edd80a7e7d9348c675feee9fdc7231"
            "c50bf481d4b74328bdee990dc0af51f0a9ce68a34340cbf6067d65a1bc5b6406"
            "9e11b8b1a3bbc72f3c5d517befd88b288ca28f8a2adcb8308eda9e97fb4ab325"
            "b567524999b568c401c0d94ea358434d786b2349ad878b197df169e78bbbdb20"
            "08611c7b0ee75ac194c86517ff4e592debce41c3972344dfadc6af0a1c84c1ae"
            "dd5b6b3c0ab3500a12677c73f8c6aaf7f9526ee5020bb01874d32ee0449c6dd8"
            "35282a15dea4fabad0dcf06dea8e7b9e55c9a70686756f1f6db32f01b4509685"
            "21e67614b361c51a3673fb5cf4b313d35b041599d95a54d17de65204a289c04b"
            "33a33f3d15a58a90b90fe9c0d05894f75c48000e8892866e516f605c58466c06"
            "52df4df4245cf61ecb43ce23ac6d64259d89a0c02a156957159feef112d16398"
            "51e0b1b2e97aa138b6b7657ade0eb2df303cba9e4a729e79061ccd89116c56f3"
            "13a082edb0e311185b2820bec856acf95497f23b04be15e7059206f93db9a683"
            "7071bff558f8d7ec8ff91c089b7c3baabbf8a8770741d353cb0541383867b0a9"
            "6dce09199b453bcfeddb8f633797bca30f720faf649c4a67a488ecf4388c5e73"
            "83cf508114629bf0d2bc0692bcb364748b6a728b2607125c74568624affa5174"
            "e400c0c17235340b2e9f56010abaf23e594942196c7ff4d4856d264f5bcb330a"
            "d31030347df134b7f40d68080358488029de0f12d707a15fa0737b04f1c9b3f1"
            "bf8227cf67201ce2b347f47eb14d1377666c472b1a5fd34dc22002183103944f"
            "1e277def38512a4c5dabd0b535d2bd02033df67499240c94b625212b1b57b26d"
            "d82a6b126a9f9d6b92cad7920fa68e4dc4f74ffe46f31c05f2c2b675f6050fd3"
            "3c865c8a03724f9ff9789500b4ddf43ffe7eda857f7670288c27641fb9dc7c63"
            "c8a916920cc7c76f6eb3dc9b083444cfb1d77470290f3b671967030db402ffdb"
            "49fd38f424639cf0aaff985144f29040a3ad1359bddaae36dbba740ee4f0c97b"
            "194dc7d1742827db2f33965e30fa4f37c8217eaddfc34082526df5755b4338db"
            "89e4221b919409fad65d1abf4810ef67183ee40a916de209eead26fa5156116f"
            "9b72440eafde88be86e28a0a04e88fe29e4472b9ccd3a192ae00f6f52baee054"
            "0251869ec728cd03bb2201bcffcf5bc3d9c345d2b14b4f544363cacaf0c088c5"
            "6cb8dc0dc8f126136e1b82c0b7577c8a22b1448c1f588c9f34a1fc5a76986f4b"
            "98a6c4f25a832f48feab33f45e0f48bc9e5a058a0d447d5e0d996b8930d0f824"
            "8a98542f6e74cc99630b559b7c4c1ccc08e0f1b1bc053347822ea65b7a62c871"
            "90fcace20c00000090481e0835d39fd8a96a8621f6b07090b791b96bc168be8b"
            "925875f9651cef09b13b3d19fa1108a15833209497ce19b540a98823b2b717a3"
            "2336eab1c03722b620c9edc47b837e7e9dbcdeacf6e21e6b7c32bb3667017684"
            "860a0f3df8e24aeabb3ccd2f56fa81bf67f1cb75f09fa40b53d4f15f0392430a"
            "00430902b3d88062d100629620fa4365b48a8b1a70d7bfc59766bb8f66746774"
            "cf468ce1c10d2a494e4309fcf32119b14aaf3bb94b30d100410551a0de356601"
            "da0289d1573931745b3d015b150bdf91ed0fa201b77bf13f928b7da499f4b9d8"
            "4ca44d988515ca586768192b8340d3438938f37cd9e78206164622646df66ee8"
            "e9da522c387dbd783dcead20c990b95f5ca3a75a2fded5094377f65585e0b39f"
            "d656856db6f3bbcd74ac6c094e80ac1e7b437b0a45249f7f795e969b2f850669"
            "70895e4bf70c168b2239ed30178e7cde0bb7b317d15f3e632e665cf53e883b8c"
            "d1301635d74c479c1cea5be7574af47527b3fc7fa49563b3a4d1a19eb5935076"
            "25b8ba55cbd4ff01"
        ),
    },
]


class FieldCodec:
    """Serialisation of Section 7.2.1 and the sampler of Section 3.4.3
    for the two fields, over Python integers (bit i = coefficient of x^i
    for GF(2^128), the value for P-256)."""

    def __init__(self, field):
        self.field = field
        self.size = 32 if field == "p256" else 16

    def to_bytes(self, v):
        return v.to_bytes(self.size, "little")

    def from_bytes(self, b):
        v = int.from_bytes(b, "little")
        if self.field == "p256" and v >= P256_P:
            raise ValueError("non-canonical P-256 element")
        return v

    def sample(self, t):
        if self.field == "p256":
            return t.field_elt(P256_P)
        return int.from_bytes(t.bytes(16), "little")

    # Section 7.2.2: the subfield encoding, 2 bytes on the basis for
    # GF(2^128), the field's own for P-256.
    @property
    def sub_size(self):
        return 32 if self.field == "p256" else 2

    def from_subfield_bytes(self, b):
        if self.field == "p256":
            return self.from_bytes(b)
        x = int.from_bytes(b, "little")
        r = 0
        for i in range(16):
            if (x >> i) & 1:
                r ^= GF2_128_BASIS[i]
        return r


# The subfield basis of GF(2^128) (gen_gf2_128_vectors.py,
# UPSTREAM_SUBFIELD_BASIS), for the subfield runs of Section 7.4.
GF2_128_BASIS = [
    0x1,
    0x5c5971877501d4b8f1871e01b64fda4c,
    0x8bb99658eaf2cae0a6e310fb6e176ea8,
    0xb61e08da12f9665c3f8de8a2f9ff7eed,
    0xa76c2e634c6483ae9ba3282087a3f827,
    0x54944ff4a5269cedf7af4e93629f689e,
    0x5439ecfd75a950d8d0765f1873309b88,
    0x49ecdfbe06777b02e566f9fc3d9b58a2,
    0x97a401b733e66a9319af205497f8e2d0,
    0x789fd7793ce7523860e4dbdce9777814,
    0xaa440b2d4b546256c0f157187adbc05b,
    0x79f2cadb70b6115d222f207d0d8ad9f9,
    0xae72af7894ce037df6d1f84fb66c52b8,
    0xd6f226d783d454db4af94ef056d28a30,
    0x057d918d494925fc0f37a0a4d91b4220,
    0x18d4bbb6833c5ae8b683012350e55753,
]


def ligero_geometry(rate_inv, nreq, ncol, nw, nq):
    """LigeroGeometry::new (Section 4.2), as gen_ligero_vectors.py."""
    block = (ncol + 1) // (2 + rate_inv)
    dblock = 2 * block - 1
    wr = block - nreq
    nwrow = (nw + wr - 1) // wr
    nqt = (nq + wr - 1) // wr
    return {"block": block, "dblock": dblock, "wr": wr, "nwrow": nwrow,
            "nqt": nqt, "nrow": 3 + nwrow + 3 * nqt, "leaves": ncol - dblock}


def read_ligero_part(codec, data, geom):
    """Section 7.4, read_ligero_proof of ligero/proof.rs transcribed:
    the four polynomials, the nonces, the run-length coded columns with
    the rules of the section, the path. Returns (polys, nonces,
    columns, path)."""
    pos = 0

    def take(n):
        nonlocal pos
        if pos + n > len(data):
            fail("Ligero part: bytes missing at %d" % pos)
        v = data[pos:pos + n]
        pos += n
        return v

    nreq = geom["nreq"]
    polys = []
    for n in (geom["block"], geom["dblock"], nreq,
              geom["dblock"] - geom["block"]):
        polys.append([codec.from_bytes(take(codec.size)) for _ in range(n)])
    nonces = [take(32) for _ in range(nreq)]
    total = geom["nrow"] * nreq
    cols = []
    subfield_run = False
    zero_runs = 0
    while len(cols) < total:
        runlen = int.from_bytes(take(4), "little")
        if runlen == 0:
            if cols:
                fail("Ligero part: zero-length run not first")
            zero_runs += 1
            if zero_runs > 1:
                fail("Ligero part: repeated zero-length run")
        else:
            zero_runs = 0
        if runlen > 2**25:
            fail("Ligero part: run beyond 2^25")
        for _ in range(runlen):
            if subfield_run:
                cols.append(codec.from_subfield_bytes(take(codec.sub_size)))
            else:
                cols.append(codec.from_bytes(take(codec.size)))
        subfield_run = not subfield_run
    if len(cols) != total:
        fail("Ligero part: %d opened elements, %d expected"
             % (len(cols), total))
    npath = int.from_bytes(take(4), "little")
    path = [take(32) for _ in range(npath)]
    if pos != len(data):
        fail("Ligero part has %d trailing bytes" % (len(data) - pos))
    return polys, nonces, cols, path


def read_recording(path):
    """The tier 3 recording (ADR 0027): the circuit shape, the public
    inputs, the challenges and the padded proof."""
    rec = {"layers": [], "layer_challenges": [], "proof": []}
    for line in path.read_text().splitlines():
        if not line or line.startswith("#"):
            continue
        f = line.split()
        op = f[0]
        if op == "circuit":
            rec["name"] = f[1]
            rec["noutput"], rec["ninput"], rec["npublic"], rec["nl"] = map(
                int, f[2:6])
        elif op == "layer":
            rec["layers"].append({"logw": int(f[2]), "nterms": int(f[4])})
        elif op == "public":
            rec["public"] = [int(x, 16) for x in f[1:]]
        elif op == "g":
            rec["g"] = [int(x, 16) for x in f[1:]]
        elif op == "layer_challenges":
            rec["layer_challenges"].append([int(x, 16) for x in f[2:]])
        elif op == "proof":
            rec["proof"].append([int(x, 16) for x in f[2:]])
        elif op == "alpha_input":
            rec["alpha_input"] = int(f[1], 16)
    return rec


def read_sumcheck_part(codec, data, rec):
    """Section 7.3 into the pad order of Section 6.5, per layer: for
    each round l (P0), r (P0), l (P2), r (P2) become 4 r + 0, + 2, + 1,
    + 3; then the two claims."""
    layers = []
    pos = 0

    def elt():
        nonlocal pos
        v = codec.from_bytes(data[pos:pos + codec.size])
        pos += codec.size
        return v

    for layer in rec["layers"]:
        logw = layer["logw"]
        evals = [0] * (4 * logw + 2)
        for r in range(logw):
            evals[4 * r + 0] = elt()
            evals[4 * r + 2] = elt()
            evals[4 * r + 1] = elt()
            evals[4 * r + 3] = elt()
        evals[4 * logw] = elt()
        evals[4 * logw + 1] = elt()
        layers.append(evals)
    if pos != len(data):
        fail("sumcheck part has %d trailing bytes" % (len(data) - pos))
    return layers


def replay_challenges(codec, label, root, circuit_id, rec, proof):
    """zk/verifier.rs: label, root, statement, then the core's draws."""
    t = Transcript(label)
    t.write_bytes(root)
    t.write_bytes(circuit_id)
    for x in rec["public"]:
        t.write_elt(codec.to_bytes(x))
    t.write_elt(codec.to_bytes(0))
    t.write0(sum(layer["nterms"] for layer in rec["layers"]))
    for _ in range(MAX_LOGW):
        codec.sample(t)
    g = [codec.sample(t) for _ in range(MAX_LOGW)]
    layer_challenges = []
    for layer, evals in zip(rec["layers"], proof):
        alpha = codec.sample(t)
        beta = codec.sample(t)
        ch = [alpha, beta]
        for r in range(layer["logw"]):
            for h in range(2):
                t.write_elt(codec.to_bytes(evals[4 * r + 2 * h]))
                t.write_elt(codec.to_bytes(evals[4 * r + 2 * h + 1]))
                ch.append(codec.sample(t))
        t.write_slice([codec.to_bytes(evals[4 * layer["logw"]]),
                       codec.to_bytes(evals[4 * layer["logw"] + 1])])
        layer_challenges.append(ch)
    alpha_input = codec.sample(t)
    return g, layer_challenges, alpha_input


def check_b3(here):
    for proof in B3_PROOFS:
        rec = read_recording(here / proof["recording"])
        if rec["name"] != proof["name"]:
            fail("recording %s is not %s" % (proof["recording"], proof["name"]))
        codec = FieldCodec(proof["field"])
        data = bytes.fromhex(proof["sumcheck"])
        expected_len = sum(4 * l["logw"] + 2 for l in rec["layers"]) * codec.size
        if len(data) != expected_len:
            fail("%s: sumcheck part is %d bytes, the circuit needs %d"
                 % (proof["name"], len(data), expected_len))
        evals = read_sumcheck_part(codec, data, rec)
        if evals != rec["proof"]:
            fail("%s: the sumcheck part read from the draft differs from the"
                 " recorded padded proof" % proof["name"])
        g, lc, ai = replay_challenges(
            codec, proof["label"], bytes.fromhex(proof["root"]),
            ZERO_CIRCUIT_ID, rec, evals)
        if g != rec["g"]:
            fail("%s: replayed g differs from the recording" % proof["name"])
        if lc != rec["layer_challenges"]:
            fail("%s: replayed layer challenges differ from the recording"
                 % proof["name"])
        if ai != rec["alpha_input"]:
            fail("%s: replayed alpha_input differs from the recording"
                 % proof["name"])
        # Stage 5: the Ligero part parses by the rules of Section 7.4
        # for the geometry of the circuit, with the nonces of B.3.1.
        rate_inv, nreq, ncol = proof["config"]
        nw = (rec["ninput"] - rec["npublic"]
              + sum(4 * l["logw"] + 3 for l in rec["layers"]))
        geom = ligero_geometry(rate_inv, nreq, ncol, nw, len(rec["layers"]))
        geom["nreq"] = nreq
        polys, nonces, cols, path = read_ligero_part(
            codec, bytes.fromhex(proof["ligero"]), geom)
        if [n.hex() for n in nonces] != proof["nonces"]:
            fail("%s: the nonces read differ from B.3.1" % proof["name"])
        if len(path) > 2 * geom["leaves"]:
            fail("%s: path longer than the tree" % proof["name"])


def write_zk_proofs(out):
    for proof in B3_PROOFS:
        lines = [
            "# The Appendix B.3.%d proof of IETF draft-google-cfrg-libzk-03,"
            % (2 if proof["field"] == "p256" else 3),
            "# Longfellow ZK stage 4: label, root, circuit identifier and the",
            "# sumcheck part of the complete proof serialisation (Sections 7.3",
            "# and 7.5), for the replay of sumcheck_kat against the tier 3",
            "# recording of the same circuit (ADR 0032).",
            "# Generated by gen_transcript_vectors.py (this directory); do not"
            " edit by hand.",
            "# Stage 5 (ADR 0040): the configuration and the Ligero part",
            "# (Section 7.4), the bytes that follow the sumcheck part, and",
            "# the Merkle nonces listed in Appendix B.3.1.",
            "# Lines:",
            "#   zk_proof <circuit> <label> <root> <circuit identifier>",
            "#   zk_sumcheck <circuit> <bytes>",
            "#   zk_ligero <circuit> <rate_inv> <nreq> <ncol> <bytes>",
            "#   zk_nonce <circuit> <k> <32 bytes>",
            "# all byte strings as hex in memory order; the label is the",
            "# ASCII string of the upstream unit test, the identifier its 32",
            "# zero bytes.",
            "#",
            "field " + proof["field"],
            "zk_proof %s %s %s %s" % (proof["name"], proof["label"].hex(),
                                      proof["root"], ZERO_CIRCUIT_ID.hex()),
            "zk_sumcheck %s %s" % (proof["name"], proof["sumcheck"]),
            "zk_ligero %s %d %d %d %s" % ((proof["name"],) + proof["config"]
                                           + (proof["ligero"],)),
        ] + ["zk_nonce %s %d %s" % (proof["name"], k, n)
             for k, n in enumerate(proof["nonces"])]
        (out / ("zk_proof_%s_%s.txt" % (proof["field"], proof["name"][:4]))
         ).write_text("\n".join(lines) + "\n")


# ----------------------------------------------------------------------
# The cases: copied constants
# ----------------------------------------------------------------------

# (source, message, digest)
SHA256_CASES = [
    ("FIPS 180-4, empty message", b"",
     "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
    ("FIPS 180-4 example, one block", b"abc",
     "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
    ("FIPS 180-4 example, two blocks (448 bits)",
     b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
     "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
    ("FIPS 180-4 example, 896 bits",
     b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn"
     b"hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
     "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"),
    ("CAVP SHA256ShortMsg, Len = 8", bytes.fromhex("bd"),
     "68325720aabd7c82f30f554b313d0570c95accbb7dc4b5aae11204c08ffe732b"),
    ("CAVP SHA256ShortMsg, Len = 16", bytes.fromhex("5fd4"),
     "7c4fbf484498d21b487b9d61de8914b2eadaf2698712936d47c3ada2558f6788"),
    ("CAVP SHA256ShortMsg, Len = 24", bytes.fromhex("b0bd69"),
     "4096804221093ddccfbf46831490ea63e9e99414858f8d75ff7f642c7ca61803"),
    ("CAVP SHA256ShortMsg, Len = 32", bytes.fromhex("c98c8e55"),
     "7abc22c0ae5af26ce93dbb94433a0e0b2e119d014f8e7f65bd56c61ccccd9504"),
]

FIPS197_C3_KEY = "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"
SP800_38A_F55_KEY = (
    "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4"
)

# (source, key, block, ciphertext)
AES256_CASES = [
    ("FIPS 197 Appendix C.3", FIPS197_C3_KEY,
     "00112233445566778899aabbccddeeff",
     "8ea2b7ca516745bfeafc49904b496089"),
    ("SP 800-38A F.5.5 CTR-AES256, counter block 1", SP800_38A_F55_KEY,
     "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff",
     "0bdf7df1591716335e9a8b15c860c502"),
    ("SP 800-38A F.5.5 CTR-AES256, counter block 2", SP800_38A_F55_KEY,
     "f0f1f2f3f4f5f6f7f8f9fafbfcfdff00",
     "5a6e699d536119065433863c8f657b94"),
    ("SP 800-38A F.5.5 CTR-AES256, counter block 3", SP800_38A_F55_KEY,
     "f0f1f2f3f4f5f6f7f8f9fafbfcfdff01",
     "1bc12c9c01610d5d0d8bd6a3378eca62"),
    ("SP 800-38A F.5.5 CTR-AES256, counter block 4", SP800_38A_F55_KEY,
     "f0f1f2f3f4f5f6f7f8f9fafbfcfdff02",
     "2956e1c8693536b1bee99c73a31576b6"),
]


def fail(msg):
    print("gen_transcript_vectors: " + msg, file=sys.stderr)
    sys.exit(1)


def check_cases():
    for source, msg, digest in SHA256_CASES:
        got = hashlib.sha256(msg).hexdigest()
        if got != digest:
            fail("SHA-256 mismatch on " + source + ": " + got)
    for source, key, block, ct in AES256_CASES:
        got = aes256_encrypt(bytes.fromhex(key), bytes.fromhex(block)).hex()
        if got != ct:
            fail("AES-256 mismatch on " + source + ": " + got)


# ----------------------------------------------------------------------
# Output
# ----------------------------------------------------------------------


def write_sha256(path):
    lines = [
        "# Known-answer vectors for SHA-256 (FIPS 180-4), Longfellow ZK"
        " stage 4.",
        "# Generated by gen_transcript_vectors.py (this directory); do not"
        " edit by hand.",
        "#",
        "# The cases are copied constants: the FIPS 180-4 examples and CAVP",
        "# SHA256ShortMsg cases, recomputed by the generator with hashlib,",
        "# which aborts on any mismatch (ADR 0029, ADR 0032).",
        "# Format: one case per line:  sha256 <message> <digest>",
        "#   message as hex bytes, '-' for the empty message; digest as",
        "#   64 hex digits, the 32 bytes of the digest in order.",
        "#",
    ]
    for source, msg, digest in SHA256_CASES:
        lines.append("# " + source)
        lines.append("sha256 " + (msg.hex() if msg else "-") + " " + digest)
    path.write_text("\n".join(lines) + "\n")


def write_aes256(path):
    lines = [
        "# Known-answer vectors for AES-256 single-block encryption"
        " (FIPS 197),",
        "# Longfellow ZK stage 4.",
        "# Generated by gen_transcript_vectors.py (this directory); do not"
        " edit by hand.",
        "#",
        "# The cases are copied constants: FIPS 197 Appendix C.3 and the",
        "# counter blocks of NIST SP 800-38A Appendix F.5.5 (CTR-AES256),",
        "# each as a single-block encryption. The generator recomputes them",
        "# with its own AES-256 and aborts on any mismatch (ADR 0029,",
        "# ADR 0032). The counter layout of the transcript's FsPrf (little-",
        "# endian from zero) is the draft's and is anchored by Appendix B.2,",
        "# not by these cases.",
        "# Format: one case per line:  aes256 <key> <block> <ciphertext>",
        "#   key as 64 hex digits, block and ciphertext as 32, bytes in"
        " order.",
        "#",
    ]
    for source, key, block, ct in AES256_CASES:
        lines.append("# " + source)
        lines.append("aes256 " + key + " " + block + " " + ct)
    path.write_text("\n".join(lines) + "\n")


def write_transcript_fs(path, script):
    lines = [
        "# Fiat-Shamir transcript vectors, IETF draft-google-cfrg-libzk-03",
        "# Appendix B.2 (B.2.1 to B.2.5), Longfellow ZK stage 4.",
        "# Generated by gen_transcript_vectors.py (this directory); do not"
        " edit by hand.",
        "#",
        "# One chained run: the harness executes the lines in order on the",
        "# library's transcript, state carried from line to line. The",
        "# generator reproduced every value below with its own transcript",
        "# before writing them (ADR 0032).",
        "# Lines:",
        "#   reset <label>            a new transcript from the label (hex)",
        "#   write_bytes <bytes>      the byte array frame",
        "#   write_elt <bytes>        the element frame, serialised element",
        "#   write_slice <n> <bytes>  the array frame, n elements"
        " concatenated",
        "#   elt <value>              draw one element of the 4-word prime",
        "#                            field of B.2 (p = 2^256 - 2^32 - 977):",
        "#                            32 bytes little-endian, rejected at or",
        "#                            above p; value as printed in the draft,",
        "#                            the big-endian integer, 64 hex digits",
        "#   nat <n> <result>         nat (n)",
        "#   choose <n> <k> <list>    choose (n, k), comma-separated",
        "# Elements are written as 32 bytes little-endian (Section 7.2.1).",
        "#",
    ]
    path.write_text("\n".join(lines + script) + "\n")


def main():
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).parent
    out.mkdir(parents=True, exist_ok=True)
    check_cases()
    script = b2_script()
    check_b3(Path(__file__).parent)
    write_sha256(out / "sha256.txt")
    write_aes256(out / "aes256.txt")
    write_transcript_fs(out / "transcript_fs.txt", script)
    write_zk_proofs(out)
    print(
        "gen_transcript_vectors: %d sha256, %d aes256 and %d B.2 cases"
        " written to %s"
        % (len(SHA256_CASES), len(AES256_CASES),
           sum(1 for l in script if l.split()[0] in ("elt", "nat", "choose")),
           out)
    )


if __name__ == "__main__":
    main()
