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
# serialisation of B.3.2 (B.3.3).
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
            "# Lines:",
            "#   zk_proof <circuit> <label> <root> <circuit identifier>",
            "#   zk_sumcheck <circuit> <bytes>",
            "# all byte strings as hex in memory order; the label is the",
            "# ASCII string of the upstream unit test, the identifier its 32",
            "# zero bytes.",
            "#",
            "field " + proof["field"],
            "zk_proof %s %s %s %s" % (proof["name"], proof["label"].hex(),
                                      proof["root"], ZERO_CIRCUIT_ID.hex()),
            "zk_sumcheck %s %s" % (proof["name"], proof["sumcheck"]),
        ]
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
