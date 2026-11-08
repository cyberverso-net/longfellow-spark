# Chapter 9: the mDoc layer and the proof of age

This chapter covers block 5 of Phase D ([ADR 0058](../adr/0058-mdoc-layer.md), issue #65): the layer that turns two Longfellow proofs into one mDoc proof of age in the format of upstream's `applications/mdoc_zk`, made by this project from upstream's witness files and accepted by upstream's verifier, and the symmetric verifier, which accepts upstream's example proofs. Block 6 (#66) will build the witnesses from the credential itself; Section 1.6 and Section 3.4 say what that leaves out of this chapter. The audience is the one of [ADR 0081](../adr/0081-audience-certification-evaluators.md): nothing here assumes a background in cryptography or in SPARK, and every step that an evaluator must follow is spelled out.

## 1. The construction

### 1.1 What an mDoc proof of age states

An mDoc is a mobile credential in the format of ISO 18013-5: a document, such as a driving licence, whose data elements are signed by an issuer and bound to a key held by the holder's device. A relying party, a website that must check that its visitor is an adult, asks the holder to show one attribute, `age_over_18`, and nothing else. Showing the signed document would reveal everything in it. A zero-knowledge proof shows only that the document, signed by a known issuer and bound to a key the device just used, carries that attribute with the requested value, and that it is valid at the date the relying party gives.

Upstream proves this with two circuits over two fields, because the two halves of the work live naturally in different arithmetic:

- The **hash circuit**, over GF(2^128), reads the bytes of the signed part of the document (the mobile security object, MSO), computes its SHA-256 digest, checks that the requested attribute, as an issuer-signed item, hashes to one of the digests the MSO lists, checks the validity dates against the date `now`, and reads the device key the MSO carries. Hashing is bit arithmetic, which a binary field expresses cheaply.
- The **signature circuit**, over P-256, verifies two ECDSA signatures on the curve P-256: the issuer's signature on the MSO digest under the issuer's public key, and the device's signature on the session transcript under the device key. Elliptic-curve arithmetic lives in the prime field of the curve.

Each circuit is proved with the prover of chapter 7 and checked with the verifier of chapter 5. What the layer adds is the glue that makes the two proofs one statement about one credential: the tags that bind the values the two circuits share (Section 1.3), the public inputs of each circuit built from the relying party's data (Section 1.4), one Fiat-Shamir transcript across the two proofs (Section 1.4), and the proof format (Section 1.5).

The relying party's data, what the verifier knows and the holder does not choose: the issuer's public key as two coordinates; the session transcript, the CBOR structure of ISO 18013-5 that carries the relying party's nonce; the requested attribute, its identifier and the value asked for; the date `now`; and the document type.

### 1.2 The production circuits

Upstream ships its circuits as archives, one per circuit version and number of attributes, each holding the two circuits and named by a combined identifier, SHA-256 of the signature circuit's identifier followed by the hash circuit's. Its table of specifications (`runtime/src/zk_spec.rs`, `ZK_SPECS` and `CURRENT_ZK_SPECS` at d5e6be7) names, for each archive, the version, the number of attributes and the Ligero configuration of each circuit (the inverse rate, the number of queries, the number of columns):

| Version | Attributes | Archive (first bytes) | Hash circuit | Signature circuit |
|---|---|---|---|---|
| 7 | 1 | `8d079211` | 7, 132, 4151 | 7, 132, 4096 |
| 7 | 2 | `6a581068` | 7, 132, 4265 | 7, 132, 4096 |
| 7 | 3 | `8ee4849a` | 7, 132, 4307 | 7, 132, 4096 |
| 7 | 4 | `5aebdaaa` | 7, 132, 4415 | 7, 132, 4096 |
| 6 | 1 | `137e5a75` | 4, 128, 4096 | 4, 128, 2945 |
| 6 | 2 | `b4bb6f01` | 4, 128, 4025 | 4, 128, 2945 |
| 6 | 3 | `b2211223` | 4, 128, 4121 | 4, 128, 2945 |
| 6 | 4 | `c70b5f44` | 4, 128, 4283 | 4, 128, 2945 |
| 5 | 1 | `f88a39e5` | 4, 128, 4096 | 4, 128, 2945 |
| 5 | 2 | `f51b7248` | 4, 128, 4025 | 4, 128, 2945 |
| 5 | 3 | `c27195e0` | 4, 128, 4121 | 4, 128, 2945 |
| 5 | 4 | `fa5fadfb` | 4, 128, 4283 | 4, 128, 2945 |
| 8 | 1 to 4 | `5a893815`, `ea4c66ad`, `e43e7404`, `c73b6342` | 7, 132, 5255 or 5246 | 7, 132, 4445 |

This project holds the first row and the fifth ([ADR 0055](../adr/0055-phase-d-scope-mdoc-scale.md), [ADR 0059](../adr/0059-mdoc-vectors-and-measurement.md)): the version 7 and the version 6 archive with one attribute, whose circuits, example proofs and witness files are pinned under `tests/vectors/upstream/mdoc/`. The signature circuit is the same in both (identifier `2845210a...`); the hash circuits differ. Versions 5 to 7 share the legacy layout of the tags and the public inputs described below; version 8 has another layout and no archive at d5e6be7, so it is not in the project. The table is `Mdoc_Spec` (Section 3.1), two rows.

### 1.3 The tags that bind the two proofs

Three values appear in both circuits: the digest of the MSO that the issuer signed, and the two coordinates of the device key. The hash circuit computes or reads them from the document; the signature circuit verifies signatures under them. They are secret, parts of the credential, so they cannot be public inputs. Without a link, a dishonest holder could prove the hash circuit on one credential and the signature circuit on another.

The link is a message authentication code, a MAC, of a particular simple kind. For each 256-bit value m, split in two halves m0 and m1 of 128 bits, each read as an element of GF(2^128), the prover computes

    tag0 = (av + ap0) * m0,    tag1 = (av + ap1) * m1

where ap0 and ap1 are one-time pads the prover draws at random for this proof (together, the three pairs are `mac_ap`), and av is a challenge drawn from the transcript after both commitments. The six tags are public inputs of both circuits; each circuit holds its own copy of the value and of the pads in its witness, and checks the equation. If both proofs are accepted, both circuits spoke of values with the same tags under the same pads and the same challenge, which for a field is the same values. And the tag hides m when m is not zero: it is m multiplied by av + ap, a field element the verifier cannot predict since ap is a fresh uniform pad, and the product of a non-zero element by a uniform one is uniform. The construction has one limit, which upstream's has too: a zero half gives a zero tag whatever the pad, so a tag tells a zero half from a non-zero one (and a non-zero half gives a zero tag only when av + ap is zero, with probability 2^-128). The three values are a SHA-256 digest and the two coordinates of a point on P-256; a zero half of any of them does not occur in practice, and the layer does not check for it, as upstream does not.

The order matters. If av were known before the commitments, a prover could pick two different values and two pads that give the same tags. Since av is drawn from the transcript after both roots are written, the values and the pads are fixed before av exists, and the pair of commitments has one chance in 2^128 of colliding. This is why the two phases of [ADR 0085](../adr/0085-prover-and-verifier-in-two-phases.md) were needed: both commitments before either statement.

This is the legacy form of versions 5 to 7 (`runtime/src/mac.rs`, `push_legacy_macs`). The three values, in order, are the issuer's signature digest and the x and y coordinates of the device key, each written as 32 little-endian bytes; m0 is bytes 0 to 15 and m1 bytes 16 to 31, with the little-endian convention of `GF2_128.From_Bytes` (chapter 1); av and the pads are field elements by their 128-bit value. The modern form of version 8 is different and not in the project. In Ada this is `Mdoc_Mac.Legacy_Tags`, Gold on the six products (Section 3.1).

### 1.4 The public inputs and the transcript

A circuit takes its inputs as field elements, one per wire, the public ones first. Upstream's builders (`runtime/src/concrete/legacy/public.rs`) push one element per bit for everything that is "bits", least significant bit first, as the element One or Zero; one element per 128-bit value for the tags and av; and field elements as they are for the issuer's key and the digest.

**The hash circuit**, over GF(2^128), for one attribute:

| Piece | Elements | Version 7 | Versions 5 and 6 |
|---|---|---|---|
| the constant one | 1 | the element One (OneWire, [ADR 0064](../adr/0064-lean-circuit-premises.md)) | the same |
| the attribute | 784 or 776 | the CBOR text string of the identifier as bits, zero bits to 32 bytes (256); the CBOR value as bits, zero bits to 64 bytes (512); two lengths of 8 bits, 1 + 17 + 1 + id_len and value_len + 12 + 1, the framing of `elementIdentifier` and `elementValue` in the issuer-signed item | one buffer: the CBOR text of the identifier, the CBOR text `elementValue`, the value, as bits, zero bits to 96 bytes (768); its length, 8 bits |
| the date now | 160 | the 20 bytes of `YYYY-MM-DDThh:mm:ssZ` as bits; a shorter date is padded with the element 2, which no bit can equal | the same |
| the six tags | 6 | one element each | the same |
| av | 1 | one element | the same |

952 elements at version 7, 944 at version 6; with n attributes, 1 + 784 n + 167 and 1 + 776 n + 167. The verifier compares the count with the circuit's (`AttributeNumberMismatch` upstream, `Input_Count` here): a request with the wrong number of attributes for the archive is refused before any work.

**The signature circuit**, over P-256, 900 elements: the constant one; the issuer's public key as two field elements; e2, the digest the device signed, as one field element; the six tags as 128 bits each (768); av as 128 bits.

**e2** is SHA-256 of the COSE `Sig_structure` of the ISO 18013-5 `DeviceAuthentication`, built from the session transcript and the document type with fixed CBOR headers (`circuits/src/cbor/mdoc.rs`, `compute_transcript_hash`); the header of `Device_Auth` lists the bytes. The device signed exactly this structure when it answered the relying party, so the signature circuit's check of the device signature on e2 ties the proof to this session. For versions below 8 the document type reaches the circuit only through e2, as upstream's verifier notes.

**The transcript.** Upstream opens the Fiat-Shamir transcript of chapter 4 from the session transcript bytes (`Transcript::new (transcript)`, here `Transcript.Reset` with those bytes as the label: one byte-string frame, no label of its own), and the two proofs share it. In order, the transcript absorbs the session transcript, the root of the hash commitment, the root of the signature commitment; av is drawn, 16 bytes read as a little-endian 128-bit value; then the statement of the hash proof (its circuit identifier, its shape, its public inputs), its sumcheck and Ligero proof, the statement of the signature proof and its proofs. The verifier replays the same sequence from the proof bytes.

### 1.5 The proof format

One byte string (`runtime/src/proto.rs`, `MdocProof::write`): the six tags, each as its 128-bit value in 16 little-endian bytes (96 bytes); then the proof of the hash circuit, the proof string of draft Section 7.5 that chapter 7's writers produce; then the proof of the signature circuit; nothing after. The length of the hash proof is not written: the reader learns it by reading the proof under the geometry of its circuit, and the signature proof starts there. For the version 7 pair the whole is about 360 kB (161 kB and 199 kB for the two proofs), for the version 6 pair about 325 kB.

### 1.6 The witness

The witness of each circuit is its private inputs: for the hash circuit, the bytes of the MSO and of the issuer-signed item with the intermediate values of their SHA-256, the offsets of the fields inside them, the three values the tags bind as bits, and `mac_ap`; for the signature circuit, the ECDSA witnesses of the two signatures, and `mac_ap` again. Building it from the credential is block 6: the CBOR parse of the document, the SHA-256 trace, the attribute positions, the ECDSA witnesses, the drawing of `mac_ap` from the randomness source.

In this block the witnesses come from upstream's two witness files per archive (ADR 0059): the circuit's inputs as little-endian field elements, public ones first, 16 bytes each for the hash circuit and 32 for the signature circuit. The layer reads two things from the ends of the hash circuit's private part (`Mdoc_Inputs.Witness_Parts`): the three messages, its first 768 elements as bits, and `mac_ap`, its last six elements, since upstream's builder pushes the messages first and the pads last (`legacy/private.rs`, `push_witness_hash`). The pads are one-time: two proofs under the same pads with different challenges av and av' give the bound value away, since tag + tag' = (av + av') m. Upstream's example proof of each archive was made under the pads its witness files hold, so a proof made with those same pads would leak the MSO digest and the device key of the test credential. The prover of this block therefore draws fresh pads from its randomness source and places them in both witnesses before committing (`Mdoc_Inputs.Place_Pads`): in the hash witness as its last six elements, in the signature witness at the end, where upstream's builder encodes each 128-bit pad as 64 elements of two bits, the element 2 v - 3 of the pair v (`push_plucked_128_legacy`); `Sig_Pads_Match` first checks that the file's pads are where the layout says. So the proof of this block is made from upstream's witnesses with this project's pads, tags and av.

## 2. The algorithms

### 2.1 Upstream's prover step by step

`run_mdoc_prover_inner` (`runtime/src/prover.rs` at d5e6be7), for a specification, the archive, the credential, the issuer's key, the session transcript, the attributes, the date and the document type, and what this project does at each step:

| Step | Upstream | This project |
|---|---|---|
| 1 | Checks the version, that the attributes share one namespace, and for version 8 only the CBOR values. | The version is the row's; one attribute per request in the archives held; the layout check of `Mdoc_Inputs.Fits` (Section 3.1). |
| 2 | Parses the key's coordinates as P-256 elements. | `Mdoc_Cli.Coordinate`: hex, below p. |
| 3 | Draws `mac_ap` from the randomness source. | Drawn from the randomness source (`Cli_Random`, `--seed` for a reproducible proof) and placed in both witnesses in place of the file's (Section 1.6). |
| 4 | Opens the transcript from the session transcript. | `Transcript.Reset (Session)`. |
| 5 | Decompresses the archive into the two circuits. | The LFC2 payloads are pinned and loaded in their packed form (chapter 6, [ADR 0074](../adr/0074-circuit-identifier-checked-once.md)); their identifiers are checked against the row and combined (Section 3.3). |
| 6, 7 | Parses the credential and builds the two witnesses. | Block 6; here the witness files. |
| 8 | Commits the hash circuit: pads, witness vector, tableau, Merkle tree, the root to the transcript. | `Zk_Prover.Commit` of the GF(2^128) chain (ADR 0085). |
| 9 | Commits the signature circuit the same way. | `Zk_Prover.Commit` of the P-256 chain. |
| 10 | Draws av, 16 bytes little-endian. | `Transcript.Get_Random_Bytes`, `GF2_128.From_Bytes`. |
| 11 | The six tags. | `Mdoc_Mac.Legacy_Tags`. |
| 12 | The public inputs of both circuits. | `Mdoc_Inputs.Hash_Inputs`, `Device_Auth.Digest`, `Mdoc_Inputs.Sig_Inputs`. |
| 13 | Proves the hash circuit: the statement, the sumcheck, the Ligero proof. | `Zk_Prover.Prove_Committed`. |
| 14 | Proves the signature circuit. | The same on the P-256 chain. |
| 15 | Writes the proof: the tags, the two proofs. | `Mdoc_Proof.Write_Tags`, the two proofs copied after it. |

The checks that need no transcript come first in `Mdoc_Prover.Prove`: the bound on the session transcript, the attributes against the version's layout, the counts of the public inputs against the circuits'. `Not_Satisfied`, which needs the public inputs, is found in step 13 or 14, as upstream finds it (ADR 0085).

### 2.2 The witness files as inputs

Upstream does not record which credential and which request its artifacts were made from. Before any code, the block settled it by reading the public parts of the files against the layout of Section 1.4: the first 952 elements of the version 7 hash witness, the first 944 of the version 6 one, and the first 900 of the signature witnesses. They decode to the attribute `family_name` with the CBOR text value `"Mustermann"` (`6a 4d75737465726d616e6e`), the date `2024-10-01T09:00:00Z`, the document type `org.iso.18013.5.1.mDL`, and, in the signature witness, an issuer key and an e2 that match exactly one family of upstream's test cases (`testcases/src/vectors.rs`, the cases named `..._MDOC_3`, which share a credential, a key and a 143-byte session transcript; `FAMILYNAME_MUSTERMANN_MDOC_3` names the attribute). The six tags in the hash witness equal the first 96 bytes of the example proof of the same archive, and av, re-derived from the two roots of that proof under the test case's transcript, equals the last public element. So the witness files and the example proof of each archive are one run of upstream's prover on that case, and the test case of this block is that one: not the AV profile's example attribute `age_over_18`, which upstream's `TEST_DATA` credential carries but which these files were not made from.

The check is permanent: `gen_mdoc_layer_vectors.py` rebuilds the public parts of all three files from the case's parameters with its own transcription of the builders, recomputes the tags from the ends of the witness, and fails unless everything agrees byte for byte; `mdoc_kat` then rebuilds them in Ada (Section 5). The parameters are in that generator, in `scripts/measure-mdoc.sh` and in `tests/vectors/upstream/README.md`.

### 2.3 The verifier side

`run_mdoc_verifier_inner` (`runtime/src/verifier.rs`): the same checks; the two circuits and their geometries; the proof read (the tags, then each proof by its geometry; nothing may remain); the transcript opened from the session transcript; both commitments received, that is, both roots written; av drawn; the public inputs of the hash circuit rebuilt from the request and checked for their count; the hash proof verified; the key parsed and e2 computed; the public inputs of the signature circuit rebuilt; the signature proof verified. `Mdoc_Verifier.Verify` follows it with `Zk_Verifier.Receive` and `Verify_Received` (ADR 0085), with the count checks first.

What the verifier does not do, and the relying party does outside the proof: trust the issuer's key (a trust list), check the freshness of the nonce inside the session transcript, choose `now`; and what the circuits compute is trusted (Section 6).

## 3. The Ada/SPARK implementation

### 3.1 The units of the layer

Seven packages in `src/`, each with its header stating what is proved, tested and trusted:

- **`Cbor_Encode`**: the head of a CBOR text or byte string of n bytes, one to five bytes by the cases of the standard. `Head_Len` is the length, `Head` the bytes, Gold: the postcondition states every byte.
- **`Mdoc_Mac`**: the types of the tags (`Pads` is `mac_ap`, three pairs of elements; `Messages` three 32-byte values; `Tags` six elements) and `Legacy_Tags`, Gold on the six products of Section 1.3, stated with the field's `Mul` and `Add` and a function `Half` that names the element of each half. The loop that computes them carries an invariant over the tags done so far, the usual way of proving a loop in SPARK: what holds before each turn and is kept by it holds after the last.
- **`Device_Auth`**: `Digest`, e2 from the session transcript and the document type, Silver. It feeds SHA-256 piece by piece, so no buffer of the whole structure is needed; the header lists the bytes in the order they reach the hash. It also holds the two bounds the layer imposes: `Max_Session_Transcript`, 65,000 bytes, which upstream's pull request 223 proposes for its C++ entry point (not merged at d5e6be7; to be re-read with issue #122), and `Max_Doc_Type`, 65,535 bytes, the longest a CBOR head of three bytes carries, where upstream takes any length: a bound for the proofs of the lengths, far above any document type of ISO 18013-5.
- **`Mdoc_Inputs`**: the request types (an `Attribute` is an identifier of up to 64 bytes and a value of up to 96, each a fixed buffer with its length, since SPARK records cannot hold strings of varying size; `Attribute_List` up to four of them), `Fits` and `All_Fit` (the pieces fit the version's buffers), `Hash_Count` (the closed formula of Section 1.4, Gold by definition), `Hash_Inputs` and `Sig_Inputs` (Silver, with Gold on the counts and on the positions of the constant one, the key, e2, the tags and av), and `Witness_Parts`, `Sig_Pads_Match` and `Place_Pads` (Section 1.6; `Place_Pads` is Gold on where it puts the pads). The builders push one element at a time through small procedures (`Push_Bits`, `Push_Bytes`, `Push_Pad`, `Push_Attribute`), each with a postcondition on how far the position moved, so that the proof of the count is a sum of fixed numbers.
- **`Mdoc_Spec`**: the two rows of Section 1.2 (`Specification`: version, attributes, the combined identifier, the two circuit identifiers, the two configurations), `Lookup` by combined identifier, and `Combined_Of`, SHA-256 of the two identifiers.
- **`Mdoc_Proof`**: the fixed part of the format, `Write_Tags` and `Read_Tags` at the front of the proof, Gold on the bytes; the offset `Hash_First`, 96.
- **`Mdoc_Status`**: the layer's statuses. `Ok`; `Transcript_Too_Long`; `Attribute_Invalid` (an attribute does not fit the layout); `Input_Count` (the public inputs built are not as many as the circuit has); `E2_Not_In_Field` (the digest is not below p, where upstream's builder panics); `Hash_Failed` and `Sig_Failed`, with the status of the failing prover or verifier beside them, since the layer drives two of each.

### 3.2 `Mdoc_Prover` and `Mdoc_Verifier`

`Mdoc_Prover` is generic over the two prover chains, one per field, so that the library instance with the test source (`Mdoc_Prover_Lib`, `Simple_Rng`) is proved and the command line instantiates it again with the operating system's source (`Mdoc_Prover_Cli`), exactly as `Zk_Prover` is handled in chapter 7. Its formal packages name their actuals where they can (`Ligero_Verifier_GF2_128`, `Packed_HQuad_GF2_128`), so that the element types of the two chains are known inside the generic to be those of the two fields: the tags are GF(2^128) elements and the signature circuit's inputs P-256 elements, and the compiler checks it. `Mdoc_Verifier` needs no generic: the two verifier chains have no randomness, and the library's instances are the only ones.

`Prove` takes the version, the two circuits with their identifiers, subfield boundaries and configurations (a small record `Circuit_Info`), the two private input arrays, `mac_ap` and the three messages, the issuer's key, the session transcript, the attributes, the date and the document type, and fills a buffer of `Max_Len` bytes, the tags plus the two proofs at their longest. The body is Section 2.1: the three checks, `Transcript.Reset`, two `Commit`, the draw of av, the tags, the public inputs, `Write_Tags`, two `Prove_Committed`. Each `Prove_Committed` writes into a heap buffer of exactly its own `Max_Proof_Len` bytes, which its precondition requires, and the bytes are copied into place; the two `Committed` records are released on every path that does not consume them, which the ownership checks of [ADR 0047](../adr/0047-heap-allocation-by-ownership.md) enforce. The postcondition states the statuses: on `Ok` the proof is at least the tags and one byte of each proof; otherwise the length is zero, and the detail status is set exactly when one prover failed.

`Verify` takes the version, the two circuits with identifiers and configurations, the request and the proof bytes: the three checks, the tags read, `Transcript.Reset`, `Receive` at offset 96 and `Receive` at the offset after the hash proof, the check that the second proof ends where the buffer ends, av, the hash circuit's inputs and `Verify_Received`, e2 and the signature circuit's inputs and `Verify_Received`. Both procedures take the executable part of the loader's postcondition on each circuit as a precondition, as `Zk_Prover.Prove` and `Zk_Verifier.Verify` do ([ADR 0072](../adr/0072-predicate-checks-in-the-prover-instances.md)), and the rest at level `Proof_Only`.

### 3.3 `longfellow_prove_mdoc` and `longfellow_verify_mdoc`

Two programs in `cli/`, outside SPARK like the other two, sharing `Mdoc_Cli`: the command line, the files, the hex, and the loading of the two circuits of a specification. `--spec` names an archive by its combined identifier; the LFC2 payloads are read from `--circuits DIR` (default `tests/vectors/upstream/mdoc/`), loaded in their packed form through `Pinned_Circuits`, and refused with `combined_hash` unless their identifiers are the row's and combine to the archive's name: one identified profile, selected and checked, the first step of what issue #79 asks for. The request is `--pkx` and `--pky`, `--transcript HEX` or `--transcript-file`, `--now`, `--doc-type`, and `--attr ID:CBORHEX`, repeatable. The prover also takes the two witness files and `--out`, and `--seed` for a reproducible proof (the fresh pads and the prover's own draws then come from `Simple_Rng`); the verifier `--proof`. The programs check the executable preconditions of the library before each call (the lengths, the circuits, the configurations), and print the layer's status with the inner one beside it: `hash_failed not_satisfied`, say, or `ok`.

The session transcript above 65,000 bytes is refused by the programs with `transcript_too_long` and by the library with the status of the same name.

### 3.4 Witness generation (block 6)

Not in this block: the CBOR parse of the credential, the SHA-256 trace of the MSO, the attribute positions, the ECDSA witnesses, the device key, the drawing of `mac_ap`. The constant-time account of the parse, which depends on the data and where the data is the secret, is ADR 0058's at block 6. What this block adds to the constant-time discipline of [ADR 0051](../adr/0051-constant-time-in-the-prover.md) is small: the tags multiply the secret messages and pads by the field's constant-time product; `Witness_Parts`, `Sig_Pads_Match` and `Place_Pads` index on constants and accumulate their layout checks over every element without a short circuit, in masks, for the bits and for the 384 element comparisons of the pads (the limbs xor-ed and or-ed, no record equality), with one branch at the end on the result, as [ADR 0051](../adr/0051-constant-time-in-the-prover.md) admits for the prover's own checks; the public inputs, av, the tags and the proof are public.

## 4. What the proofs guarantee

For every input that meets the preconditions, GNATprove proves of the units of the partition `mdoc` (`Cbor_Encode`, `Mdoc_Mac`, `Device_Auth`, `Mdoc_Inputs`, `Mdoc_Spec`, `Mdoc_Proof`, `Mdoc_Status`, `Mdoc_Verifier`, `Mdoc_Prover_Lib`):

- No run-time error: no overflow, no index out of range, no read of an uninitialised value, and the ownership checks on the two commitments, the two proofs received and the proof buffers (no dangling or double free, every allocation freed on every path that does not return it).
- `Cbor_Encode.Head` returns the bytes the standard prescribes, for every length (Gold).
- `Mdoc_Mac.Legacy_Tags` returns the six products of Section 1.3 (Gold).
- `Mdoc_Inputs.Hash_Inputs` fills exactly `Hash_Count` elements, the constant one first, the six tags and av last at their positions; `Sig_Inputs` fills 900 with the constant one, the key and e2 first (Gold on the counts and positions). `Witness_Parts`, when it accepts, returns the last six elements as the pads; `Place_Pads` leaves the pads where `Witness_Parts` and `Sig_Pads_Match` read them (Gold).
- `Mdoc_Proof.Write_Tags` and `Read_Tags` write and read each tag at 16 I (Gold).
- `Mdoc_Spec.Lookup` returns a row whose combined identifier is the one asked for.
- The statuses of `Mdoc_Prover.Prove` and `Mdoc_Verifier.Verify` are as stated: a detail status exactly when one of the two provers or verifiers failed, a non-empty proof exactly on `Ok`.

What the proofs do not say: that the bits pushed are upstream's (Section 5), that e2 is upstream's digest, that the rows of the table are upstream's. Those are tested.

The partition `mdoc` on the proving machine from the final sources, GNATprove 16.1 with the project's prover configuration ([ADR 0020](../adr/0020-prover-configuration-step-budget.md)): 695 checks, all proved, no justification, no `pragma Assume`; 101 by flow analysis, 594 by the provers (371 run-time checks, 78 assertions, 145 functional contracts), the most steps used by a proof 51,968, a ninth of the budget. Seven runs on the working tree during the block. The first stopped on a rule of the language rather than a check: the two proof buffers of `Mdoc_Prover.Prove` were allocated without a value, which SPARK does not allow, and are now allocated as zeros. Two runs left the comparison of the pads in `Sig_Pads_Match` unproved, a function whose result had to be proved equal to a quantifier over 384 elements while it is computed as a mask: the proof closed once ghost code, never compiled, carried the quantifier one element at a time and kept the position of the first mismatch as the counterexample for the other direction. The whole project at the gate of the block is in the pull request.

## 5. What is only tested

### 5.1 The proof accepted by upstream's verifier

The exit criterion of the block (#65, criterion 1): a proof made by `longfellow_prove_mdoc` from the witness files is accepted by upstream's `run_mdoc_verifier`. `tests/vectors/upstream/verify_mdoc.rs` is a driver for upstream's runtime crate at d5e6be7, built as an example as `scripts/measure/heap_v7.rs` is, which reads a proof file and calls `run_mdoc_verifier_inner` under the parameters of the test case of Section 2.2, for the version 7 or the version 6 archive; it exits with status 0 only when upstream accepts. It is run by hand with cargo (the commands are in the file's header) on the proofs the `cli` step writes under `cli/out/`. On 8 November 2026, on the two proofs of this block, versions 7 and 6: both accepted; a copy with one tag altered refused with upstream's `GeneralFailure`.

### 5.2 Upstream's example proofs accepted

Criterion 2: `longfellow_verify_mdoc` accepts upstream's example proof of each archive (`<id>.bin` under `tests/vectors/upstream/mdoc/`) under the parameters of Section 2.2, in the `cli` step of `make check`, every time. The same step makes a proof from the witness files on each archive with `--seed 1`, verifies it, and checks the refusals: a wrong date, a wrong attribute value, a wrong document type (refused through e2 by the signature circuit), a tag altered by one bit (refused by the hash circuit, whose public inputs hold the tags), the proof cut short by one byte (`Proof_Encoding`). `scripts/measure-mdoc.sh mdoc` is the script; it runs with the default 8 MB stack.

### 5.3 Times and memory

The first session of the proving machine on this block (8 November, commit e5d208e against upstream d5e6be7, [ADR 0067](../adr/0067-performance-milestones-by-trust.md)) measured the two programs against upstream's `heap_v7`, the same flow on both sides: both circuits of the version 7 pair in one process, generic arithmetic, baseline processor target, three runs each, the median. The proof takes 4.47 s and a peak heap of 132 MB against upstream's 4.06 s and 107 MB (1.10 and 1.23 times); the verification 2.55 s and 64 MB against 1.61 s and 48 MB (1.58 and 1.33 times). The criterion of the memory milestone ([ADR 0080](../adr/0080-milestone-memory.md)), twice upstream's peak, holds for the complete proof of age: 61 % of it for the prover, 67 % for the verifier. The version 6 pair, one run: 3.88 s and 111 MB to prove, 2.34 s and 59 MB to verify. The tables, the resident sets and the comparison with the single-circuit programs in the same session are on [the performance page](performance.md), "The mDoc proof of age".

### 5.4 The vectors and the harness

`gen_mdoc_layer_vectors.py` writes `mdoc_layer.txt`: the CBOR heads at the boundaries of the standard; the tags on random inputs and on the real pads and messages of each witness file, where the expected tags are the file's; e2 on the test case and on synthetic inputs (an empty transcript, a document type of 30 bytes and one of 300, a transcript above 255 bytes, the three lengths of the CBOR head); the public inputs of the hash circuit for both versions, one and two attributes, a short date, a long identifier, no attribute, as the digest of the elements' bytes, and the real cases as the digest of the files' public parts; the public inputs of the signature circuit, random and real; the ends of each witness file, with the pads at the end of the signature witness; the two rows of the table. `mdoc_kat` checks every unit against it, places fresh pads in both witnesses and reads them back, and, without vectors, the limits of the two layouts, a witness without the layout, the tags through the front of the proof, an unknown specification: 76 checks. The real cases are the check of Section 2.2 made permanent: the generator fails unless its transcription rebuilds the files, and the harness fails unless the Ada units rebuild them.

## 6. What stays trusted, and the limits

**The construction as upstream's code specifies it.** No document of the pinned draft covers the mDoc layer: the tags, the layouts of the public inputs, e2's fixed headers and the table of specifications are specified by upstream's code and tested against it. The trusted base register lists them (rows R8 to R10), with the test case the witness files were recovered from.

**What the circuits compute** (register row R2) is trusted until the certified circuits milestone: the layer puts the right values on the right wires, and that the hash circuit checks the attribute and the dates, and the signature circuit the two signatures, is what the circuit files say they do.

**The four conditions of section A.8** of Annex A of the EU Age Verification technical specification, and what this block covers of each. For each condition: what the layer does, what the circuit enforces (R2, trusted), and what the relying party checks outside the proof.

| A.8 condition | What the layer does | What the circuit enforces (R2) | Outside the proof |
|---|---|---|---|
| 1. The attestation's signature verifies under the attestation provider's key. | Puts the issuer's key in the signature circuit's public inputs; binds the digest the issuer signed across the two circuits with the first pair of tags, av drawn after both commitments. | The hash circuit computes SHA-256 of the MSO and checks the tag of the digest; the signature circuit verifies the issuer's ECDSA signature on that digest under the key and checks the same tag. | That the key is the attestation provider's: the relying party's trust list. The layer takes the key as given. |
| 2. The attestation includes the requested attribute with value true. | Puts the attribute's identifier and its CBOR value in the hash circuit's public inputs, in upstream's framing. The layer passes the requested value as given (`F5` for `age_over_18`) and does not require it to be true: the relying party chooses what it requests, the circuit checks the presence of that value, and the same holds for `age_over_NN`. The test case of this block requests `family_name` with the value `"Mustermann"` (Section 2.2). | The hash circuit checks that an issuer-signed item with that identifier and value hashes to a digest the MSO lists, at an offset the prover chooses (the framing question of #88). The namespace is not checked by the version 7 circuit. | Nothing: this is the heart of the proof. |
| 3. The app instance can sign the nonce with the device key included in the attestation. | Computes e2 from the session transcript and the document type and puts it in the signature circuit's public inputs; binds the device key's coordinates across the circuits with the second and third pairs of tags. | The hash circuit checks the device key in the MSO against the tags; the signature circuit verifies the device's ECDSA signature on e2 under that key and checks the tags. | The relying party supplies the session transcript with its nonce and checks their freshness. The document type reaches the circuit only through e2 at version 7. |
| 4. The attestation is within its validity period. | Puts `now` in the hash circuit's public inputs, 20 bytes as bits. | The hash circuit compares the MSO's validity dates with `now`. | The relying party chooses `now`; the layer does not read a clock. |

So the block covers the binding and the public side of all four conditions: every public input they rest on, the tags that make the two circuits speak of one credential, and the one transcript that makes the proof non-interactive and binds av to both commitments. Not covered: what the circuits compute (R2, #88 and the certified circuits milestone), the witness from the credential (block 6), the relying party's trust in the issuer's key, the freshness of the nonce, revocation, and the security level of the profile as a whole (#79).

**The transcript bound** of 65,000 bytes follows upstream's pull request 223, not merged at d5e6be7; issue #122 re-reads it.

**Memory.** Both commitments are alive together between the second `Commit` and the first `Prove_Committed`; the structure is upstream's and cannot be otherwise, since av, which the public inputs need, exists only after both. Section 5.3 measures the peak.
