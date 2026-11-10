# 0086 The witness from the mDoc: the bounds, the constant-time perimeter and the inversion of secrets

## Status

Accepted (2026-11-09, with the third and last pull request of block 6, #136; Proposed since 2026-11-08 with the first, #134). Note of 2026-11-10 (#150): one deliberate divergence from upstream's witness builder, beside the bounds of this record: at version 6 `Mdoc_Witness.Hash_Witness` refuses, with the status `Item_Order_Unsupported`, before any commitment and with the witness array zeroed, an issuer-signed item whose `elementValue` entry does not follow its `elementIdentifier` entry, the one order the version 6 circuit frames (its generator, `lib/circuits/mdoc/mdoc_hash.h` before upstream's commit 0d92f80, compares the identifier's text, the key `elementValue` and the value as one span shifted by the identifier's offset; the runtime's builder places that offset at `slot[ei] + 18` with the span `id_len + val_len + 13`), where upstream's builder builds the witness and its circuit refuses the proof after the commitment. The rule, "the slot of the value is the slot of the identifier plus one", was derived from the framing formula and checked against the generator's code before it was written; chapter 9 Section 3.7 states it as a constraint for issuers. The version 7 circuit reads the order from the witness and the status never applies there. A correction to the Verification impact below: upstream's negative test cases are six (`FAIL_*`), not eight. This record completes the constant-time account that [ADR 0058](0058-mdoc-layer.md) promised at block 6, and takes the decision that [ADR 0051](0051-constant-time-in-the-prover.md) reserved on the inversion of secrets; both records point to it from their Status lines.

## Date

2026-11-08

## Context

Block 5 of Phase D (ADR 0058, #126) made the mDoc proof of age from upstream's witness files. Block 6 (#66) builds the two witnesses from the credential itself: the CBOR parse of the document, the SHA-256 trace of the signed part, the positions of the fields, the ECDSA witnesses of the two signatures, the device key. Three things about it are decisions rather than transcriptions of upstream, and the design of the block (reviewed and approved by the author) asked that they be recorded before the code.

First, the bounds. Upstream's parser works on heap vectors of any size and recurses without a depth limit; a SPARK parser without recursion and without the heap needs bounds, and the proofs of the arithmetic on lengths and offsets need them too. Upstream itself bounds three things through its circuits: the signed part of the document (the MSO) by the SHA-256 capacity of the hash circuit, an issuer-signed item by two SHA-256 blocks, and the session transcript and the document type as block 5 recorded them.

Second, the perimeter of constant time. The credential is the secret; ADR 0058 said that the parse "depends on the data, and the data is the secret", and deferred to this block the account of which parts are constant time and which are not. Upstream's parse is not constant time, and neither is its scalar multiplication on the curve (`scalar_mul` of `core/algebra/src/ec.rs` branches on the bits of the scalar; the rounds of `ecdsa2/concrete.rs` index a table with the secret bits).

Third, the inversion of secrets. ADR 0051 noted that the prover of Phase C computed no inverse of a secret and said: "should an inversion of a secret become necessary, it is a decision to take first." The ECDSA witness of upstream's signature circuit needs s^-1 in the scalar field and rx^-1, pkx^-1, (-s mod q)^-1 and the Z^-1 of each affine conversion in the base field, all on values of the credential.

## Decision

**The bounds.** Six, each a constant of the units, each excess refused with a status and never silently truncated:

- the signed part of the document, the wrapped MSO (tag 24 and its two-byte length head included): at most 2,531 bytes for the version 7 circuits and 2,211 for version 6, the SHA-256 capacity of the hash circuit (40 or 35 blocks) less the 18-byte COSE prefix, the 2-byte length and the 9 bytes of padding; and a map of at least 256 bytes with a two-byte length head, the only encoding the circuits accept (`validate_mso_layout`);
- an issuer-signed item, tag 24 included: at most 119 bytes, the two SHA-256 blocks of `push_witness_attrs` less the nine bytes of padding (`Mdoc_Witness.Max_Item_Bytes`); upstream refuses an item of 256 bytes or more with `AttributeTooLong` and stops on one of 120 to 255, which does not pad into its two blocks either, so the bound here is the one its circuit enforces, as a status; the 38 test documents hold items of 79 to 103 bytes;
- the session transcript and the document type: 65,000 and 65,535 bytes, as ADR 0058 records;
- **the whole document: at most 262,144 bytes** (`Max_Mdoc_Bytes`). Upstream does not bound it. The bound covers a document with a portrait and an issuer's certificate chain; upstream's 38 test documents are between 1,264 and 3,549 bytes. The file bound of the command line stays 16 MB;
- **the CBOR nesting depth, 16, and the number of CBOR elements, 4,096**, the two bounds of a parser that walks the document once with an explicit stack and a table of elements, without recursion and without the heap. The path to an issuer-signed item is eight levels deep.
- **the issuer-signed items of a document: at most 256** (`Mdoc_Parse.Max_Items`), added with the parse (#135): the result of a parse holds the position and the locator of every item, fixed-size records in a fixed table, where upstream collects them in a vector. The 38 test documents hold between one and five items.

**The perimeter of constant time.** The discipline of ADR 0006 and ADR 0051 applies to every operation on a value once it is extracted from the document, and the parse itself is declared outside it:

- Constant time by construction: the SHA-256 trace, always over the circuit's maximum number of blocks (40, 35 or 2), the zero blocks included, as upstream's `sha256_msg_derived` computes it, so that the time does not depend on the length of the signed part; the bit and plucked encodings of the witness (fixed loops over fixed widths); the arithmetic of the base field (`P256_Field`) and of the new scalar field (`Q256_Field`, this block); the elliptic-curve arithmetic of the ECDSA witness (`P256_Curve`): the complete addition and doubling formulas of upstream (fixed sequences of field operations), the two scalar multiplications of the point R as double-and-add-always with a masked selection, where upstream branches on the bits, and the 256 rounds of the circuit's slicing with an eight-way masked selection of the table entry, where upstream indexes the table with the secret bits; the inversions, by the fixed Fermat chains of the two fields.
- Not constant time, declared: the parse of the document (`Cbor_Parse`, `Mdoc_Parse`, the second pull request of the block), and the padding of a message into its blocks (`Sha256.Trace.Pad_Message`), which copies the message and places the marker and the length where it ends, so that its work depends on the length of the signed part or of the item, a length the parse has already handled in the open. A parser over a variable-length document indexes on the lengths and positions it finds, and the UTF-8 check of every text string reads its bytes; upstream's does the same. What its timing reveals to a local observer is the structure of the holder's own credential (its lengths, the positions of its fields, the number of its items) and the bytes of its text strings (the identifiers, the text values of the items), not the signatures, the digests or the coordinates, which the parse copies by length; the lookup of the requested attribute compares identifiers of public length. The privacy of the structure inside the proof rests on the circuit, which locates the fields by secret offsets, not on the parse, which runs on the holder's device. A constant-time parse (a fixed scan of the maximum document with a masked selection of every field) was considered and rejected as out of proportion.
- The new constant-time sites join the list of #70 (the check of the generated code): `P256_Curve.Select_8`, `Select_Point`, `Select_Element`, `Mask_Of_Zero`, the loop of `Scalar_Mul`, `Add`, `Double` and `Affine`; `Q256_Field.Add`, `Sub`, `Mul` and `Inv`; `Ecdsa_Witness.Push_Legacy`. Until the check exists, the pull request of each part of the block records an inspection of the disassembly on arm64 and x86-64, as #86 did.

**The inversion of secrets is allowed**, because every inverse this project computes is a fixed addition chain: `P256_Field.Inv`, 255 squarings and 12 multiplications on an exponent chain checked against p - 2 by the vector generator, and `Q256_Field.Inv`, a window chain over the public exponent q - 2 (a table of sixteen powers, then four squarings and one multiplication per nibble, the table indexed by the constant exponent and never by the value), checked the same way; both total, with `Inv (Zero) = Zero`. The clause of ADR 0051 is amended by its Status line.

**The scalar field is a sibling of `P256_Field`.** `Q256_Field` repeats the Montgomery arithmetic on four limbs with the constants of q, the same contracts and the same proof structure, Gold on the ring operations and the conversions, Silver on `Inv` with its vectors. The two differ in one step: p is one below a multiple of 2^64, so a Montgomery round of `P256_Field` adds p times the low word itself, while q is not, so a round of `Q256_Field` first multiplies the low word by q' = -q^-1 mod 2^64. The duplication, about 900 lines of a Gold unit, is recorded here; #137 holds the generic unit that would replace both if a third modulus ever appears.

## Alternatives considered

- **No bound on the document, as upstream.** Not available: SPARK needs the bounds for the index types and the proofs; the heap would move the question, not remove it.
- **A smaller document bound**, 65,535 bytes (a two-byte CBOR length). Rejected: a portrait alone can exceed it.
- **A constant-time parse.** Rejected as out of proportion, as the Decision says.
- **Forbidding the inversion of secrets** by rewriting the witness without inverses. Not available: the circuit requires the inverses as witness values.
- **A generic Montgomery field** instantiated for p and q. Deferred to #137: a refactor of the Gold unit that every P-256 proof rests on, with the risk of step-limit surprises in each instance, is not the work of this block.

## Consequences

- The chapter of the mDoc proof of age (chapter 9) gains the sections on the witness: the ECDSA witness in the first pull request, the parse and the trace in the second, the complete witness and the proof from the document alone in the third.
- The trust model and the trusted base register say what the curve arithmetic rests on: `Add` and `Double` are Silver, anchored by the RFC 5903 vectors and by the byte identity of the ECDSA witness with upstream's files; Gold against the group law is not attempted.
- The measurement of the complete proof becomes a comparison of equals: upstream's `heap_v7` parses the document and builds its witness in the same process.

## Verification impact

- Provable: absence of run-time errors in the parser on any bytes and in the witness computation; Gold on the invariants of the parser's table, on the frame of the ECDSA witness (nothing outside its interval changes), on the counts and positions of the pieces of the complete witnesses where a contract can state them, on the bit encodings, on the selections of the curve unit.
- Tested: the curve against RFC 5903 and an independent transcription; the ECDSA witness against the signature witness files of both archives, element by element; the complete witnesses of both circuits against the four witness files, element by element, and against an independent transcription on the 38 test documents; the 38 test documents through the round trip from the document (`make mdoc-cases`), the eight negative cases refused by the circuit.
- Trusted: the curve formulas as upstream's code specifies them (register row R11), the parse's non-constant-time behaviour as declared here.

## References

- Upstream at d5e6be7: `core/algebra/src/ec.rs`, `circuits/ecdsa2/src/concrete.rs`, `applications/mdoc_zk/runtime/src/concrete/legacy/private.rs`, `applications/mdoc_zk/circuits/src/cbor/parse.rs` and `mdoc.rs`.
- Renes, Costello and Batina, "Complete addition formulas for prime order elliptic curves", EUROCRYPT 2016, algorithms 1 and 3.
- RFC 5903, Sections 3.1 and 8.1.
- [ADR 0006](0006-constant-time-discipline-and-scope.md), [ADR 0016](0016-p256-inversion.md), [ADR 0051](0051-constant-time-in-the-prover.md), [ADR 0058](0058-mdoc-layer.md), [ADR 0069](0069-p256-montgomery-multiplication.md).
