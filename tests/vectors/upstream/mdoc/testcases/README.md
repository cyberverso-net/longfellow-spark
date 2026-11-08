# Upstream's test documents (block 6 of Phase D, ADR 0086)

One directory per test case of `rust/applications/mdoc_zk/testcases/src/vectors.rs`
of longfellow-zk at commit d5e6be77336933d50bf7f25a954f8ec273eb51ce, the pin
(ADR 0002, ADR 0079), with the case's data as files:

- `mdoc.bin`: the bytes of the `mdoc` array, the credential as the holder
  presents it (CBOR: `documents[0]` with `issuerSigned` and `deviceSigned`);
- `transcript.bin`: the bytes of the `transcript` array, the session transcript;
- `request.txt`: `pkx`, `pky` (the issuer's public key, as upstream writes them),
  `now` (the date the proof is evaluated at) and `doc_type`, one per line.

The files are copied unchanged from the Rust source (the hex arrays as bytes, the
strings as they are). Licence: Apache-2.0, the project's own. The SHA-256 of each
copy:

## `FAMILYNAME_MUSTERMANN_MDOC_3` (upstream's `familyname_mustermann-mdoc[3].json`)

The document from which upstream made the witness files and the example proofs of
both archives under `../` (chapter 9, Section 2.2): `family_name` = `"Mustermann"`,
dated `2024-10-01T09:00:00Z`, document type `org.iso.18013.5.1.mDL`, a transcript of
143 bytes, a document of 3,173 bytes.

    8583f7eb06731c4db7fff8b51a7e5f0649a6328fabb4f11e894f01c87894fbd9  mdoc.bin
    63aa38f9523ee40b9543bdbe6c8f3259c54ce8bca3cfc7f5cfc9cc3231bb1c09  transcript.bin
    e0cfc3d0096db9384c50ba4797862e2e071cecb2b3f7e3b195ea9235972d1557  request.txt

Used by `gen_ecdsa_witness_vectors.py`, which reads the two signatures and the
device key off the document and checks the ECDSA witnesses it computes against the
signature witness files of both archives (block 6a, #134). The other 37 documents of
`vectors.rs` come in with the parse of the document (block 6b, #135).
