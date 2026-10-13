# 0032 Transcript vectors: Appendix B.2, Appendix B.3 end to end, NIST

## Status

Proposed

## Date

2026-10-13

## Context

The Gold of stage 4 is structural ([ADR 0031](0031-transcript-gold-perimeter.md)): it proves the framing and the extraction properties, not that the digests, the keystream or the challenges are the draft's. The draft gives, in Appendix B.2, the only published vectors of the transcript itself: five chained steps over a 4-word prime field with 48 generated elements, 24 `nat` results and 6 `choose` lists. Appendix B.3 gives two complete proofs for the explicit circuits of stage 3, with their labels and commitment roots; the stage 3 recordings of the upstream verifier (`tests/vectors/upstream/`, [ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md)) hold the challenges that the upstream core consumed on those very proofs. NIST publishes vectors for SHA-256 and AES-256. Three facts about B.2 were established while reading it against the code and by an independent recomputation: the field is defined by the prime of secp256k1 (2^256 - 2^32 - 977), so 2^256 - p = 2^32 + 977, the probability that a 32-byte draw is rejected is about 2^-224 and no rejection occurs in the vectors; the element 7 and the array [8, 9] are written as 32-byte little-endian encodings; the printed values are the big-endian integers of the elements, not the little-endian byte strings drawn.

## Decision

Vectors for stage 4 come from three anchors, in the notation of [ADR 0009](0009-known-answer-vectors.md) where it applies (plain text, one case per line).

- **(a) Appendix B.2, in full.** A harness-only sampler for the 4-word field of B.2 reads 32 bytes little-endian and asserts the value below p, so that byte consumption is reproduced exactly; it lives in the test project, since the library has no secp256k1 field, and drives the byte-level frames of `Transcript` with 32-byte little-endian encodings of 7, 8 and 9. The harness checks, byte for byte: the 16 elements after the label `test` and the 100-byte array 0 .. 99 (B.2.1), the 16 after the element 7 (B.2.2), the 16 after the array [8, 9] (B.2.3), the 24 `nat` results after the string `nats` (B.2.4) and the 6 `choose (m, 20)` lists after the string `choose` (B.2.5), each step starting from the state the previous one left. The expected values are the draft's, embedded in the vector file as printed (big-endian integers).
- **(b) Appendix B.3, end to end against tier 3.** For each of the two circuits: the label (`sgonal_test_vector_p256`, `sgonal_test_vector_gf2_128`), the root as the first 32 bytes of the "Complete Proof Serialization" block, the sumcheck part as the next 4 logw + 2 elements per layer (768 bytes for B.3.2, 384 for B.3.3), the explicit circuit already in `tests/vectors/` and its public input, and the circuit identifier of 32 zero bytes that the upstream unit tests use. The proof reader must produce the padded proof the recording holds (verified fact: the first sumcheck element of B.3.3, bytes `6240c86a ... 9d28` little-endian, is the first recorded element `289d0e3f ... 4062`); `Replay_Challenges` must reproduce the recorded g (all 40), the per-layer `layer_challenges` and `alpha_input`; and `Verifier_Core` on the replayed challenges must emit the recorded constraints. The harness `sumcheck_kat` runs the recorded files both ways, injected and replayed, and both must agree with the recording. A negative case feeds a P-256 proof with one element at or above p and expects the reader to reject it.
- **(c) NIST and encoding vectors.** SHA-256: the FIPS 180-4 examples (`abc`, the 448-bit and 896-bit messages) and a selection of CAVP short messages, by their published values; AES-256: FIPS 197 Appendix C.3 (one block) and SP 800-38A F.5.5 (CTR-AES256: four input blocks with their outputs, checked as single-block encryptions; the counter layout of `FsPrf`, little-endian from zero, is the draft's and is anchored by B.2, not by the standard). Section 7.2.1 encoding: `GF2_128.To_Bytes` and `From_Bytes` on the subfield basis constants of stage 1, on structural cases, and on the first element of B.3.3 above, which anchors the byte order on the draft.
- **The generator `gen_transcript_vectors.py`**: an independent Python reference of Sections 3.1 to 3.4 (`hashlib` for SHA-256, a from-scratch AES-256 written in the generator, no third-party package) that reproduces every value of B.2 from the draft's text, replays the transcript of B.3 and compares its challenges with the tier 3 recordings, and aborts with a non-zero status on any mismatch with the values it embeds; `make vectors` compares its output with the committed files as for the other generators. The NIST cases are copied constants, not recomputed.
- **The harness `transcript_kat`** runs (a) and (c); (b) extends `sumcheck_kat`. Both fail on any case and when no case ran; `scripts/check.sh` runs them.

## Alternatives considered

- **B.2 with the library's P-256 field instead of the secp256k1 field.** Rejected: the element 7 encodes identically, but the sampler's rejection bound is p, and a draw between the two primes (probability about 2^-32 per draw against 2^-224) would diverge; the vectors are defined over the 4-word field and are reproduced as such.
- **Reading the "Sumcheck Proof" block of B.3 directly.** Not possible for B.3.3: the block is absent from the TXT and the HTML renderings of draft-03 (a presentation erratum, added to the list of [ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md)); both proofs are taken from the complete serialisation, whose layout Section 7.5 fixes and which the sizes confirm (32 + 768 + 4652 = 5452 and 32 + 384 + 2632 = 3048 bytes).
- **Recording the transcript state from upstream (digests, keystream) as a tier 3 file.** Not needed: B.2 anchors the transcript on the draft directly, and the recorded challenges anchor the replay; a disagreement is localised by B.2 (transcript) or by the first differing challenge (replay order).
- **Testing SHA-256 and AES-256 only through B.2.** Rejected: B.2 fails as a whole on any error; the NIST cases localise an error to the primitive.

## Consequences

- `tests/vectors/` gains `transcript_fs.txt` (B.2), `sha256.txt`, `aes256.txt`, `gf2_128_bytes.txt`, `zk_proof_p256_b3_2.txt` and `zk_proof_gf2_128_b3_3.txt` (label, root, sumcheck bytes), the generator, and the harness `transcript_kat`; `sumcheck_kat` gains the replayed path.
- The README trust model moves "the challenge derivation" from trusted to tested, naming the files, and lists SHA-256 and AES-256 as Silver plus NIST vectors ([ADR 0029](0029-sha256-and-aes256-in-spark.md)).
- The errata list of ADR 0027 and chapter 3 gains the missing B.3.3 block and the "scalar field" wording of Section 3.4.3, to be reported with the others.

## Verification impact

- Provable: nothing; vectors are tests.
- Tested: the transcript against the draft byte for byte (B.2); the replay against the upstream verifier on the two published proofs (B.3); SHA-256 and AES-256 against NIST; the GF(2^128) encoding against the draft.
- Trusted: that the draft's vectors were produced by the protocol the draft describes (the recomputation and the upstream code agree with them); that the recordings of tier 3 are faithful (ADR 0027).
- Constant time: no effect.

## References

- draft-google-cfrg-libzk-03, Appendix B.2.1 to B.2.5, B.3.2, B.3.3, Sections 3.4.3, 7.2.1, 7.3, 7.5.
- google/longfellow-zk at d5e6be7: `docs/specs/rust/tests/unit_tests.rs` (`test_fiat_shamir_test_vectors`, `test_sgonal_test_vector_p256`, `test_sgonal_test_vector_gf2_128`: labels, the zero circuit identifier, the expected roots and proof sizes).
- FIPS 180-4; FIPS 197, Appendix C.3; NIST SP 800-38A, Appendix F.5.5; CAVP SHA-256 short message tests.
- `tests/vectors/upstream/sumcheck_core_p256_b3_2_sgonal.txt`, `sumcheck_core_gf2_128_b3_3_quadratic.txt`.
- [ADR 0009](0009-known-answer-vectors.md), [ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md), [ADR 0028](0028-stage-4-scope-and-challenge-replay.md), [ADR 0031](0031-transcript-gold-perimeter.md).
