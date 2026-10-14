# 0029 SHA-256 and AES-256 in SPARK: Silver with NIST vectors, constant-time exemption

## Status

Accepted (2026-10-14, at the close of stage 4)

## Date

2026-10-13

## Context

The transcript of draft Section 3 needs two primitives: SHA-256 as the incremental accumulator whose digest seeds the generator, and AES-256 encryption of single blocks for the generator `FsPrf` (Section 3.1.1; the key schedule, the fourteen rounds, no decryption). The README trust model has listed "the SHA-256 implementation once introduced" as trusted since the first commit. No Ada or SPARK dependency of the project provides either primitive; the toolchain is pinned ([ADR 0020](0020-prover-configuration-step-budget.md)) and every dependency enters the proof perimeter and the hosted gate.

The constant-time discipline of [ADR 0006](0006-constant-time-discipline-and-scope.md) was decided for field arithmetic that the prover will run on secret witnesses. A table-based AES (S-box lookups indexed by data) leaks its input through the cache and is the textbook case the discipline excludes. What the transcript processes, however, is the content of the proof string: the label, the commitment root, the public inputs, the term count, the padded evaluations and claims, and the challenges derived from them. All of it is public by construction; a transcript that absorbed a secret would be a protocol error, not a timing one.

## Decision

- SHA-256 (FIPS 180-4) and AES-256 encryption (FIPS 197: key expansion and the forward cipher only) are written in SPARK in this repository, as packages `Sha256` and `Aes256`, proved Silver: absence of run-time errors for every input, every subprogram proved terminating.
- Their functional correctness is not proved. It is anchored by known-answer vectors (FIPS 180-4 examples and CAVP short messages for SHA-256; FIPS 197 Appendix C.3 and SP 800-38A F.5.5, CTR-AES256, for AES-256; [ADR 0032](0032-transcript-vectors.md)). The package headers and the README trust model say so: what is proved is that the code does not fail; that it computes SHA-256 and AES is tested.
- A table-based AES is acceptable: the S-box as a constant table indexed by data bytes, and the round as byte operations over it. The constant-time discipline of ADR 0006 is declared not applicable to `Transcript`, `Sha256` and `Aes256`, with the reason above recorded in each header, together with the instruction that these packages must never be used on secret data; a future use on secrets (none is planned: the prover's pads come from its own randomness, not from the transcript) is a new decision.
- `Sha256` exposes an incremental interface (a context, `Update` over a byte array, `Digest` as a function, so that the accumulator survives, as `get_hash` does in the reference). The ghost absorbed-bytes model of [ADR 0031](0031-transcript-gold-perimeter.md) does not live in the context: GNAT 16 has no ghost record components (found at block 1, 2026-10-13), so the model is state of `Transcript`, whose single call to `Update` is the point where the model is appended to. `Aes256` exposes the key schedule and single-block encryption; `FsPrf` in `Transcript` builds the counter mode over it.

## Alternatives considered

- **An external SPARK crate from the Alire index.** Rejected: a third-party implementation would enter the proof perimeter and the trust model under its own proof level and conventions, pinned to a GNATprove release outside the project's control; SHA-256 and the forward AES cipher are a few hundred lines, and reviewing them is cheaper than reviewing a dependency.
- **A binding to a C library (OpenSSL, libsodium).** Rejected: code outside SPARK at the heart of the verifier breaks the project-wide absence of run-time errors claim and adds a platform dependency to the hosted gate.
- **A bitsliced or otherwise constant-time AES.** Rejected: the data are public, the implementation is longer and its proof costlier, and the project would still claim nothing about timing (ADR 0006 proves nothing about time). Noted as the change to make if the transcript ever processes secrets.
- **Proving functional correctness against a formal specification of SHA-256 or AES (Gold).** Not pursued: the specification would be a transcription of FIPS 180-4 or FIPS 197 in ghost code, and the proof would show the code equals that transcription, as `Mul_Ref` did for `Mul`; the gap between the transcription and the standard would still be closed by vectors. The vectors close the whole gap at once, and the two functions are not where soundness lives (a wrong hash gives wrong challenges, which the end-to-end vectors of ADR 0032 detect).
- **SHA-256 only, with a hash-based generator instead of AES.** Rejected: the draft and the reference fix AES-256 in counter mode, and the B.2 vectors depend on it.

## Consequences

- Two new packages in the library, about the size of `GF2_128`, with their vectors and a harness.
- The README trust model moves SHA-256 and AES-256 from "once introduced" to "introduced, Silver plus NIST vectors", and the constant-time entry gains the exemption with its reason.
- The verification condition count grows by the Silver checks of two byte-oriented kernels (array indexing, shifts, modular arithmetic), expected to be cheap.

## Verification impact

- Provable: absence of run-time errors and termination of both packages.
- Tested: that the digests and ciphertexts are those of FIPS 180-4, CAVP, FIPS 197 and SP 800-38A on the committed cases; the B.2 vectors of the draft exercise both through the transcript.
- Trusted: that the code computes SHA-256 and AES-256 on inputs the vectors do not cover.
- Constant time: exempt for `Transcript`, `Sha256` and `Aes256`, on the ground that they process public data only; the exemption is recorded in the headers and in the README.

## References

- FIPS 180-4 (Secure Hash Standard), Section 6.2; FIPS 197 (Advanced Encryption Standard), Sections 5.1 and 5.2, Appendix C.3; NIST SP 800-38A, Appendix F.5.5; CAVP SHA-256 short message tests.
- draft-google-cfrg-libzk-03, Sections 3.1 and 3.1.1.
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/transcript.rs` (`FsPrf`, `get_hash`).
- [ADR 0003](0003-proof-policy-and-trust-model.md), [ADR 0006](0006-constant-time-discipline-and-scope.md), [ADR 0028](0028-stage-4-scope-and-challenge-replay.md).
