# 0028 Stage 4 scope: Fiat-Shamir transcript and challenge replay

## Status

Proposed

## Date

2026-10-13

## Context

Stage 3 left the symbolic verifier core with its challenges as an input ([ADR 0022](0022-stage-3-scope-and-challenges-as-input.md)): the `Challenges` record of `Sumcheck_Verifier` is the interface between the core and whatever derives the challenges, and the derivation is listed as trusted in the README. In the protocol every challenge is a Fiat-Shamir value: the transcript of draft Section 3 absorbs the public data of a proof, byte-framed by a tag-length-value codec, and yields pseudorandom bytes seeded by a hash of everything absorbed so far; field elements, naturals and subsets are extracted from those bytes. The reference implementation at d5e6be7 drives one transcript from the label through the sumcheck part and on into Ligero (`zk/verifier.rs`, `sumcheck/common.rs`, `transcript.rs`).

Two facts about the reference fix the shape of this stage. First, the transcript itself knows nothing of fields: it hashes and encrypts bytes, and the field enters only through the serialisation of elements (Section 7.2.1) and the sampler of Section 3.4.3. Second, the challenges that the core consumes are determined by the label, the commitment root, the statement (circuit identifier, public inputs, term count) and the padded sumcheck proof, in that order, with nothing else in between.

## Decision

Stage 4 is the transcript of Section 3 and the replay of the challenges from a proof. Following the reference implementation at d5e6be7:

- **`Transcript`**, a package that is not generic, with state rather than a type (one transcript at a time, `Reset (Label)` starts a new one; amended at block 1, 2026-10-13, since the ghost model of [ADR 0031](0031-transcript-gold-perimeter.md) cannot be a record component in GNAT 16): the SHA-256 accumulator and the generator `FsPrf` (AES-256 in counter mode, `Block[i] = AES256(SEED, ID(i))` with `ID(i)` the 16-byte little-endian encoding of i from 0, Section 3.1.1; the counter is bounded by 2^40 blocks as in the reference, where `refill` panics at the bound; here the generator does not encrypt past it: it returns zero bytes and raises a sticky `Exhausted` flag on the transcript, which no later write or draw clears; unused bytes of a block are kept for the next request); the byte-level codec of Section 3.2 (`Write_Bytes`: tag 0x00, length as eight little-endian bytes, the bytes; `Write0 (n)`: the same frame around n zero bytes; the element frame: tag 0x01 then the serialised element; the slice frame: tag 0x02, count as eight little-endian bytes, then the serialised elements with no per-element tag); `Get_Random_Bytes` (when no generator is live, the seed is SHA-256 of every byte absorbed so far, tags and lengths included, and the generator is discarded on every write, tag and length bytes included, Section 3.1 and `transcript.rs`); `Nat` (Section 3.4.1: l is the byte length of n, the mask is the smallest all-ones value covering n itself, the l bytes are read little-endian, masked and accepted if below n); `Choose` (Section 3.4.2: a fresh array 0 .. n - 1, k steps of `j = i + nat (n - i)`, swap, take `a (i)`; empty when n or k is 0; `k <= n` is a precondition, as the reference asserts, since with k > n the loop would reach `nat (0)`). A transcript is created from a label by `Write_Bytes` of the label, as `Transcript::new` does. `Choose` bounds n to 2^16 (the largest of Appendix B.2.5; the array of the shuffle lives on the stack); phase B raises it if Ligero needs more. The element and slice frames take serialised bytes, so the package has no field parameter and the test harness can drive it with any encoding.
- **A shared byte type.** A package `Bytes` declares `Byte_Array` (unsigned 8-bit, `Natural` index) and the fixed subtypes the stage needs; `P256_Field` keeps its `Byte_Array` as a subtype renaming it, so that its stage 2 contracts do not change.
- **`Field_Signature` extended** with `Serialized_Size`, `To_Bytes`, `From_Bytes` (a procedure with an `Ok` flag, accepting exactly the canonical little-endian encodings of Section 7.2.1: for P-256 the values below p, for GF(2^128) every 16-byte string) and a Boolean constant `Sampling_Rejects` (True for P-256, False for GF(2^128)). `GF2_128.To_Bytes` and `From_Bytes` are new; `P256_Field` already has both. Both wrappers are updated.
- **A generic glue over the field**, `Sumcheck_Transcript`, instantiated for both fields: `Sample` (draw `Serialized_Size` bytes, `From_Bytes`, repeat until accepted; this is the sampler of Section 3.4.3 for both fields, 16 bytes read as coefficients for GF(2^128), 32 bytes little-endian with rejection of values at or above p for P-256); `Write_Element` and `Write_Element_Slice` over the byte-level frames; `Write_Sumcheck_Statement` (`zk/common.rs`: `Write_Bytes` of the 32-byte circuit identifier, then each public input as its own element frame, then one zero element, then `Write0` of the total term count over all layers); `Begin_Circuit` (`MAX_LOGW = 40` draws q, discarded, then 40 draws g); `Begin_Layer` (alpha, then beta); `Round_Poly` (element frame of the padded p (0), element frame of the padded p (P2), then one draw); `End_Layer` (the two padded claims as one slice); and `Replay_Challenges`, which from the label, the root, the circuit, the public inputs and the padded sumcheck proof fills the stage 3 `Challenges` record exactly as `symbolic_sumcheck_verifier_core` draws them: `Begin_Circuit`, then per layer `Begin_Layer`, for each round and each hand `Round_Poly`, `End_Layer`, and after the last layer one draw for `alpha_input`. `Replay_Challenges` returns a status: `Ok`, or `Exhausted` when the generator passed 2^40 blocks during the replay, in which case the record is not to be used; the status is the reference's panic rendered as an outcome, and no proof reaches it in practice (a draw takes at most three blocks and the longest run of draws between two writes is the 80 of `Begin_Circuit`, so the flag can only be raised by an astronomically long run of rejected samples).
- **The sumcheck proof reader**, in the glue: from the bytes of Section 7.3 (per layer, per round the four elements hand 0 p (0), hand 1 p (0), hand 0 p (P2), hand 1 p (P2), then the two claims; no length prefixes, the layout given by the circuit) into `Sumcheck_Proof`, whose flat layout is the pad order of Section 6.5 (hand h of round r at 4 r + 2 h and 4 r + 2 h + 1). `From_Bytes` rejects a non-canonical P-256 element, and the reader returns a status, never raises. The root is the first 32 bytes of a complete proof (Section 7.5); the sumcheck part follows.

Out of scope: Ligero and everything the transcript does after `alpha_input` (the Ligero verifier writes `DEFAULT_STATEMENT_HASH` and draws its own challenges, `ligero/verifier.rs`); the subfield GF(2^16) sampler; the reader of the complete proof beyond root and sumcheck part; the prover's use of the transcript (phase C).

## Alternatives considered

- **A transcript generic over the field.** Rejected: hashing, encryption and the codec do not depend on the field, and a generic transcript would have to be instantiated once per field and proved twice for no gain; the field enters only through serialisation, which the glue owns.
- **The transcript inside the verifier core.** Rejected by ADR 0022: the core stays a function of a complete `Challenges` record, so that the recorded upstream runs keep checking it with injected challenges while the replay is checked separately against the same recordings.
- **`Sample` as a formal subprogram of `Field_Signature`.** Rejected: a sampler needs the transcript as its source of bytes, and the field packages must not depend on the transcript; with `From_Bytes` and `Sampling_Rejects` in the signature the rejection loop is written once in the glue and is the same loop for both fields.
- **Writing the public inputs as one slice.** Rejected: the reference writes each public input as its own element frame (`zk/common.rs`, lines 34 to 36), and the two encodings hash differently.

## Consequences

- The `Challenges` record and the preconditions of `Verifier_Core` are unchanged; stage 4 is a producer of that record.
- The harness `sumcheck_kat` switches to replayed challenges on the recorded runs and keeps the injected path as a cross-check ([ADR 0032](0032-transcript-vectors.md)).
- The README trust model removes "the challenge derivation until stage 4" and gains the entries of [ADR 0029](0029-sha256-and-aes256-in-spark.md).
- Phase B will drive the same transcript from `alpha_input` onwards for Ligero; `Transcript` exposes `Choose` for that purpose already.

## Verification impact

- Provable: absence of run-time errors on every subprogram of the stage for every input (Silver); the Gold perimeter of [ADR 0031](0031-transcript-gold-perimeter.md); the shape of the filled `Challenges` record (sizes and indices).
- Tested: the transcript against the draft's Appendix B.2 and the replayed challenges against the recorded upstream runs ([ADR 0032](0032-transcript-vectors.md)).
- Trusted: the functional correctness of SHA-256 and AES-256 beyond the vectors ([ADR 0029](0029-sha256-and-aes256-in-spark.md)); the completeness of the absorption, which no contract states: the sequence of writes above is the checklist, and the B.3 end-to-end vectors are its test.
- Constant time: not applicable to this stage, with the reason recorded in ADR 0029.

## References

- draft-google-cfrg-libzk-03, Sections 3.1, 3.1.1, 3.2, 3.3, 3.4.1 to 3.4.3, 6.5, 7.2.1, 7.3, 7.5.
- google/longfellow-zk at d5e6be7, `docs/specs/rust/src/`: `transcript.rs` (the struct, `write_untyped`, `write_bytes`, `write0`, `write_elt_field`, `write_elt_field_slice`, `get_random_bytes`, `nat`, `choose`, `FsPrf`), `zk/common.rs` (`write_sumcheck_statement`), `zk/verifier.rs` (the driving order), `sumcheck/common.rs` (`begin_circuit`, `begin_layer`, `round_poly`, `end_layer`), `sumcheck/proof.rs` (`read_sumcheck_proof`), `algebra/gf2_128.rs` and `algebra/p256.rs` (`to_bytes`, `from_bytes`, `sample`), `ligero/verifier.rs` (what follows `alpha_input`).
- [ADR 0022](0022-stage-3-scope-and-challenges-as-input.md), [ADR 0024](0024-field-genericity-by-formal-package.md); `src/sumcheck_verifier.ads` (the `Challenges` and `Sumcheck_Proof` records).
