# 0031 Transcript Gold perimeter

## Status

Accepted (2026-10-14, at the close of stage 4)

## Date

2026-10-13

## Context

[ADR 0003](0003-proof-policy-and-trust-model.md) puts Gold where functional correctness buys security and Silver elsewhere; [ADR 0023](0023-gold-perimeter-for-protocol-code.md) made Gold structural for protocol code: equality with a ghost transcription of the formula, the algebraic content left to tests. The transcript has three kinds of code. Byte-level framing (the codec of Section 3.2), where a wrong tag, a wrong length width or a swapped order changes every challenge and is invisible to any test that does not reproduce the draft's vectors byte for byte. Combinatorial extraction (`nat`, `choose`, the sampler), with properties that are exactly what the protocol relies on: a value below n, k distinct indices below n, a canonical element. And the two primitives of [ADR 0029](0029-sha256-and-aes256-in-spark.md), whose functional correctness is a tested property.

The codec's natural specification is "the bytes absorbed so far": a write appends its frame to that sequence. The sequence is unbounded in principle (`write0` of the term count absorbs as many zero bytes as the circuit has terms), so a ghost model over a fixed-capacity array would either cap the circuits the proof speaks of or carry a capacity through every contract. SPARKlib, the companion library of GNATprove, provides functional (immutable, mathematical) sequences in `SPARK.Containers.Functional.Infinite_Sequences`, meant precisely for ghost models; it is published as the Alire crate `sparklib`, released in step with GNATprove (16.1.0 for the pinned toolchain).

## Decision

Gold perimeter of stage 4, in the structural sense of ADR 0023:

- **`Nat (n)`**: the result is below n. The mask is stated as a ghost property: it is the smallest all-ones value covering n, that is `(n and Mask) = n` and `n > Mask / 2`; and l is the byte length of n. The loop invariant carries both; the postcondition holds on exit ([ADR 0030](0030-literal-rejection-sampling.md) on exit itself).
- **`Choose (n, k)`**, with the precondition `k <= n` that the reference asserts: the k results are distinct and below n. Proved through the permutation invariant of the Fisher-Yates array: every entry is below n and no two entries are equal, preserved by each swap; the results are the first k entries.
- **`Sample` for P-256**: the result satisfies the canonical-form predicate of `P256_Field.Element` (the existing predicate; `From_Bytes` with `Ok` gives it). For GF(2^128) the result is the element whose coefficients are the 16 bytes read, by the postcondition of `GF2_128.From_Bytes`.
- **The codec, structural Gold over a ghost byte sequence.** `Transcript` is a package with state, one transcript at a time (`Reset (Label)` starts a new one), because the model has to be a ghost object: GNAT 16 has no ghost record components (amended at block 1, 2026-10-13; the first text put the model in `Sha256.Context`). Its ghost state `Absorbed` is a functional sequence of bytes, appended to in exactly two places, the internal `Absorb (Data)` and `Absorb_Byte (B)` (a tag) that are also the only calls of `Sha256.Update`; on top of them, every write of `Transcript` states its frame: `Write_Bytes (T, D)` appends the tag 0x00, the eight little-endian bytes of `D'Length`, then D; `Write0 (T, N)` the same frame around N zero bytes; the element frame appends 0x01 then the bytes; the slice frame appends 0x02, the eight little-endian bytes of the count, then the elements' bytes in order. Ghost functions spell each frame out as what it appends to a sequence (`Bytes_Frame (S, D)` is S, then the tag, then the eight length bytes, then D, written with `Add` and `Append`), so a postcondition reads `Absorbed = Bytes_Frame (Absorbed'Old, D)` and the proof of each write is the sequence of its `Absorb` calls, one per piece of the frame, with no lemma in between; the zero bytes of `Write0` are absorbed one at a time against a recursive `Add_Zeros`. (Equality of two sequences built by different concatenations needs an extensional lemma that the provers did not close within the step budget; the frames are therefore defined in the shape the writes produce.) The generic glue states the same for `Write_Element` and `Write_Element_Slice` (with `F.To_Bytes` of each element) and for `Write_Sumcheck_Statement` as the concatenation of the identifier frame, one element frame per public input, the zero element frame and the `Write0` frame, built by a ghost function `Statement_Bytes` that folds over the public inputs (npublic + 3 frames; four only for the one-input circuits of Appendix B.3). What is proved is that the bytes handed to SHA-256 are the encoding of Section 3.2; what SHA-256 does with them is tested (ADR 0029).
- **`FsPrf`**: the block input is the 16-byte little-endian encoding of the counter (Gold trivially, stated on the ghost model of the input block); `Counter <= 2^40` is a predicate of the generator state, and the postcondition of a refill says that below the bound the counter advances by one and at the bound the output block is zero and `Exhausted` is raised ([ADR 0028](0028-stage-4-scope-and-challenge-replay.md)). The bound is not a precondition anywhere, so the unbounded loops of [ADR 0030](0030-literal-rejection-sampling.md) have nothing to establish about it; `Exhausted` is sticky (every postcondition of the transcript carries `Exhausted'Old implies Exhausted`).
- **Silver with proved shape**: `Get_Random_Bytes` (the generator is reset on every write and seeded from the digest when absent: stated as a Boolean ghost "generator live" flag and its transitions, not as a property of the bytes); `Replay_Challenges` fills a `Challenges` record with `Last + 1 = Chal_Total (C)`, all 40 g values and `Alpha_Input`, the per-layer blocks at `Chal_Off (C, J)`, and returns `Ok` exactly when the transcript is not `Exhausted` on exit; the proof reader produces `Proof_Total (C)` elements in the pad order of Section 6.5 or reports failure. `Sha256` and `Aes256` are Silver.

The ghost model uses `SPARK.Containers.Functional.Infinite_Sequences` from the `sparklib` crate, pinned to the version matching the toolchain. The model is proof-only (amended at block 1): SPARKlib's lemma vocabulary (`Equal_Prefix` and the like) sits at its assertion level `SPARKlib_Full`, which depends on the level `Static` and can never be enabled at run time, so the ghost code that refers to it, `Bytes.Append` and every contract of `Transcript` that mentions `Absorbed`, is declared at that level too (`Ghost => SPARKlib_Full`, `Post => (SPARKlib_Full => ...)`). GNATprove proves it for all inputs; no build profile compiles it, not even the assertion-enabled test build of [ADR 0010](0010-assertion-enabled-test-project.md), and the absorbed sequence costs nothing at run time. The executable alternative, quantifying over positions, compiled but its loop invariant ran out of steps. What the test build checks about absorption is its output, the B.2 vectors byte for byte ([ADR 0032](0032-transcript-vectors.md)). Preconditions and the executable parts of postconditions (a result below n, distinct indices) stay at the default level and execute in the test build.

Tested, not proved: that the digest seeds the generator as the draft says, that the keystream is AES-256 in counter mode, that the extracted values are the draft's (Appendix B.2, byte for byte), that the replayed challenges are the upstream verifier's (Appendix B.3 against the recorded runs); see [ADR 0032](0032-transcript-vectors.md).

## Alternatives considered

- **A bounded ghost byte array with a fixed capacity.** Rejected: `write0` of the term count makes the absorbed length a function of the circuit, so the capacity would cap the circuits the contracts speak of, or every contract would carry a capacity discriminant.
- **Modelling only the absorbed length, or the last frame written.** Rejected: too weak; a swapped tag between the element and the slice frame, or a length written big-endian, would prove, and those are exactly the errors the perimeter is meant to exclude.
- **Gold on the digest or on the generated bytes.** Not possible without a formal specification of SHA-256 and AES, which ADR 0029 declines; the vectors cover it.
- **A functional sequence written in the project instead of SPARKlib.** Rejected: SPARKlib's containers come with their own proofs and lemmas and are the library GNATprove is tested against; writing a sequence with the same contracts would be a stage of its own.
- **No Gold on the codec (Silver plus B.2 vectors).** Rejected: the vectors exercise one frame of each kind; the structural proof covers every length and every count, and it documents the encoding in the contracts where a reader looks for it.

## Consequences

- A new dependency, `sparklib`, pinned in `alire.toml`; ghost-only use, no executable code of the library depends on it. The hosted gate installs it through Alire as it does `gnatprove`.
- The Gold statements of the codec are the project's written form of the absorption checklist: a reader can compare the frames in the contracts with Section 3.2 and the order in `Replay_Challenges` with `zk/verifier.rs` line by line.
- Chapter 4 explains functional containers, ghost package state and assertion levels on first use.
- One transcript at a time: a program that needs two (a prover and a verifier in one process, phase C) drives them in sequence; SPARK library code has no tasking, so nothing is lost.

## Verification impact

- Provable: the properties listed above, for all inputs, on both instances of the glue; absence of run-time errors everywhere.
- Tested: everything about the values of digests, keystream bytes and extracted elements ([ADR 0032](0032-transcript-vectors.md)).
- Trusted: SPARKlib's functional sequences as a model (their contracts are AdaCore's and are used here as given, the same standing as `Big_Integers` in [ADR 0014](0014-p256-functional-specification-and-ghost-model.md)); SHA-256 and AES-256 beyond the vectors (ADR 0029).
- Constant time: not applicable (ADR 0029).

## References

- draft-google-cfrg-libzk-03, Sections 3.1.1, 3.2, 3.4.1, 3.4.2, 3.4.3, 6.5, 7.3.
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/transcript.rs`, `zk/common.rs`, `zk/verifier.rs`.
- SPARK User's Guide, "Functional containers" and "SPARK Library"; the Alire crate `sparklib` 16.1.0 (AdaCore/SPARKlib).
- [ADR 0003](0003-proof-policy-and-trust-model.md), [ADR 0014](0014-p256-functional-specification-and-ghost-model.md), [ADR 0023](0023-gold-perimeter-for-protocol-code.md), [ADR 0028](0028-stage-4-scope-and-challenge-replay.md), [ADR 0029](0029-sha256-and-aes256-in-spark.md), [ADR 0030](0030-literal-rejection-sampling.md).
