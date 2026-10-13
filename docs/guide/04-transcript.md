# Chapter 4: the Fiat-Shamir transcript and the challenge replay

Stage 4 of Phase A. Outline; the sections are written as the blocks of the stage land. The transcript of draft Section 3 (`Transcript`, with `Sha256` and `Aes256` under it), the field serialisation and sampling through `Field_Signature`, and the generic glue `Sumcheck_Transcript` that replays the challenges of a proof into the `Challenges` record of chapter 3. Decisions: [ADR 0028](../adr/0028-stage-4-scope-and-challenge-replay.md) to [ADR 0032](../adr/0032-transcript-vectors.md). This chapter follows the shape of the first three.

## 1. The mathematics

### 1.1 Fiat-Shamir: from an interactive protocol to a proof string

What the verifier's randomness is replaced with, why every public element must be absorbed before the challenge that depends on it, and what an omission costs (the Frozen Heart class).

### 1.2 Absorb and squeeze: a hash accumulator and a pseudorandom generator

SHA-256 as the accumulator, the digest as the seed of AES-256 in counter mode, why the generator is discarded on every write (Section 3.1).

### 1.3 Rejection sampling: naturals below n, subsets, field elements

The mask of `nat`, Fisher-Yates for `choose`, canonical elements for P-256 and raw coefficients for GF(2^128); why termination is probabilistic (Section 3.4).

### 1.4 Why the statement is absorbed before anything else

Correlation intractability and `write0` of the term count (Section 3.3).

## 2. The algorithms

### 2.1 The TLV codec of Section 3.2

The three frames, their tags, the eight-byte little-endian lengths; the label as the first frame.

### 2.2 FsPrf: AES-256 in counter mode

The 16-byte little-endian counter from zero, the kept partial block, the 2^40 bound.

### 2.3 nat and choose, step by step

With the B.2.4 and B.2.5 vectors as worked examples.

### 2.4 The transcript of a sumcheck proof

Label, root, statement, `begin_circuit`, per layer `begin_layer`, rounds, `end_layer`, `alpha_input`: the absorption checklist, line by line against `zk/verifier.rs`.

### 2.5 Reading the sumcheck proof from bytes

The order of Section 7.3 against the pad order of Section 6.5; root and sumcheck part in a complete proof (Section 7.5).

## 3. The Ada/SPARK implementation

### 3.1 Bytes, Sha256 and Aes256: byte arrays, rotations and tables

`Unsigned_32` rotations and shifts, packed byte arrays, constant tables; the incremental context as an in-out record.

### 3.2 Transcript: a package with state, and the ghost absorbed sequence

Abstract state and refined state, a ghost global as the model, functional sequences from SPARKlib on first use; assertion levels, and why the model is proof-only (GNAT 16 has no ghost record components, SPARKlib's lemmas are never executable).

### 3.3 Field_Signature extended: Serialized_Size, To_Bytes, From_Bytes, Sampling_Rejects

The new formals, `GF2_128.To_Bytes` and `From_Bytes`, the shared `Bytes` package and the renaming in `P256_Field`.

### 3.4 Procedures that may not terminate: Always_Terminates

The implicit aspect, its conditional form, how the condition propagates to the callers, and why `Nat` and `Sample` are procedures.

### 3.5 Sumcheck_Transcript: the generic glue and Replay_Challenges

Sample, the frames over elements, the statement, the protocol helpers, the replay into `Challenges`.

### 3.6 Errors as status

The proof reader's status; the sticky `Exhausted` flag of the generator after 2^40 blocks, where the reference panics, and how `Replay_Challenges` reports it; nothing raises.

## 4. What the proofs guarantee

### 4.1 Structural Gold on the codec, Gold on nat, choose and the sampler

What "the absorbed bytes are the encoding of Section 3.2" does and does not say; the statement as npublic + 3 frames; the precondition `k <= n` of `Choose`.

### 4.2 Silver on SHA-256 and AES-256, and what stays tested

### 4.3 The verification condition table

Per package and per instance of the glue, with step counts, at the closing commit of the stage.

## 5. What is only tested

### 5.1 Appendix B.2 reproduced in full

### 5.2 Appendix B.3 end to end against the recorded upstream runs

### 5.3 NIST vectors for SHA-256 and AES-256; the GF(2^128) encoding

### 5.4 Errata of draft-03 found at this stage

## 6. What stays trusted, and the limits

SHA-256 and AES-256 beyond the vectors; termination of `Nat` and of the P-256 sampler; SPARKlib's functional sequences as a model; the completeness of the absorption beyond the B.3 vectors; the constant-time exemption and its scope.
