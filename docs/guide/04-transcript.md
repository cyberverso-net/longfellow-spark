# Chapter 4: the Fiat-Shamir transcript and the challenge replay

Stage 4 of Phase A. The transcript of draft Section 3 (`Transcript`, with `Sha256` and `Aes256` under it and `Fisher_Yates` beside it), the field serialisation and sampling through `Field_Signature`, and the generic glue `Sumcheck_Transcript` that replays the challenges of a proof into the `Challenges` record of chapter 3 and reads the sumcheck part of a proof string. Decisions: [ADR 0028](../adr/0028-stage-4-scope-and-challenge-replay.md) to [ADR 0032](../adr/0032-transcript-vectors.md). This chapter follows the shape of the first three.

## 1. The mathematics

### 1.1 Fiat-Shamir: from an interactive protocol to a proof string

The sumcheck protocol of chapter 3 is interactive: after each prover message the verifier sends a random challenge, and soundness rests on the challenge being unpredictable when the message was fixed. Fiat-Shamir removes the verifier: the prover computes each challenge as a hash of everything exchanged so far, and the verifier recomputes the same hashes from the proof string. The security argument needs the hash to behave like a random oracle on *the whole transcript*: every public element that the prover could choose after seeing a challenge must be absorbed before that challenge is derived. An element left out is not a crash and not a type error; it is a proof system in which the prover picks that element last and forges at will (the "Frozen Heart" class). Nothing in this chapter is proved against that mistake. What exists is the absorption checklist of ADR 0028, written as the sequence of calls in `Replay_Challenges`, compared line by line with the reference implementation, and the end-to-end vectors of Section 5, which catch any divergence from the reference on the two published proofs.

### 1.2 Absorb and squeeze: a hash accumulator and a pseudorandom generator

The draft's transcript (Section 3.1) is a duplex: SHA-256 accumulates the absorbed bytes; when a challenge is requested the digest of everything absorbed so far seeds a generator, AES-256 in counter mode (`FsPrf`, Section 3.1.1), whose keystream is cut into challenges; any further write discards the generator, so the next request reseeds from a digest that includes the new bytes. Two consequences shape the code. A request never consumes more of the digest than it needs: unread bytes of a keystream block are kept for the next request, and the draft's test vectors depend on this. And the hash state must survive the digest: the reference clones the accumulator to compute the seed (`get_hash`), which is why `Sha256.Digest` is a function of the context and leaves it untouched.

### 1.3 Rejection sampling: naturals below n, subsets, field elements

A uniform natural below n (Section 3.4.1) is drawn by reading as many bytes as n has, masking to the smallest all-ones value that covers n, and retrying while the result is not below n; the mask keeps the rejection probability at or below one half. A subset of k distinct indices below n (Section 3.4.2) is the first k entries of a Fisher-Yates shuffle driven by such draws. A field element (Section 3.4.3) is the serialised size of the field in bytes, read as an element: for GF(2^128) every 16-byte string is an element and nothing is rejected; for P-256 a 32-byte string is rejected when its little-endian value is at or above p, with probability about 2^-32. Each rejected attempt consumes bytes, so the number of attempts is part of the transcript: an implementation that capped the loop would produce different challenges from the reference whenever the cap was hit. The loops are therefore literal and unbounded, and their termination is a probabilistic fact, not a proved one ([ADR 0030](../adr/0030-literal-rejection-sampling.md)).

### 1.4 Why the statement is absorbed before anything else

Section 3.3 absorbs, before any challenge, the commitment root, the statement (circuit identifier, public inputs) and a run of zero bytes as long as the circuit has terms (`write0`). The zeros cost nothing to a honest party and bind the oracle's computational depth to the size of the circuit, which is what the correlation-intractability argument of the draft needs against self-referential provers. The code treats them as any other frame.

## 2. The algorithms

### 2.1 The TLV codec of Section 3.2

Three frames, each a tag byte followed by its payload: a byte array is `0x00`, the length as eight little-endian bytes, the bytes; a field element is `0x01` then its serialisation (the length is fixed by the field); an array of elements is `0x02`, the count as eight little-endian bytes, the serialisations in order with no per-element tag. `write0 (n)` is the byte array frame around n zero bytes. A transcript starts from a label absorbed as a byte array frame. Tags and lengths are absorbed like payloads and discard the generator like them.

### 2.2 FsPrf: AES-256 in counter mode

Block i of the keystream is AES-256 under the seed of the 16-byte little-endian encoding of i, from 0. The reference refuses to go past 2^40 blocks with an assertion; this implementation sets a sticky `Exhausted` flag instead and returns zero bytes from then on, so that a replay reports the condition as a status rather than failing ([ADR 0028](../adr/0028-stage-4-scope-and-challenge-replay.md)). No proof reaches it: a draw takes at most three blocks and the longest run of draws between two writes is the eighty of `begin_circuit`.

### 2.3 nat and choose, step by step

For `nat (256)`, Appendix B.2.4: n has two bytes, the mask is `0x1FF` (the mask covers n itself, not n - 1, so for a power of two exactly half the draws are rejected), two bytes are read little-endian, masked, and accepted when below 256; the draft's results 100, 189, 3, 92 for the four calls after the string `nats` are what the harness reproduces. For `choose (31, 20)`, Appendix B.2.5: the array 0 .. 30, then twenty steps j = i + nat (31 - i), swap a (i) and a (j), take a (i); the draft's list starts 10, 29, 30, 11.

### 2.4 The transcript of a sumcheck proof

`zk/verifier.rs` and `sumcheck/common.rs` of the reference fix the order, and `Replay_Challenges` follows it: the label; the commitment root as a byte array; the statement (the 32-byte circuit identifier as a byte array, each public input as its own element frame, the zero element, `write0` of the term count over all layers); `begin_circuit` (MAX_LOGW = 40 draws discarded, reserved by the draft, then 40 draws, the output-binding challenges g); then per layer `begin_layer` (alpha, then beta), for each round and each hand `round_poly` (the padded p (0) and p (P2) of that hand as two element frames, then one draw), `end_layer` (the two padded claims as one array frame); after the last layer one draw, `alpha_input`. Everything the Ligero verifier does after that is phase B and continues the same transcript.

### 2.5 Reading the sumcheck proof from bytes

Section 7.3 serialises, per layer, per round the four elements l (P0), r (P0), l (P2), r (P2), then the two claims, with no length prefix: the layout is given by the circuit. The verifier core wants the pad order of Section 6.5, hand h of round r at 4 r + 2 h and 4 r + 2 h + 1, so the reader permutes the four elements of each round (slots 0, 2, 1, 3). In a complete proof (Section 7.5) the root is the first 32 bytes and the sumcheck part follows; the Ligero proof after it is phase B.

## 3. The Ada/SPARK implementation

### 3.1 Bytes, Sha256 and Aes256: byte arrays, rotations and tables

`Bytes` declares the one byte array of the protocol code, `Byte_Array`, indexed from 0 to `Natural'Last - 1` so that the length of any array fits an `Integer` (the ghost model converts it to a big integer without a range check), with the fixed subtypes `Bytes_8`, `Bytes_16`, `Bytes_32`, `Bytes_64`. `P256_Field` keeps its own `Byte_Array` as a subtype of this one, so its stage 2 contracts did not move. `GF2_128` gains `To_Bytes` and `From_Bytes` on the same pattern as P-256 (`Limb_Of_8`, `Limbs_Of_Bytes`, `Bytes_Of_Limbs`, 16 bytes little-endian), Gold on that model, with `Ok` always True since every 16-byte string is an element.

`Sha256` is FIPS 180-4 over `Unsigned_32` with `Rotate_Right` and `Shift_Right` from `Interfaces`; the context holds the state, a 64-byte block buffer, its fill and a modular byte counter; `Update` feeds bytes one at a time and compresses when the buffer fills; `Digest` pads a copy and returns the 32 bytes big-endian. `Aes256` is FIPS 197 with the state as 16 bytes column-major, the S-box as a constant table indexed by `Unsigned_8` (generated from its definition by the vector generator, not copied), the key schedule as fifteen round keys, `Xtime` with a data-dependent conditional. Both are Silver: absence of run-time errors and termination for every input; that they compute SHA-256 and AES is tested ([ADR 0029](../adr/0029-sha256-and-aes256-in-spark.md)). The constant-time discipline of chapter 1 is declared not applicable to them and to the transcript: the data are the public content of a proof string, and the headers say so.

Three small lessons of the proof. Flow analysis does not see an array initialised by two loops or by four statements per iteration: the schedule and the output are zeroed first. A computed shift amount in `Unsigned_8 (Shift_Right (W, 24 - 8 * J) and 16#FF#)` and the mask itself cost the provers more than the literal shifts and `mod 256` the code now uses. And the padding loop of `Digest` needs a postcondition on `Put` about the fill count, or its variant cannot be proved.

### 3.2 Transcript: a package with state, and the ghost absorbed sequence

`Transcript` is a package with state, not a type: `Abstract_State => State` names, in the spec, the executable state that the body refines into the hash context, the generator (key schedule, block counter, current block, unread bytes), the `Live` and `Exhausted` flags. One transcript exists at a time; `Reset (Label)` starts a new one. The reason is the model. The Gold statements of this stage say what bytes reached SHA-256, and the natural model is a sequence of bytes that every write extends: `Absorbed`, a *functional sequence* from SPARKlib (`SPARK.Containers.Functional.Infinite_Sequences`, instantiated on `Unsigned_8` in `Bytes`): a mathematical value with no capacity and extensional equality, so that `write0` of a term count absorbs as many zeros as the circuit has terms without any array capping the circuits the contracts speak of. The first design put that sequence inside `Sha256.Context` as a *ghost record component*; GNAT 16 has no such thing, and a ghost object has to be a variable, hence package state ([ADR 0031](../adr/0031-transcript-gold-perimeter.md), amended).

The model is appended to in exactly two places, `Absorb` and `Absorb_Byte` in the body, which are also the only two calls of `Sha256.Update`; every write is a sequence of such calls and its postcondition states the frame it produced: `Logical_Eq (Absorbed, Bytes_Frame (Absorbed'Old, D))`, where `Bytes_Frame (S, D)` is the ghost function "S, then the tag, then the eight length bytes, then D", written with `Add` and `Append` in the order the bytes are absorbed. `Zero_Frame` ends in `Add_Zeros`, recursive on the count, and `Write0` absorbs its zeros one byte at a time so that each iteration is one unfolding of the definition. The equality is `Logical_Eq`, the logical equality of sequences, for the same reason chapter 3 uses `Same`: the extensional `"="` of SPARKlib gives the provers no congruence, and the proof of a frame is a chain of substitutions through three or four calls.

*Assertion levels.* SPARKlib declares its lemma vocabulary (`Equal_Prefix`, `Logical_Eq`, the postconditions of `Add` and `Get`) at an assertion level `SPARKlib_Full` that depends on the level `Static` and therefore can never be enabled at run time; ghost code that refers to it must sit at that level too. `Bytes.Append`, `Add_Zeros`, the frame functions, `Absorbed`, `Generator_Live` and every contract that mentions them are declared `Ghost => SPARKlib_Full` or written as `Post => (SPARKlib_Full => ...)`. Such a postcondition is proof-only: GNATprove proves it for all inputs, and no build profile compiles it, not even the assertion-enabled test build of chapter 1. A level aggregate may contain only level associations, so a postcondition cannot mix an executable part with the model; `Nat` and `Choose` keep plain, executable postconditions and never mention `Absorbed`, which their `Global` leaves unchanged. The `Runtime` level, the other predefined one, is checked *always*, even without `-gnata`, and is not used.

`Generator_Live` and `Is_Exhausted` are the proved shape of the squeeze side: a write leaves no generator live, a draw leaves one live, and `Exhausted` is sticky, stated as `Is_Exhausted'Old <= Is_Exhausted` on Booleans (the prefix of `'Old` must be evaluated unconditionally, so this conjunct comes first). Flow analysis does not see assignments at the `SPARKlib_Full` level, which is why `Reset` declares `Absorbed` as `In_Out` although it assigns it first.

### 3.3 Field_Signature extended: Serialized_Size, To_Bytes, From_Bytes, Sampling_Rejects

The signature package of chapter 3 gains four formals: the byte length of an element, the encoding, the decoding as a procedure with an `Ok` flag (exactly the canonical encodings of Section 7.2.1: below p for P-256, every string for GF(2^128)), and the Boolean `Sampling_Rejects`. The actuals take the field's fixed subtype (`Bytes_32`, `Bytes_16`) while the formals say `Byte_Array`; this is mode conformance, legal for formal subprograms, and the glue always passes arrays of `Serialized_Size` bytes indexed from 0. The provers do not see `Serialized_Size` as 32 or 16 in the instances (it reaches them through two formal packages), so a product with it is nonlinear arithmetic: the reader's one such step, "element k of n fits in n times the size", is a lemma of its own proved from `Lemma_Mult_Is_Monotonic` of `SPARK.Lemmas.Integer_Arithmetic` on big integers.

### 3.4 Procedures that may not terminate: Always_Terminates

GNATprove 16 treats every subprogram as carrying an implicit `Always_Terminates` and reports termination as a check. A procedure may declare `Always_Terminates => False`, or a Boolean condition, to say that termination is not claimed; a function may not, because a non-terminating function would be an unsound axiom. `Nat` and `Choose` carry `False` and are procedures for that reason; `Sample` of the glue, and everything that calls it (`Begin_Circuit`, `Begin_Layer`, `Round_Poly`, `Replay_Challenges`), carry `not SA.F.Sampling_Rejects`: the GF(2^128) instance is proved terminating, the P-256 instance is declared possibly non-terminating, and the condition is the same text in both. Inside `Sample` the rejection loop sits under `if SA.F.Sampling_Rejects`, so that in the instance where the condition is statically False the loop is unreachable and the termination check closes. Absence of run-time errors is proved inside the unbounded loops regardless: each iteration is safe, only their number is open.

### 3.5 Sumcheck_Transcript: the generic glue and Replay_Challenges

The glue is generic over the three stage 3 instances of a field (`Sumcheck_Algebra`, `Sumcheck_Expression`, `Sumcheck_Verifier`), because it fills `Sumcheck_Verifier.Challenges` and `Sumcheck_Proof` and needs their offsets `Chal_Off` and `Proof_Off`. `Sample` is the sampler of Section 3.4.3 for both fields. `Write_Element` and `Write_Element_Slice` put the frames over `To_Bytes`; `Serialise` concatenated a slice of elements with a postcondition on its layout, until chapter 5 replaced it by absorbing a slice one element at a time. `Write_Sumcheck_Statement` has the postcondition `Statement_Frame (Absorbed'Old, Id, C, Pub)`, the four frames of Section 3.3 with the public inputs folded by the recursive `Publics_Frame`, which is what ADR 0031 calls the statement being npublic + 3 frames. `Begin_Circuit`, `Begin_Layer`, `Round_Poly` and `End_Layer` are the four helpers of `sumcheck/common.rs`, the last two Gold on their frames (`Claims_Pair` names the two-element array so that postcondition and body speak of the same term).

`Replay_Challenges` drives them in the order of Section 2.4 and fills the record. Each layer goes through `Replay_Layer` with indices relative to the layer's blocks (a slice of the proof in, a block of challenges out), so that the index checks are linear in logw and the transcript contracts weigh on one short loop; the outer loop uses the step and monotonicity lemmas of chapter 3's offsets, copied here with `Unhide_Info`, to place each block. `Read_Sumcheck_Proof` walks the bytes in the order of Section 7.3 and writes the pad order; `Take` reads one element and the status becomes `Bad_Element` on the first non-canonical encoding, as `read_elt_field` fails upstream.

One more lesson of the proof, the sharpest of the stage: the two recursive ghost functions `Add_Zeros` and `Publics_Frame` were first left visible, and a term `Add_Zeros (S, C.NT)` in the context of `Replay_Challenges` let the provers unfold the definition without bound, so that even `LC'First = 0` for an array declared `(0 .. 2 * Logw + 1)` ran out of steps, and five times the budget did not help. Hidden (`Hide_Info` at the declaration, `Unhide_Info` in the one body that steps them), everything proved at once. Chapter 3 had recorded the same rule for `Off`; it holds for every recursive ghost definition. A nonlinear product in a *precondition* has the same effect on every verification condition of the subprogram, so the reader's length condition is stated on machine integers and only the lemma speaks in big integers.

### 3.6 Errors as status

Nothing raises. `Read_Sumcheck_Proof` returns `Ok` or `Bad_Element`; `Replay_Challenges` returns `Ok` or `Exhausted`, the generator's bound of Section 2.2 rendered as an outcome; the sizes of the records are preconditions, established by the caller from the circuit as in chapter 3.

## 4. What the proofs guarantee

### 4.1 Structural Gold on the codec, Gold on nat, choose and the sampler

"The absorbed bytes are the encoding of Section 3.2" means: for every input, after each write of `Transcript` the model sequence is the old sequence followed by exactly the frame of that write (tag, eight little-endian length bytes, payload; or tag and element; or tag, eight count bytes and the concatenated elements), and after `Write_Sumcheck_Statement` it is the old sequence followed by the identifier frame, one element frame per public input, the zero element frame and the zero run of the term count; and the model is appended to only where `Sha256.Update` is called, with the same bytes. It does not say what SHA-256 does with those bytes, nor that the keystream is AES-256 of the counter, nor that `Replay_Challenges` absorbs everything the protocol requires: the first two are tested against NIST and Appendix B.2, the third against the upstream verifier on Appendix B.3 (Section 5). `Nat` returns a value below n, with the mask and byte length of Section 3.4.1 as loop invariants; `Choose` returns k distinct indices below n, from the permutation invariant of the Fisher-Yates array (every entry below n, no two equal, preserved by each swap) kept in `Fisher_Yates` where the draws arrive as data and the proof context is light; the P-256 sampler returns a canonical element by the type's predicate, through `From_Bytes` with `Ok`. All of it holds on exit, whenever the loop exits (ADR 0030).

### 4.2 Silver on SHA-256 and AES-256, and what stays tested

`Sha256` and `Aes256` are Silver: no run-time error and termination on every input, which for byte-oriented kernels is the whole of the proof obligation (indices, shifts, modular arithmetic). Their functional correctness is not proved: a formal specification would be a transcription of FIPS 180-4 or FIPS 197 in ghost code, and the gap between that transcription and the standard would still be closed by vectors, so the vectors close the whole gap at once ([ADR 0029](../adr/0029-sha256-and-aes256-in-spark.md)). A wrong digest gives wrong challenges, which the end-to-end vectors detect.

### 4.3 The verification condition table

GNATprove 16.1 with the project's prover configuration ([ADR 0020](../adr/0020-prover-configuration-step-budget.md)), the whole project at the close of stage 4: 7810 checks, all proved, no justification, no `pragma Assume`, against 6811 at the end of stage 3. Maximum steps for a single successful proof unchanged at 429702 (a P-256 lemma); the stage 4 maximum is 138943, in the P-256 instance of the glue.

| Category | Checks | Discharged by |
|----------|--------|---------------|
| Data dependencies (`Global`) | 360 | flow analysis |
| Initialization | 135 | flow analysis |
| Non-aliasing | 1 | flow analysis |
| Run-time checks (indices, ranges, overflow, predicates, discriminants) | 4458 | Z3 70%, 27% trivial, CVC5 3% |
| Assertions (`pragma Assert`, loop invariants, variants) | 644 | Z3 82%, CVC5 11%, Alt-Ergo 4%, 4% trivial |
| Functional contracts (postconditions, lemma postconditions, preconditions at calls) | 1917 | Z3 90%, CVC5 8%, Alt-Ergo 1% |
| Termination | 294 | 231 flow, 63 provers |

Proof checks by unit of stage 4 (flow excluded): `Bytes` 89 (`Append` and the recursive model), `Sha256` 12, `Aes256` 33, `Transcript` 87, `Fisher_Yates` 48, `GF2_128` 40 with the serialisation, the glue 260 in the P-256 instance and 233 in the GF(2^128) one; the P-256 instance costs more because every `Element` carries the canonical-form predicate, as in chapter 3. Which of CVC5 and Z3 is credited with a check varies from run to run; this run credits Z3 with most of the project.

Lessons from closing these proofs, in addition to those of chapter 3:

- A recursive ghost definition left visible in a caller's context is a matching loop: hide it at the declaration and unhide it in the one body that steps it. The rule is not specific to `Off`.
- Logical equality (`Logical_Eq`, `Same`) is the equality to state structural contracts with; the extensional equality of SPARKlib's containers, like the predefined equality of records with arrays, gives no congruence.
- SPARKlib's lemma vocabulary is proof-only (`SPARKlib_Full`); ghost code that uses it goes to that level, and such contracts never execute. A postcondition with levels is all-or-nothing, and `Runtime` is always checked.
- A nonlinear product in a precondition weighs on every check of the subprogram; a product with a constant the provers cannot see (a formal object through formal packages) is nonlinear.
- Two `out` arguments that are components of the same array alias; `'Loop_Entry` needs an object, not a function call; a subtype constraint may not depend on a variable, so make the bound a constant of the block.
- The Why3 session returns stale "unproved" results after a change, twice in this stage with dozens of false failures; `gnatprove --clean` before any diagnosis, without exception.

In plain terms, for every input, not on samples: no run-time error occurs in any stage 4 package; every write of the transcript hands SHA-256 exactly the frame of Section 3.2, and the statement exactly the frames of Section 3.3; `Nat` is below n, `Choose` is k distinct indices below n, the P-256 sampler returns canonical elements; the generator is live after a draw and not after a write, and exhaustion is sticky; `Replay_Challenges` fills a record of the stage 3 shape or reports exhaustion, and the reader produces the pad order or reports a bad element; every subprogram terminates except `Nat`, `Choose` and the P-256 sampler and their callers in the P-256 instance, which are declared.

Reproduce with `make prove`.

## 5. What is only tested

### 5.1 Appendix B.2 reproduced in full

`gen_transcript_vectors.py` contains an independent transcript written from the draft's text (SHA-256 from `hashlib`, AES-256 from scratch with the S-box computed from its definition, the counter mode, the codec, `nat`, `choose`, the prime-field sampler) and the constants of Appendix B.2 copied from the draft: the prime of the 4-word field, which is the secp256k1 prime, so that no 32-byte draw is rejected in these vectors (probability about 2^-224); the 48 field elements of B.2.1 to B.2.3, printed as big-endian integers; the 24 `nat` results of B.2.4; the six `choose (m, 20)` lists of B.2.5. It replays the five chained steps, aborts on any mismatch, and writes `transcript_fs.txt` as a script: `reset`, `write_bytes`, `write_elt`, `write_slice`, `elt`, `nat`, `choose` lines that the harness `transcript_kat` executes in order on the library's transcript, with a harness-only sampler for the B.2 field (32 bytes little-endian, rejected at or above p, so that byte consumption is the draft's). 78 cases, byte for byte. Together with the 8 SHA-256 cases (FIPS 180-4 examples, CAVP short messages) and the 5 AES-256 cases (FIPS 197 Appendix C.3, the counter blocks of SP 800-38A F.5.5 as single-block encryptions), 91 cases.

### 5.2 Appendix B.3 end to end against the recorded upstream runs

Appendix B.3 gives two complete proofs for the explicit circuits of chapter 3. The generator copies their roots and sumcheck parts from the "Complete Proof Serialization" blocks (the first 32 bytes, then 768 bytes for B.3.2 and 384 for B.3.3), with the labels of the upstream unit tests and the all-zero circuit identifier they use, reads the sumcheck part into the pad order and compares it with the padded proof of the tier 3 recording of the same circuit (chapter 3, Section 5.3), replays the transcript of Section 2.4 with its own transcript and compares every challenge, g, alpha, beta, every round challenge and `alpha_input`, with the recording; it aborts on any mismatch and writes `zk_proof_p256_b3_2.txt` and `zk_proof_gf2_128_b3_3.txt`. The harness `sumcheck_kat` reads these before the recordings and, at the end of each tier 3 block, checks that `Read_Sumcheck_Proof` produces the recorded padded proof, that `Replay_Challenges` reproduces the recorded challenges, that `Verifier_Core` on the replayed record emits the constraints it emitted on the injected one, and, for P-256, that a proof with an element at or above p is refused. 11 checks on the two circuits; a tier 3 block without its proof file is a failure.

### 5.3 NIST vectors for SHA-256 and AES-256; the GF(2^128) encoding

The NIST cases are copied constants, recomputed by the generator before being written and checked by `transcript_kat` against the library, once in a single `Update` and once byte by byte with the digest taken twice. The GF(2^128) encoding of Section 7.2.1 is anchored on the draft by `gf2_128_bytes.txt`: the first sumcheck element of B.3.3, whose bytes come from the complete serialisation and whose value from the tier 3 recording, agrees with `To_Bytes` only for the little-endian order; the sixteen subfield basis constants and eight structural cases follow (25 cases in `gf2_128_kat`).

### 5.4 Errata of draft-03 found at this stage

Section 3.4.3 and the description of B.3.2 call P-256 a "scalar field"; the prime used throughout is the base field prime (chapter 3, Section 5.4). The "Sumcheck Proof (hex)" block of Appendix B.3.3 is missing from the TXT and HTML renderings of the draft ("artwork only available as TXT"), while B.3.2's is present; the sumcheck parts of both proofs are therefore taken from the complete serialisations, whose layout Section 7.5 fixes and whose sizes confirm (32 + 768 + 4652 = 5452 bytes and 32 + 384 + 2632 = 3048). Both are recorded in ADR 0032 and reported with the errata of chapter 3.

## 6. What stays trusted, and the limits

- That `Sha256` and `Aes256` compute SHA-256 and AES-256 on inputs the vectors do not cover (ADR 0029).
- Termination of `Nat` and of the P-256 sampler, and of everything that calls them in the P-256 instance: a probabilistic property, at most one half per attempt for `nat` and below 2^-32 for P-256, declared with `Always_Terminates` and not proved (ADR 0030).
- SPARKlib's functional sequences as a model, with the same standing as `Big_Integers` in chapter 2: their contracts are AdaCore's and are used as given (ADR 0031).
- The completeness of the absorption beyond what the two B.3 proofs exercise: the sequence of calls in `Replay_Challenges` is the checklist, compared with the reference by reading; a public element the protocol should absorb and the reference also omits would pass every test here.
- The constant-time exemption of the transcript, the hash and the cipher: justified by the data being public, and void if a future use ever gives them a secret (ADR 0029).
- That the draft's vectors were produced by the protocol the draft describes, and that the tier 3 recordings are faithful (chapter 3).

Limits of this stage: one transcript at a time, driven in sequence by a program that needs two; `Choose` bounds n to 2^16 (the largest of B.2.5) because the shuffle's array lives on the stack, to be raised when Ligero needs more; `Write_Element_Slice` bounds a slice to 4096 elements for the same reason; the reader covers the sumcheck part only, the Ligero proof after it being phase B; and exhaustion of the generator, while reported, is a status no caller can recover from except by rejecting the proof.
