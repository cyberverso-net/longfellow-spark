# Trust model

Every claim this project makes about its code falls into one of three groups ([ADR 0003](../adr/0003-proof-policy-and-trust-model.md)):

- **Proved.** GNATprove has shown it for every possible input.
- **Tested.** It holds on the committed test vectors, which come from sources outside this repository.
- **Trusted.** It is assumed. We list it here so that nothing is assumed silently.

A fourth group covers what SPARK cannot express at all, such as soundness or constant time, and says what stands in for a proof there.

The [verification approach](verification-approach.md) explains why the line falls where it does. Each package header gives the same information for its own subprograms. If a header and this page disagree, the header is the one to fix.

## In short

- No run-time error is possible anywhere in the SPARK code, for any input. This is the Silver level, and it holds for the whole project.
- The arithmetic of both fields is proved equal to a simple reference written for clarity. That the reference is the one the specification means is tested.
- The building blocks of the verifier and the prover are proved against transcriptions of the specification's formulas. That those formulas fit together into a sound protocol is a theorem of the protocol, not something SPARK can prove.
- The verifier accepts the proofs the upstream prover makes. The prover reproduces upstream's proofs byte for byte. Both facts are tested.
- The toolchain, the specification, the operating system's random generator and the circuit files are trusted.
- No check is justified away and no `pragma Assume` is used. Full functional correctness of the whole system (Platinum) is not a goal.

## What is proved

**Everywhere.** Every SPARK unit is Silver for all inputs: no overflow, no index out of range, no division by zero, no read of an uninitialised value. Units that use the heap also pass SPARK's ownership checks on every allocation. Gold, a proved functional contract, applies only where a package header declares it.

Many of these contracts are stated at the assertion level `Proof_Only`. GNATprove proves them, but they are never compiled into an executable, so the test harnesses check those units through their vectors.

**The two fields** (chapters 1 and 2).

- `GF2_128.Add`, `Xtime`, `Mul` and `Square` are proved. `Mul` and `Square` are proved equal to the ghost reference `Mul_Ref`.
- `P256_Field.Add`, `Sub`, `Neg`, `Mul`, `Square`, `Is_Canonical`, `From_Bytes` and `To_Bytes` are proved against a ghost integer model, `To_Int`, and a ghost prime `P`.
- `P` is defined from the limbs of p. The proof shows that it equals 2^256 - 2^224 + 2^192 + 2^96 - 1, as a polynomial identity in 2^32.

**The sumcheck algebra** (chapter 3, for each of the two fields).

- `Eq`, `Bindeq`, `Bind`, `Lagrange_Basis`, `Eval_Quad`, `Eval_Circuit`, `Bind_G`, `Eval_Bound_Quad` and every `Expression` operation are proved equal to a ghost reference. Each reference transcribes the draft's formula in a fixed order of operations. Equality is the logical equality `Same`.
- `Eval_Circuit` carries the semantics of the Z assertions. `Symbolic_Round` is the draft's formula by definition.
- `Verifier_Core` is Silver. It is proved to emit only terms the Ligero verifier can index, with the right pad indices for the quadratic triples.
- `Input_Constraint` is Gold against the formula of Section 6.7. Term W of the constraint has witness W and coefficient `Eq2 (npublic + W)`. The constant is the public binding, summed over the public inputs in order, minus the final claim. The last terms are the claim pads, built with the operations of `Expression` (Phase D, ADR 0056).
- These are structural proofs. They say nothing about the laws of the field. That `Bindeq` agrees with `Eq`, that the Lagrange basis interpolates, and that the constraints are the upstream verifier's, are all tested.

**The transcript** (chapter 4).

- The frames of `Transcript` and the statement of `Sumcheck_Transcript` are proved on a ghost sequence of the absorbed bytes.
- `Nat` returns a value below n. `Choose` returns distinct values below n.
- `GF2_128.To_Bytes` and `From_Bytes`, and the layout of `Serialise`, are proved.

**Ligero and the complete verifier** (chapter 5).

- `Merkle.Build` is proved against the recursive heap of the tree. `Merkle.Verify` accepts only when every index is below n, no index repeats and the proof is consumed exactly. The root is node 1 of the node model.
- `Ligero_Geometry.Make` is proved against `LigeroGeometry::new` and Section 4.2.1, with every row index in range.
- `Lagrange.Build` and `Evaluate` are proved against the Lagrange matrix at the queried columns. Every inverse they use multiplies back to one.
- `Ligero_Proof.Read` accepts only columns that follow the rules of Section 7.4.
- The three tests of `Ligero_Verifier` are proved against the combinations of Sections 4.4 and 4.5, through `axpy`, `vaxpy`, `dot` and `dot1`. The slice frames are proved by recursion.
- `Verifier_Core` emits only terms below `Witness_Count`.
- The two verifiers are Silver, and the status they return is proved to match its cause.

**The circuit loader** (chapter 6).

- `Uleb128.Read` returns the value of the one to four bytes it consumed.
- `Circuit_Reader.Read` returns, on `Ok`, a circuit that satisfies `Well_Formed` and whose identifier is the stored one. Otherwise it returns null.

**The prover** (chapter 7).

- The writers of Sections 7.3, 7.4 and 7.5 write exactly `Proof_Len` bytes. The Ligero part satisfies the reader's rules, `Well_Coded`, at the reader's offset, with the root first.
- `Round_Evals` is proved equal to a ghost transcription of `eval_round_poly`.
- In `Encode_Row`, the systematic part equals the row and the parity part equals `Lagrange.Evaluate`.
- Each row is placed in the tableau without touching the others. The witness slots of each row hold the witnesses, the values of the triples, or zeros.
- `Merkle.Open` produces exactly the digests `Merkle.Verify` consumes, stated in `Verify`'s own model.
- `Lqc_Triples` equals the core's layout. The pad layout gives `Witness_Count` as the private inputs plus `Pad_Total`.
- Every prover unit is Silver for any circuit, inputs, configuration and random byte stream. The subfield projection and `In_Subfield` are Silver.
- `Additive_Fft` is Silver for every row of up to 2^16 values, and `Extend` keeps the row as the first part of its output. In `Encode_Row`, the parity part is proved equal to the Lagrange evaluation only with the Lagrange encoder, which P-256 uses; on GF(2^128) it comes from the FFT and is tested (Phase D, ADR 0057).

## What is tested

The vectors live in `tests/vectors/`. Each generator is an independent Python program that aborts when its own anchors disagree with the external constants it embeds.

**The two fields.**

- `GF2_128.Mul_Ref`, and so `Mul`, follows the convention of the pinned specification: bit i is the coefficient of x^i, and reduction is by Q(x). The checks are in `gf2_128_mul.txt` and `gf2_128_square.txt`, run by `gf2_128_kat`.
- These files have three tiers. The anchors are checked against the subfield basis constants of upstream (google/longfellow-zk at d5e6be7, `gf2_128.rs` and `gf2_128_test.cc`). Structural cases come from the field definition. Random cases come from a Python reference built differently from `Mul_Ref`: a schoolbook product, then long division.
- `GF2_128.Inv` computes the inverse. `gf2_128_inv.txt` checks `Inv (beta_i) = g^(65535 - i)`, `E * Inv (E) = 1` on random elements and `Inv (Zero) = Zero`. Two Python references, Fermat exponentiation and the extended Euclid algorithm, must agree. The harness checks `E * Inv (E) = One` again at run time.
- The limbs of `P_Limbs` are the prime of Table 1, and the byte encoding is that of Section 7.2.1. The files `p256_add.txt`, `p256_mul.txt` and `p256_bytes.txt` are anchored on b, Gx and Gy of RFC 5903, through the curve equation.
- `P256_Field.Inv` is the inverse, by `p256_inv.txt`, with the same two references and the same run-time check.
- The generator `gen_p256_vectors.py` also re-derives the Solinas reduction table and the inversion chain.

**The sumcheck algebra.**

- The explicit circuits of draft Appendix B.3 use the term lists of the upstream unit tests. The errata of the appendix are in ADR 0027.
- The algebra is checked against an independent Python reference, in `sumcheck_gf2_128.txt` and `sumcheck_p256.txt`. The harness also checks the Lagrange constants by `d * inv (d) = 1`, and `Bindeq` against `Eq`.
- `Verifier_Core` agrees with the upstream verifier on recorded runs with injected challenges, in `tests/vectors/upstream/`. The recordings are produced outside this repository. The harness reads them when present.

**The transcript.**

- SHA-256 and AES-256 are checked against FIPS 180-4, CAVP, FIPS 197 and SP 800-38A.
- The transcript matches draft Appendix B.2 byte for byte, over 78 chained steps (`transcript_fs.txt`).
- The GF(2^128) encoding matches Appendix B.3.3 (`gf2_128_bytes.txt`).
- Challenge derivation is checked end to end. `Replay_Challenges` and the proof reader match the recorded upstream runs on the two Appendix B.3 proofs, both with injected and with replayed challenges. An independent Python transcript recomputes every value.

**Ligero and the complete verifier.**

- The Merkle tree matches Appendix B.1.1 and an independent reference. The vectors open every subset of trees with up to nine leaves, plus eight negative cases.
- The geometry and the Lagrange tables match an independent reference. The interpolation property is checked through a Vandermonde system.
- The proof reader is tested on subfield runs and on each of the rules of Section 7.4, broken one at a time.
- The Ligero verifier is checked step by step against recorded upstream runs on the two Appendix B.3 proofs: every challenge, every chosen column, and both sides of each test. The nonces match Appendix B.3.1.
- `Zk_Verifier` accepts the two complete proofs from the proof string, on both fields. It refuses the negative cases of ADR 0040 with the expected status.

**The circuit loader.**

- The LFC2 format is checked against an independent Python reader and writer, and against the two upstream circuit files. The identifier the generator computes must equal the one each upstream file stores.
- The Appendix B.3 circuits, written in LFC2 in two encodings, load term for term. Twenty-eight malformed files are refused with their status.
- The two proofs the upstream prover made, for `sha256` on GF(2^128) and `ecdsa2` on P-256, are accepted from their files. Changing one byte of the root, the sumcheck part or the Ligero part makes them fail with `Merkle_Failed`. This runs in the release build (`interop_kat`).

**The prover.**

- `longfellow_prove` reproduces the two upstream proofs byte for byte from their inputs, under the seeds of the upstream test. This is the exit criterion of Phase C.
- Proofs made under another seed, or with the system's random generator, are accepted by `longfellow_verify`.
- Piece by piece, the prover matches an independent Python transcription of the reference prover: the pads and padded sumcheck proofs, the Merkle roots, the unencoded rows and the openings of the commitment.
- The writers rewrite every proof in the repository identically.
- The complete proofs of the small circuits are accepted by `Zk_Verifier`. The statuses `input_length`, `not_satisfied`, `not_in_subfield` and `config_invalid` are each triggered. A prover with input checks turned off makes proofs of false statements, and the verifier refuses them.
- The sixteen masks of the subfield projection are checked on all 65536 subfield elements.
- The shape of the whole tableau is checked slot by slot (ADR 0052).
- The additive FFT gives the Lagrange codeword. A Python transcription of the upstream FFT is checked against barycentric Lagrange interpolation (`gen_fft_vectors.py`), `fft_kat` checks the Ada FFT on those vectors and against `Lagrange.Evaluate` on random rows, and the prover's commitments and the `sha256` proof stay those of the Lagrange encoder (Phase D).
- A proof file made by this project was verified by the upstream `ZkVerifier`, by hand, through `tests/vectors/upstream/verify_proof_file.rs`.

**Where the vectors are.**

| Area | Vector files | Generator | Harness |
|------|--------------|-----------|---------|
| GF(2^128) | `gf2_128_*.txt` | `gen_gf2_128_vectors.py` | `gf2_128_kat` |
| P-256 field | `p256_*.txt` | `gen_p256_vectors.py` | `p256_kat` |
| Sumcheck | `sumcheck_*.txt`, `upstream/sumcheck_core_*.txt` | `gen_sumcheck_vectors.py` | `sumcheck_kat` |
| Transcript | `sha256.txt`, `aes256.txt`, `transcript_fs.txt`, `zk_proof_*.txt` | `gen_transcript_vectors.py` | `transcript_kat`, `sumcheck_kat` |
| Ligero | `merkle.txt`, `ligero_geometry.txt`, `lagrange_*.txt`, `ligero_proof.txt`, `upstream/ligero_*.txt` | `gen_ligero_vectors.py` | `ligero_kat`, `sumcheck_kat` |
| Circuits | `circuit_summary.txt`, `circuit_lfc2.txt` | `gen_circuit_vectors.py` | `circuit_kat` |
| Additive FFT (Phase D) | `fft.txt` | `gen_fft_vectors.py` | `fft_kat` |
| mDoc circuits (Phase D) | `mdoc_summary.txt`, from the archives in `upstream/mdoc/` | `gen_mdoc_vectors.py` | `circuit_kat` |
| Interop | `interop.txt` | `gen_circuit_vectors.py` | `interop_kat` (release build) |
| Prover | `writer.txt`, `sumcheck_prover.txt`, `ligero_commit.txt`, `zk_prove.txt` | `gen_prover_vectors.py` | `writer_kat`, `prover_kat`; `make cli` for the byte identity |

The `upstream/` recordings are produced outside this repository, by the instrumented upstream code described in ADR 0027 and ADR 0040.

## What is trusted

**Randomness and the protocol's theorems.**

- The operating system's generator, `/dev/urandom`, read outside SPARK by `Os_Random`. Zero knowledge of the proofs `longfellow_prove` makes without `--seed` depends on it. A proof made with `--seed` is predictable by design.
- That `Simple_Rng` is the generator of the upstream test. It was transcribed, and the byte identity confirms it.
- The soundness, completeness and zero-knowledge theorems of the padded sumcheck, of Ligero and of their composition (ADR 0035, 0050, 0052).
- The fixed statement hash `DEFAULT_STATEMENT_HASH` of the reference (ADR 0035).

**Tools.**

- The GNAT compiler and GNATprove, including GNATprove's model of `Big_Integers`, which the P-256 ghost model uses.
- The SMT solvers: CVC5, Z3 and Alt-Ergo.
- SPARKlib's functional sequences, used as a ghost model (ADR 0031).
- That `Same`, the logical equality of each field wrapper, is the equality of its element type. Its body is the predefined `=`, outside SPARK (ADR 0023).

**Inputs and references.**

- The pinned specification itself.
- The upstream circuit files, as to what they compute, until this project compiles its own. Their shape is proved `Well_Formed` on load and their identifier is recomputed (ADR 0046).
- The upstream production reader at d5e6be7, as the definition of the LFC2 format.
- That the recordings of the upstream Ligero verifier are faithful to d5e6be7 (ADR 0040).

**Properties tested but not proved.**

- That `Sha256` and `Aes256` compute SHA-256 and AES-256 beyond the NIST and Appendix B.2 vectors. Both are Silver (ADR 0029).
- That the additive FFT and the Lagrange encoder agree beyond the tested rows, and the algorithm of Lin, Chung and Han as the reference implements it (ADR 0057).
- Fermat's little theorem, behind the test anchors of both `Inv`. On the verification path every inverse is checked at run time by `Checked_Inv` (ADR 0037).
- That the absorption into the transcript is complete beyond the two Appendix B.3 proofs. The sequence of calls in `Replay_Challenges` is the checklist.
- The termination of `Transcript.Nat`, of the P-256 sampler and of their callers in the P-256 instance. It is a probabilistic property, declared with `Always_Terminates` (ADR 0030).

**The machine.**

- Enough memory for one circuit and the two working sets of a verification, all on the heap. A failed allocation raises `Storage_Error`, which is outside the proofs (ADR 0047).
- GNAT building an aggregate allocator in place. The spike of ADR 0047 observed it, but the language does not guarantee it.
- A 64-bit target, behind `Unsigned_128` (ADR 0012).

## Outside the proofs, and what covers it

- **Soundness and zero knowledge of the protocol.** These are probabilistic properties, not contracts of a subprogram. The implementation follows the pinned specification step by step and cites each section, so that it is an instance of the analysed protocol and not a variant.
- **Completeness of the Fiat-Shamir transcript.** The order in which `Replay_Challenges` absorbs values was compared with the reference by reading, and is tested on the Appendix B.3 proofs. On the prover side, the byte identity with the upstream proofs tests every draw and every absorption.
- **Constant time.** It is a coding discipline, documented in each package header. The guarantee holds only for builds with assertions disabled, because enabled contracts and ghost code branch on secret values (ADR 0006). It does not apply to `Transcript`, `Sha256`, `Aes256` or the units of chapter 5, which handle only the public content of a proof (ADR 0029, 0037). The prover is constant time by construction, unit by unit. The run-length structure of Section 7.4 depends only on position, and the subfield projection is a fixed linear map. Two branches on values derived from the witness are declared (ADR 0051).
