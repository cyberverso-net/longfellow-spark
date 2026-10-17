# Changelog

All notable changes to this project are recorded here. The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/); the project does not yet follow semantic versioning in the strict sense, since its interface is the pinned specification rather than an API. Every entry names the decision records (`docs/adr/`) and the guide chapter (`docs/guide/`) that describe it; the trust model that says what is proved, tested and trusted is in the README.

## [0.2.0] - Unreleased

Phase B: the verifier takes the circuits the upstream compiler produces and accepts the proofs the upstream prover made for them, from their files, on both fields.

### Added

- The LFC2 circuit loader (`Uleb128`, `Circuit_Status`, `Circuit_Reader` generic over the sumcheck algebra of a field, instantiated for GF(2^128) and P-256; chapter 6; ADR 0046): the format as the upstream production reader at d5e6be7 defines it, read in two passes with the circuit allocated once on the heap, `Well_Formed` of the core established on the result and the identifier (`compute_id`) recomputed and checked; `Uleb128.Read` proved Gold on the decoded value, `Circuit_Reader.Read` Silver on arbitrary bytes with the ownership checks and Gold on the shape of its result; 584 checks in the new proof partition `circuits`.
- The working sets of `Zk_Verifier.Verify` and `Ligero_Verifier.Verify` in one heap allocation each, under SPARK's ownership rules, freed on every path (ADR 0047): the supported scale is the available memory, the stage 3 input constraint excepted.
- The release project `cli/` with the command-line verifier `longfellow_verify` (exit status 0 accepted, 1 refused, 2 usage) and the interop harness `interop_kat`; the step `cli` of `scripts/check.sh` and of the `verify` workflow.
- Vectors (ADR 0048): the two upstream circuits, inputs and proofs copied under `tests/vectors/upstream/circuits/` and pinned by SHA-256; `gen_circuit_vectors.py`, an independent LFC2 reader and writer whose `compute_id` must equal the identifiers the upstream files store; `circuit_summary.txt`, `circuit_lfc2.txt` (the Appendix B.3 circuits in two encodings, 28 malformed files) and `interop.txt`; the harness `circuit_kat` (121 cases).
- The interop exit criterion of ADR 0011 met: the `sha256` proof (GF(2^128), 98 993 terms, 6657 inputs) and the `ecdsa2` proof (P-256, 48 256 terms, 1042 inputs) accepted end to end in about a second each; the six copies with one altered byte refused with `Merkle_Failed`.

### Changed

- 11967 checks proved in all (10738 at 0.1.0), seven proof partitions.

## [0.1.0] - 2026-10-16

Phase A complete: a verifier of Longfellow ZK (libzk) in Ada/SPARK, from the proof string to a verdict, on the explicit circuits of the pinned specification (IETF draft-google-cfrg-libzk-03), with the two complete proofs of its Appendix B.3 accepted end to end on both fields and compared value by value with the upstream verifier (google/longfellow-zk at d5e6be7). Every SPARK check of the project is proved by GNATprove with the pinned toolchain (`gnat_native 16.1.0`, `gnatprove 16.1.0`), with no justification and no `pragma Assume`.

### Added

- Stage 1, GF(2^128) (`GF2_128`; chapter 1; ADR 0004 to 0010): `Add`, `Xtime`, `Mul` and `Square` proved Gold against the ghost Horner reference `Mul_Ref`; `Inv` a fixed Itoh-Tsujii chain, Silver, total; 41 checks at the close of the stage; 209 known-answer cases anchored on the upstream subfield basis constants, 234 with the serialisation of stage 4 and the subfield injection of stage 5.
- Stage 2, the P-256 base field (`P256_Field`; chapter 2; ADR 0012 to 0017): `Add`, `Sub`, `Neg`, `Mul`, `Square`, `From_Bytes`, `To_Bytes` proved Gold against a ghost big-integer model (`To_Int (Mul (A, B)) = To_Int (A) * To_Int (B) mod p` for all inputs), canonical form by type predicate, the Solinas reduction proved as a polynomial identity in 2^32; `Inv` Silver, total; 3694 checks project-wide at the close of the stage; 467 known-answer cases anchored on the P-256 base point.
- Stage 3, the sumcheck algebra and the symbolic verifier core (`Sumcheck_Algebra`, `Sumcheck_Expression`, `Sumcheck_Verifier`, generic over a field through `Field_Signature`, instantiated for both fields; chapter 3; ADR 0022 to 0027): `Eq`, `Bindeq`, `Bind`, `Lagrange_Basis`, `Eval_Quad`, `Eval_Circuit`, `Bind_G`, `Eval_Bound_Quad` and every `Expression` operation proved structurally Gold against ghost references transcribing the draft's formulas; the core of Section 6.7 emits the Ligero constraints from a circuit, its public inputs, the padded proof and the challenges; 6811 checks at the close of the stage; 208 cases plus the recorded upstream runs with injected challenges.
- Stage 4, the Fiat-Shamir transcript and the challenge replay (`Bytes`, `Sha256`, `Aes256`, `Transcript`, `Fisher_Yates`, `Sumcheck_Transcript`; chapter 4; ADR 0028 to 0032): the transcript of draft Section 3 with its codec proved structurally Gold against a proof-only ghost sequence of the absorbed bytes, `Nat` and `Choose` Gold, the rejection loops literal; the replay of every challenge of a proof and the reader of the sumcheck part; 7810 checks at the close of the stage; Appendix B.2 reproduced byte for byte (78 cases), NIST vectors for SHA-256 and AES-256, 91 cases in all.
- Stage 5, Ligero and the complete verifier (`Merkle`, `Ligero_Geometry`, `Lagrange`, `Ligero_Proof`, `Ligero_Verifier`, `Zk_Verifier`, `Verifier_Status`, `Proof_Levels`; chapter 5; ADR 0035 to 0043): the Merkle heap and its batch verification Gold, the geometry Gold on Section 4.2.1, the Reed-Solomon code by Lagrange interpolation at the queried columns with every inverse checked at run time, the proof reader of Section 7.4 Gold on the run-length rules, the three Ligero tests structural Gold, the complete verifier of Section 7.5 Silver with proved shape; 10738 checks; 467 cases in `ligero_kat` and 333 in `sumcheck_kat`, among them the two Appendix B.3 proofs accepted from the proof string on both fields, every intermediate value equal to the recorded upstream run, and the negative cases of ADR 0040 refused with their status.
- The didactic guide (`docs/guide/`, one chapter per stage with the verification condition table), 45 architecture decision records (`docs/adr/`), the known-answer vector generators (`tests/vectors/`, 20 files and 4 upstream recordings), the single definition of the checks (`scripts/check.sh`, `make check`) and the two workflows `verify` and `prove` (ADR 0018 to 0021, 0033, 0034, 0041, 0045).

### Changed

- Consolidation after Phase A (ADR 0042 to 0045): the Status lines of the records carry amendment notes of a fixed form; the functional contracts and ghost models of the two fields are at the proof-only assertion level, so the whole harness set runs in seconds with assertions on and the slow set of ADR 0041 is folded into `make check`; the six partition checks of `prove` are required for merging.

### Trust model

What is proved, tested and trusted is listed in the README, section "Trust model", entry by entry, with the record that justifies each entry. Upstream-generated circuit files remain a declared trusted input until Phase D; the soundness and zero-knowledge theorems of the protocol are out of scope for proofs.

[0.2.0]: https://github.com/cyberverso-net/longfellow-spark/compare/v0.1.0...phase-b-loader
[0.1.0]: https://github.com/cyberverso-net/longfellow-spark/releases/tag/v0.1.0
