# Changelog

All notable changes to this project are recorded here. The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/); the project does not yet follow semantic versioning in the strict sense, since its interface is the pinned specification rather than an API. Every entry names the decision records (`docs/adr/`) and the guide chapter (`docs/guide/`) that describe it; the trust model that says what is proved, tested and trusted is in the README.

## [Unreleased]

### Changed

- The `prove` workflow's job limit is sixty minutes and the prover units are two proof partitions, `prover` and `ligero-prover`, nine in all (ADR 0054): the one partition of Phase C exceeded both the forty-five and the sixty minute limit on the hosted runner.
- The proof runs on the project's own proving machine on Google Cloud (ADR 0060): the `prove` workflow starts the VM and runs `make prove` as one job on its self-hosted runner, replacing the partition matrix on hosted runners; `scripts/remote-check.sh` runs `make check` there from the developer's working tree.

## [0.3.0] - 2026-10-19

Phase C: the prover. From a circuit, its inputs and a randomness source to the proof string of Section 7.5, in the reference's order of operations: the two proofs that google/longfellow-zk ships are reproduced byte for byte from their inputs and seeds.

### Added

- The prover units, generic over the field's transcript glue and over a `Sampling` instance that carries the randomness source (chapter 7; ADR 0049 to 0053): `Prover_Status`; `Simple_Rng`, the generator of the upstream reference test, and `Sampling` (the reference's samplers on a byte stream); `Proof_Writer` (the writers of Sections 7.3, 7.4 and 7.5, the run-length structure of the subfield encoding decided by position, Gold on the reader's rules `Well_Coded`); `Sumcheck_Prover` (the pads of Section 6.5, the round evaluations proved equal to the ghost transcription of `eval_round_poly`, the layers on the live transcript with the challenges recorded for the core, the quadratic triples); `Ligero_Prover` (the tableau of Section 4.3 on the heap, the Reed-Solomon encoder on all columns with its systematic part proved equal to the row, the commitment with nonces and `Merkle.Build`, the proof of Section 4.4 with the verifier's own challenge and absorption procedures); `Merkle.Open`, the batch opening of Section 4.1.3, Gold in the model of `Merkle.Verify`; `Zk_Prover`, the composition of `zk/prover.rs` with the validation statuses `Input_Length`, `Not_Satisfied`, `Not_In_Subfield`, `Config_Invalid` and `Exhausted`; the fixed projection of GF(2^128) on the coordinates of GF(2^16) (`GF2_128.Subfield_Coords`, sixteen masks) and the formal `To_Subfield_Bytes` of `Field_Signature`; the proof partition `prover` (4591 checks).
- The command-line prover `longfellow_prove` in `cli/` (ADR 0049, 0050): the field, the circuit file, the inputs file in the upstream JSON format, the label, the Ligero configuration, the output file; the operating system's generator by default (`Os_Random`, `/dev/urandom`, outside SPARK) and the upstream test generator behind `--seed`; exit status 0 written, 1 prover status, 2 usage or file error.
- Vectors and harnesses (ADR 0053): `gen_prover_vectors.py`, an independent Python transcription of the reference prover piece by piece (`writer.txt`, `sumcheck_prover.txt`, `ligero_commit.txt`, `zk_prove.txt`) and the masks of the projection in `gen_gf2_128_vectors.py`; the harnesses `writer_kat` (every proof of the repository rewritten identical) and `prover_kat` (the pads and padded sumcheck proofs, the commitments with their openings, the Merkle roots of the two upstream proofs reproduced, the complete proofs of the small circuits accepted by `Zk_Verifier`, the statuses, and the refusal of the proofs an unchecked prover makes of false inputs); the `cli` step reproduces `sha256_proof.bin` and `ecdsa2_proof.bin` byte for byte with `longfellow_prove` under the upstream seeds and verifies proofs under another seed and under the system source; `verify_proof_file.rs`, a test for the upstream crate that verifies a proof file of this project with the upstream verifier, run by hand.

### Changed

- 16671 checks proved in all (11967 at 0.2.0), eight proof partitions; the `prover` partition is now the heaviest and `make check` takes about an hour and a quarter.
- `Merkle`, `GF2_128` and `Field_GF2_128` gained the opening and the projection; `Field_Signature` gained one formal, so every instance of the sumcheck generics names `To_Subfield_Bytes`.

### Trust model

The operating system's generator is trusted for the zero-knowledge property of the proofs made without `--seed`; the shapes of the tableau are proved row by row and tested as a whole (ADR 0052, amended at block 4); completeness is tested, not proved. The README lists the entries.
[0.3.0]: https://github.com/cyberverso-net/longfellow-spark/compare/v0.2.0...v0.3.0

## [0.2.0] - 2026-10-17

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

[0.2.0]: https://github.com/cyberverso-net/longfellow-spark/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/cyberverso-net/longfellow-spark/releases/tag/v0.1.0
