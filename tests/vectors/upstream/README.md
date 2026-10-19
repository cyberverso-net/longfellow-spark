# Recorded runs of the upstream verifier (tier 3, ADR 0027)

This directory holds the recordings of the upstream reference verifier that
`tests/bin/sumcheck_kat` compares the symbolic core against, and the
instrumentation that produced them.

- `record_sumcheck_core.rs`: a test to drop into `docs/specs/rust/tests/` of
  google/longfellow-zk at commit d5e6be77336933d50bf7f25a954f8ec273eb51ce. It
  reproduces the two explicit circuits of draft Appendix B.3 from
  `unit_tests.rs`, runs the upstream prover, then replays
  `symbolic_sumcheck_verifier_core` with the challenge draws, the padded proof,
  the claim expressions and the emitted constraints written out in the format
  of ADR 0027. The library is not modified.
- `sumcheck_core_<field>_<circuit>.txt`: the recordings, one per circuit and
  field, produced by that test. They are not written by hand and not generated
  in this repository.
- `record_ligero_verifier.rs`: the same for the Ligero verifier (stage 5, ADR
  0040): after the upstream prover and verifier, it replays
  `LigeroVerifier::verify` step by step on the transcript of `zk/verifier.rs`
  and writes the challenges, the chosen columns and both sides of each test
  in the format of ADR 0040. The steps are the private functions of
  `ligero/verifier.rs` transcribed over the public API; each must agree where
  the library's verifier accepted.
- `ligero_<field>_<circuit>.txt`: its recordings. `tests/bin/sumcheck_kat`
  runs the Ligero verifier of this repository on the proof of the same
  circuit after the sumcheck recording, step by step against the file when
  present, composed otherwise.

To regenerate:

    cd <clone of longfellow-zk>/docs/specs/rust
    git checkout d5e6be7
    cp <this directory>/record_sumcheck_core.rs tests/
    cargo test --test record_sumcheck_core -- --nocapture
    cp /tmp/sumcheck_core_*.txt <this directory>/
    cp <this directory>/record_ligero_verifier.rs tests/
    cargo test --test record_ligero_verifier -- --nocapture
    cp /tmp/ligero_*.txt <this directory>/

The harness reads every `sumcheck_core_*.txt` here when it runs without
arguments, and the `ligero_*.txt` of the same circuit when it exists.

## Circuit files (Phase B, ADR 0048)

`circuits/` holds the two circuits that google/longfellow-zk ships with
inputs and proofs under `docs/specs/rust/tests/testdata/` at commit
d5e6be77336933d50bf7f25a954f8ec273eb51ce, copied unchanged (the `.bin`
twins of the circuit files upstream are byte-identical to the `.lfc2`
files and are not copied). Licence: Apache-2.0, the project's own. The
SHA-256 of each copy:

    6e1b3f0d8a70470d1c82b41dc401eb6d770e6cc23638d7db53acf8040e9bc440  sha256_circuit.lfc2
    c698ed9d0bb4d816419c17177a8c64860734cee7d7fa112d1e04a84a4e814297  sha256_inputs.json
    3e44a4ed36006b581b42895de343745cae81f7ee5bd0b00a2664bfac2701d0d4  sha256_proof.bin
    b9f25654d382abf81098df6e67a2dc331e90144a045bfe73e23bac23172031e9  ecdsa2_circuit.lfc2
    6c9a8861ad49c446914ab6b73c91115c7f1c95926ae56123a03e3d7f9a939a43  ecdsa2_inputs.json
    897951c8aff3b55c153f38dd9737ee063b99a24e2327f0da029d9748c29d3cc6  ecdsa2_proof.bin

`sha256` is over GF(2^128) (FieldID 4, subfield boundary 3000, 12 layers,
98993 terms, 6657 inputs, none public); `ecdsa2` over the P-256 base
field (FieldID 1, 11 layers, 48256 terms, 1042 inputs, none public). The
labels and Ligero configurations of their proofs are those of
`docs/specs/rust/tests/test_reference.rs`: `sha256_spec_test` with rate
3, 16 queries, 256 columns; `ecdsa2_spec_test` with rate 4, 16 queries,
256 columns. `gen_circuit_vectors.py` parses the circuit files with its
own LFC2 reader and writes `circuit_summary.txt`, which
`tests/bin/circuit_kat` compares with the SPARK loader; the identifier
each file stores must equal the one the generator computes, or the
generator aborts.

## Cross-verification of this project's proofs (Phase C, ADR 0053)

`verify_proof_file.rs` is a test to drop into `docs/specs/rust/tests/` of
the same commit. It loads a circuit and its inputs as `test_reference.rs`
does, reads a proof file written by this project's `longfellow_prove` and
verifies it with the upstream `ZkVerifier` under the label and the
Ligero configuration given in the environment. It is run by hand, outside
the CI, at the close of block 5 and after any change to the prover:

    cd <clone of longfellow-zk>/docs/specs/rust
    git checkout d5e6be7
    cp <this directory>/verify_proof_file.rs tests/
    LFS_FIELD=gf2_128 LFS_CIRCUIT=tests/testdata/sha256_circuit.lfc2 \
      LFS_INPUTS=tests/testdata/sha256_inputs.json \
      LFS_PROOF=<longfellow-spark>/cli/out/sha256_seed7.bin \
      LFS_LABEL=sha256_spec_test LFS_RATE_INV=3 LFS_NREQ=16 LFS_NCOL=256 \
      cargo test --test verify_proof_file -- --nocapture
    LFS_FIELD=p256 LFS_CIRCUIT=tests/testdata/ecdsa2_circuit.lfc2 \
      LFS_INPUTS=tests/testdata/ecdsa2_inputs.json \
      LFS_PROOF=<longfellow-spark>/cli/out/ecdsa2_system.bin \
      LFS_LABEL=ecdsa2_spec_test LFS_RATE_INV=4 LFS_NREQ=16 LFS_NCOL=256 \
      cargo test --test verify_proof_file -- --nocapture

The two proof files are those `scripts/check.sh cli` writes under
`cli/out/`: `sha256_seed7.bin` under `Simple_Rng (7)` and
`ecdsa2_system.bin` under the operating system's source, so neither is a
copy of the upstream file. The proofs made under the upstream seeds are
compared byte for byte with the upstream files by that step instead.
