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
