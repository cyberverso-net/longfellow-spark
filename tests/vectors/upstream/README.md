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

To regenerate:

    cd <clone of longfellow-zk>/docs/specs/rust
    git checkout d5e6be7
    cp <this directory>/record_sumcheck_core.rs tests/
    cargo test --test record_sumcheck_core -- --nocapture
    cp /tmp/sumcheck_core_*.txt <this directory>/

The harness reads every `sumcheck_core_*.txt` here when it runs without
arguments.
