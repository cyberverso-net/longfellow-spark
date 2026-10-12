# 0027 Sumcheck vectors and upstream instrumentation

## Status

Accepted (2026-10-12, after block 2 of stage 3)

## Date

2026-10-12

## Context

The Gold of stage 3 is structural ([ADR 0023](0023-gold-perimeter-for-protocol-code.md)): it proves that the code computes the transcribed formulas, not that the formulas are the draft's or that the core agrees with the upstream verifier. Both gaps are closed by tests, as [ADR 0009](0009-known-answer-vectors.md) did for `Mul_Ref`. Three sources exist. The draft gives two explicit circuits in Appendix B.3 with their witnesses and proofs; the upstream unit tests build the same circuits as term lists and run prover and verifier on them (`docs/specs/rust/tests/unit_tests.rs`, `test_sgonal_test_vector_p256` and `test_sgonal_test_vector_gf2_128`); the algebraic definitions of Sections 6.1, 6.2 and 6.4 can be checked against an independent reference.

The challenges of a real run come from the transcript, which stage 3 does not have ([ADR 0022](0022-stage-3-scope-and-challenges-as-input.md)). Checking the symbolic core against upstream therefore requires recording, from an upstream run, the challenges it consumed together with what it emitted.

Two errata in draft Appendix B.3 were found while reading the sources and are recorded here so that the vectors do not inherit them. B.3.2 is labelled "P-256 scalar field (Field ID 2)", but the order it prints is 2^256 - 2^224 + 2^192 + 2^96 - 1, the base field prime; Table 1 gives p256 the identifier 0x01, and the upstream `algebra/p256.rs` uses that prime. B.3.3 is labelled "Field ID 5", which Table 1 assigns to GF(2^16); GF(2^128) is 0x04. B.3.3 also gives the witness as [1, 84, 5, 6] with "n = 84", but the circuit requires (s + 1) m^2 + (s + 1) m + n = 0 in GF(2^128), and with m = 5 and s = 6 as polynomial bit patterns that gives n = 0x6c (108); the upstream test computes n in the field exactly so, and the proof bytes of B.3.3 were produced with that witness.

## Decision

Vectors for stage 3 come in three tiers, in the notation of ADR 0009 (plain text, one case per line, hex big-endian elements for both fields; P-256 elements as 64 hex digits of the integer).

- **Tier 1, explicit circuits.** The two circuits of Appendix B.3 as in-memory term lists, copied from the upstream unit tests (the term order of `create_sgonal_circuit_p256` and `create_sgonal_circuit_gf2_128` is the reference, since the draft gives equations, not lists): B.3.2 over the P-256 base field with witness [1, 45, 5, 6]; B.3.3 over GF(2^128) with witness [1, n, 5, 6], n computed in the field by the generator (0x6c) and the draft's 84 noted as an erratum. `Eval_Circuit` must return success with every output zero; the per-layer wire values are recorded and checked. Negative cases: one witness that violates the output and one circuit with a Z term that fails.
- **Tier 2, algebra.** `eq`, `eq2`, `bindeq`, `bind`, `lagrange_basis`: structural cases (challenges all zero, all one, a single one; the three evaluation points, where the basis must give the unit vectors) and seeded random cases, expected values from an independent Python reference written from the draft's definitions (bindeq by the recursive definition, eq by the product, the basis by division with the generator's own inverse), on both fields. The reference also checks `bindeq (C) (i) = eq (C, i, n)` on every case and the Lagrange constants of [ADR 0025](0025-polynomials-and-lagrange-constants.md) by `d * inv (d) = 1`, and aborts on any failure.
- **Tier 3, recorded upstream runs.** For the two B.3 circuits, a run of the upstream reference instrumented to log, in the order the core consumes or produces them: the output-binding challenges g, per layer alpha and beta and the per-round, per-hand challenges, alpha_input; the padded proof (p0 and p2 per hand and round, the two claims per layer); the claim expression after each round and at emission; the emitted constraints (A as (constraint, variable, coefficient) triples, b, the quadratic triples). The harness feeds the circuit, the public inputs, the proof and the challenges to the core and compares the output per constraint as a set of (variable, coefficient) pairs, ignoring order within a constraint and zero coefficients ([ADR 0026](0026-sparse-expression.md)).

  These files are produced outside this repository, by Paolo, from the upstream clone at d5e6be7 with an instrumentation patch against `docs/specs/rust/tests/unit_tests.rs` (or a test added beside it); the patch is kept under `tests/vectors/upstream/` with the commit hash, so that the recording is reproducible. No tier 3 file is written by hand or synthesised in this repository.

  Format of a tier 3 file (`sumcheck_core_<field>_<circuit>.txt`), in the line style of the other files, elements in hex as above, indices in decimal:

  ```
  field <gf2_128|p256>
  circuit <name> <noutput> <ninput> <npublic> <nl>     then the layer and term lines of tier 1
  public <w_0 .. w_npublic-1>
  pad_base <index>                                     ninput - npublic
  g <g_0 .. g_39>                                      the output-binding challenges, all 40
  layer_challenges <j> <alpha> <beta> <c_0,0> <c_0,1> <c_1,0> ... <c_logw-1,1>
                                                       round r, hand h, in consumption order
  proof <j> <e_0 .. e_4logw-1> <claim_0> <claim_1>     e index 4 r + 2 h + k: hand h of round r,
                                                       k = 0 the padded p (0), k = 1 the padded p (P2)
  alpha_input <value>
  claim <j> <r> <h> <known> <n> <var coeff> ...        the claim after round r, hand h of layer j
  constraint <c> <b_c> <n> <var coeff> ...             constraint c: b and the sparse row of A
  lqc <j> <x> <y> <z>
  end
  ```

  The `claim` lines are optional and checked when present; the `constraint` lines are compared per constraint as sets of (variable, coefficient) pairs, zero coefficients ignored on both sides. The order of the evaluations in `proof` is the pad order of Section 6.5, which differs from the serialisation order of Section 7 (there, within a round, the two hands' p (0) precede the two hands' p (P2)).

- The generator `gen_sumcheck_vectors.py` produces tiers 1 and 2 for both fields, deterministically, with a fixed seed; `make vectors` compares its output with the committed files, as for the other generators.
- The harness `sumcheck_kat` runs both instances; it fails if any case fails or if no case ran, as the other harnesses do.

## Alternatives considered

- **Tier 1 only, from the draft's text.** Rejected: the draft gives no intermediate values, and its witness for B.3.3 is wrong; the upstream test file is the usable source.
- **Deriving tier 3 by running the upstream verifier inside this repository's checks.** Rejected: it would add a Rust toolchain to `make check` and to the hosted gate; a recorded run with its patch is reproducible and small.
- **Fabricating the challenges for tier 3 (random values) and comparing only internal consistency.** Rejected: a core that agrees with itself proves nothing about agreement with upstream; the recorded challenges are what makes the comparison meaningful, the same argument ADR 0009 made for external anchors.
- **Waiting for stage 4 and checking the whole verifier on the B.3 proofs end to end.** Not sufficient: that check comes, but it attributes a failure to nothing in particular; tier 3 localises a disagreement to a layer, a round and a constraint.

## Consequences

- `tests/vectors/` gains `sumcheck_gf2_128.txt` and `sumcheck_p256.txt` (tiers 1 and 2, 208 cases together at block 2), the generator `gen_sumcheck_vectors.py`, and `tests/vectors/upstream/` with the instrumentation patch and the tier 3 recordings. The harness `sumcheck_kat` reads all of them and also re-checks the Lagrange constants and `bindeq (c) (i) = eq (c, i, n)` at run time.
- The errata above are reported upstream in the draft's issue tracker; until a later draft fixes them, [ADR 0002](0002-pin-the-specification.md) applies: the pinned text is -03, the errata are listed here and in chapter 3.
- The README trust model moves "the core agrees with the upstream verifier on the emitted constraints" from claimed to tested, with the files named.

## Verification impact

- Provable: nothing; vectors are tests.
- Tested: `Eval_Circuit` on the explicit circuits; the algebraic definitions against an independent reference; the symbolic core against recorded upstream runs with injected challenges.
- Trusted: that the upstream run was recorded faithfully from d5e6be7 with the kept patch; that the upstream reference is itself the draft's protocol.
- Constant time: no effect.

## References

- draft-google-cfrg-libzk-03, Appendix B.3 (B.3.1 randomness, B.3.2, B.3.3), Table 1 (field identifiers), Sections 6.1, 6.2, 6.4, 6.7.
- google/longfellow-zk at d5e6be7: `docs/specs/rust/tests/unit_tests.rs` (`create_sgonal_circuit_p256`, `create_sgonal_circuit_gf2_128`, `test_sgonal_test_vector_*`), `docs/specs/rust/src/algebra/p256.rs` (`prime`), `docs/specs/test-vector1-sumcheck.txt`.
- [ADR 0009](0009-known-answer-vectors.md), [ADR 0017](0017-p256-test-anchors.md), [ADR 0022](0022-stage-3-scope-and-challenges-as-input.md), [ADR 0026](0026-sparse-expression.md).
