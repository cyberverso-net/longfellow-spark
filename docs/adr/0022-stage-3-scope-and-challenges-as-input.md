# 0022 Stage 3 scope: sumcheck algebra and symbolic verifier core, challenges as input

## Status

Accepted (2026-10-12, after block 2 of stage 3)

## Date

2026-10-12

## Context

In Longfellow the sumcheck verifier does not accept or reject a proof on its own. The prover encrypts every polynomial evaluation and every per-layer claim with a one-time pad (draft Section 6.5), so the verifier sees padded values only. What the verifier produces is a set of constraints over the combined witness vector, private circuit inputs first and pad values after them: one linear constraint per layer and one after the input layer, each of the form A * W + b = 0 with A sparse, plus one quadratic constraint per layer, W[c0] * W[c1] = W[cr], relating the two claim pads to their product (Section 6.7, `symbolic_sumcheck_verifier_core` and `generate_lqc_triples`). The Ligero layer (Section 4, phase B) checks those constraints against the commitment.

Every verifier challenge is a Fiat-Shamir value: the transcript absorbs the statement, the commitment and the padded proof element by element and yields the challenges in a fixed order (`begin_circuit`, `begin_layer`, `round_poly`, `end_layer`, then `alpha_input`). The transcript is stage 4 of Phase A in the project plan, with SHA-256 and the absorption checklist, and is not available at stage 3. Circuits are in-memory data ([ADR 0011](0011-circuits-as-data.md)); the LFC2 parser belongs to phase B.

## Decision

Stage 3 is the sumcheck algebra and the symbolic verifier core, with challenges as an input. The core never touches a transcript. Stage 4 will replay the transcript over the statement and the proof and hand the core a complete `Challenges` record; the record is the interface between the two stages.

In scope, following the reference implementation at d5e6be7:

- the array vocabulary of Sections 6.1 and 6.2: `eq`, `eq2`, `bindeq`, `bind`;
- `lagrange_basis` on the three evaluation points (Section 6.4, [ADR 0025](0025-polynomials-and-lagrange-constants.md));
- `eval_quad` and `eval_circuit`, including the Z assertions (Sections 6.3.2 and 6.3.3), returning a status rather than raising;
- `bind_g` and `eval_bound_quad`;
- the symbolic core: `symbolic_sumcheck_round`, `verify_layer`, `input_constraint`, `symbolic_sumcheck_verifier_core`, producing the `LigeroTerm` triples (coefficient, constraint index, witness index) and the vector b, plus the quadratic triples (c0, c1, cr) of `generate_lqc_triples`;
- the `Expression` type that the symbolic core manipulates ([ADR 0026](0026-sparse-expression.md)).

Out of scope: the prover (Section 6.6), the transcript and every challenge derivation, `begin_circuit`, `write_sumcheck_statement`, LFC2 parsing, the Ligero check of the emitted constraints.

The `Challenges` record carries, in the order the transcript produces them:

- the output-binding challenges: the reference draws MAX_LOGW = 40 values `q` (reserved, discarded) and 40 values `g`, and the core uses `g[0 .. ceil_lg2(noutput) - 1]` as the initial binding of both hands. The record holds the 40 `g` values; the `q` values never reach the core;
- per layer: `alpha` and `beta`; then, for each round r in 0 .. logw - 1 and each hand h in 0 .. 1, in that nesting (round outer, hand inner), one challenge, the one `round_poly` returns after absorbing the two padded evaluations of that hand and round;
- `alpha_input`, drawn after the last layer.

Witness indices: the private inputs occupy 0 .. ninput - npublic - 1; the pad starts at ninput - npublic (`zk/verifier.rs`, line 177) and is laid out per layer as 4 * logw values (per round, hand 0's p0 and p2 pads, then hand 1's) followed by c0, c1, cr (Section 6.5, `LayerPad::generate_indices`). The quadratic triples are the (c0, c1, cr) of each layer, which `generate_lqc_triples` computes with the same arithmetic.

Index names, fixed here because the draft and the reference use `NW` differently: for layer j, `nw_in (j)` is the number of input wires, `layers[j].nw` in the reference and `NW[j + 1]` in the draft, with `logw (j)` the number of sumcheck rounds; `nw_out (j)` is the number of output wires, `layers[j - 1].nw` for j > 0 and `noutput` for j = 0, `NW[j]` in the draft. A term of layer j has g < nw_out (j) and h0, h1 < nw_in (j).

## Alternatives considered

- **A concrete verifier with the transcript inside, as the upstream C++ is organised.** Rejected: it would tie the stage 3 proofs to SHA-256, which is trusted until proved, and the absorption checklist is a stage of its own; a Frozen Heart omission is invisible to SPARK and deserves undivided attention.
- **A core generic over a transcript procedure (formal subprogram parameter).** Rejected: a formal procedure with state complicates the flow contracts and the Gold proofs for no gain; a complete record checked once by a precondition on its sizes is simpler to prove and to test, and it lets the harness inject recorded challenges ([ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md)).
- **Including the prover (Section 6.6).** Rejected: phase C; the verifier has independent value and the prover reuses the algebra of this stage.
- **Starting from the LFC2 loader so that real circuits can be read.** Rejected: ADR 0011 places the loader in phase B; the explicit circuits of draft Appendix B.3 and the upstream unit tests suffice to exercise every path of the core.

## Consequences

- Stage 4 is defined by its output: a `Challenges` record of the shape above. Any change to that shape is a change to this record.
- The harness checks the core against recorded upstream runs with injected challenges, so the recordings must include the challenges in the order consumed ([ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md)).
- No accept or reject decision exists at stage 3; the exit criterion is agreement with upstream on the emitted constraints.
- The verifier handles public data only (circuit, public inputs, padded proof, challenges), so the constant-time discipline of [ADR 0006](0006-constant-time-discipline-and-scope.md) imposes no constraint on this code; the generic algebra is nevertheless written without secret-dependent control flow, since the prover of phase C will reuse it on private wires.

## Verification impact

- Provable: absence of run-time errors on every subprogram for every circuit, proof and challenge record satisfying the stated size preconditions (Silver); the structural Gold kernels of [ADR 0023](0023-gold-perimeter-for-protocol-code.md); the index and capacity bounds that the symbolic core relies on.
- Tested: agreement with the upstream reference on the explicit circuits and on recorded runs.
- Trusted: the challenge derivation, until stage 4 replaces the injected record with a replayed transcript; upstream circuits as data (ADR 0011); the soundness argument of the protocol, which no contract states.
- Constant time: no requirement at this stage; see Consequences.

## References

- draft-google-cfrg-libzk-03, Sections 6.1 to 6.7, in particular 6.5 (pad layout) and 6.7 (the core).
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/sumcheck/common.rs`, `sumcheck/proof.rs`, `sumcheck/pad.rs`, `zk/symbolic_sumcheck_verifier.rs`, `zk/common.rs` (`generate_lqc_triples`), `zk/verifier.rs` (pad index start), `circuit/lfc2.rs` (the types `Term`, `CircuitLayer`, `Circuit`).
- [ADR 0011](0011-circuits-as-data.md); the project plan in the handoff note (Phase A, items 3 and 4).
