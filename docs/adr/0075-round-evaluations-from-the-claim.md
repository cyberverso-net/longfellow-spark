# 0075 The prover's round evaluations take p (1) from the claim of the round, as upstream

## Status

Proposed (2026-10-27, milestone M2 of Phase D). Takes up the alternative that [ADR 0070](0070-sumcheck-and-ligero-kernels-as-upstream.md) left for later.

## Date

2026-10-27

## Context

In each round the prover sends p (0) and p (P2) of a quadratic p. The verifier takes p (1) as the claim of the round minus p (0).

- `Round_Evals_Dense` makes three products per pair since ADR 0070: a0 = sum q0 w0, s1 = sum q1 w1 and a2 = sum dq dw. Then p (P2) = a0 + P2 (s1 - a0 - a2) + P2^2 a2.
- Upstream's production prover (`quad_round_poly` in `rust/runtime/sumcheck/src/prover.rs`) makes two, a0 and a2. It takes s1 = p (1) as the claim minus a0, as the verifier does.
  - It tracks the claim across the rounds of a layer. The claim starts as claim0 + alpha claim1, the unpadded claims of the layer before, zero before the first. After each round it is p at the challenge, by Lagrange.
  - At the end of each layer it asserts that the claim equals claim0 times claim1 times the bound quad. The assertion is `assert_eq!`, so it is also on in release builds.
- The spec reference (`eval_round_poly`) computes p (2) directly, without the claim. Our ghost references `D0_Ref` and `D2_Ref` follow it.
- The two forms agree when the claim is the true sum p (0) + p (1). That holds for an honest prover on a satisfied circuit. It is the completeness of the sumcheck, which is tested, not proved.
- One product less per pair saves 6.9 M products on the mDoc hash circuit (ADR 0070 measured it for the step from four to three).

## Decision

**Two products per pair, with a conditional contract, as upstream.**

- `Round_Evals_Dense` takes the claim `Sum` and returns the leading coefficient `Lead`. It computes p (0) and `Lead`, and p (P2) as `Comb (X2, p (0), Sum - p (0), Lead)`.
- Its postcondition states:
  - p (0) equals `D0_Ref` and `Lead` equals `Dd_Ref`, as before;
  - p (P2) equals upstream's formula, for any `Sum`;
  - if `Sum` equals `D0_Ref + D1_Ref`, the true sum, then p (P2) equals `D2_Ref`, the spec reference.
- So the postcondition `Ev2 = D2_Ref` becomes conditional on the claim. This weakening was agreed before the change.
- `Prove_Layer` tracks the claim as upstream does. It takes the unpadded claims of the layer before and returns those of its own. After each round the next claim is `Comb` at the challenge: p at the challenge from the same three sums, three products. Upstream uses Lagrange through the three values; the value is the same.
- The contract of `Prove` does not change. It never stated the values written into the proof.
- `prover_kat` checks the claim as upstream's assertion does, in the test build:
  - it tracks the claim from the unpadded proof (the proof plus the pads): p (1) as the claim minus p (0), then Lagrange at the challenge, independently of the prover's `Comb`;
  - at the end of each layer it checks that the claim equals the two claims times the bound quad.

## Alternatives considered

- **Keep three products.** Rejected. It leaves the last product gap of the prover's round evaluations open.
- **Prove that the tracked claim is the true sum, inside `Prove`.** That is the completeness of the sumcheck. It needs a precondition that the wires are the evaluation of a satisfied circuit, and lemmas for the start of a layer, each round and the end of a layer. It would make `Ev2 = D2_Ref` hold again at every call. Kept as a candidate for the certification block. It does not need this change undone: it adds the invariant that discharges the condition.
- **Check the claim at run time in the prover, as upstream's `assert_eq!`.** Not taken. A check in SPARK code is a proof obligation, and this one is the completeness theorem. The test harness makes the check instead.
- **Delayed reduction** (`mac`, `accum_reduce`). Orthogonal: a change to the field interface, out of scope as in ADR 0070.

## Consequences

- Measured on the proving machine (c4-standard-24), proved build, mdoc v7, median of three runs in one session, 6b2ccc1 against 78f5173:

  | | before | after | change |
  |---|---|---|---|
  | hash prove | 5.32 s | 5.09 s | -0.23 s (-4 %) |
  | hash verify | 2.60 s | 2.59 s | unchanged |
  | sig prove | 0.64 s | 0.62 s | -0.02 s (-3 %) |
  | sig verify | 0.39 s | 0.39 s | unchanged |

  About 6.9 M products less in the prover, as expected. The verifier does not change. Upstream, on the same session with its generic field code, proves in 2.75 s and verifies in 1.14 s. The hash proof spends 58 % of its time in the carry-less multiplication.
- The proofs of the CLI stay identical byte for byte: at the true claim the two forms give the same field element.
- A wrong claim would give wrong round polynomials. The verifier would refuse the proof, as for any other error of the prover. The verifier does not change.
- The harness compares the dense form with the term-by-term reference at the true claim, the sum of qw times the active wires, and the merged terms with the reference terms at the same claim.
- A mutation of the initial claim makes `prover_kat` fail at the first layer of every circuit.
- Guide chapter 7, the trust model and the CHANGELOG are updated.

## Verification impact

- `Round_Evals_Dense` is Gold against `QW_Ref`, `D0_Ref` and `Dd_Ref`, and against `D2_Ref` under the condition on the claim. `Lemma_D2_Split` gives `D2_Ref` from the three sums, and `Lemma_Cancel_L_F`, new in `Sumcheck_Algebra`, gives s1 from the true claim.
- `D1_Ref` and `Dd_Ref` move from the body to the spec, since the postcondition names them.
- The claim tracked by `Prove` is tested, not proved, like completeness. Its arithmetic sits in two procedures with no postcondition, `First_Claim` and `Next_Claim`. Written inline in `Prove_Layer`, the contracts of its P-256 products made the provers time out on the precondition of `Lemma_BQ_Ref_From`, which does not depend on the claim.
- No `pragma Assume`. The one weakened postcondition is that of `Round_Evals_Dense`, as agreed.

## References

- [ADR 0063](0063-milestone-m1-algorithmic-parity.md), [ADR 0070](0070-sumcheck-and-ligero-kernels-as-upstream.md), [ADR 0071](0071-prover-reuses-the-bound-quad.md).
- google/longfellow-zk at d5e6be7: `rust/runtime/sumcheck/src/prover.rs` (`layer`, `quad_round_poly`, the assertion at the end of a layer), `docs/specs/rust/src/sumcheck/prover.rs` (`eval_round_poly`).
