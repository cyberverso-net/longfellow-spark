# 0071 The prover reuses the bound quad of its own sumcheck, proved

## Status

Proposed (2026-10-24, milestone M2 of Phase D).

## Date

2026-10-24

## Context

After ADR 0070 the prover spends 143.1 M field products on the hash circuit of mdoc v7. 41.1 M of them go to the verifier core, which the prover runs to build the linear constraint for Ligero. Almost all of that, 40.8 M, is `Eval_Bound_Quad_T`: the quad of each layer, bound at the challenges of the layer.

Upstream does not recompute it.

- `prove_core` keeps, for each layer, the scalar left in `hquad` once every hand is bound, and returns it as `SumcheckProofAux { bound_quad }`.
- `symbolic_sumcheck_verifier` takes that scalar when the caller is the prover, and calls `bind_quad` only when it is the verifier.
- Upstream's prover spends 0.2 M products on the verifier core.

Our prover holds the same scalar. After the last round of a layer, the terms that remain all have both hands at 0, and the sum of their coefficients is the bound quad.

The verifier's soundness does not depend on this value: the verifier computes it itself. For the prover it is a matter of completeness. A wrong value gives a proof that the verifier rejects.

ADR 0067 makes M2 the Gold limit: nothing new moves from proved to tested. Today the prover's value comes from `Eval_Bound_Quad_T`, Gold against `EBQT_Ref`. The reused value must carry the same guarantee.

## Decision

**The prover passes its own bound quad to the verifier core, and `Prove` proves that it equals `EBQT_Ref`.**

- **`Sumcheck_Prover.Prove`** returns the bound quad of each layer, the sum of the coefficients of the terms left after the last round. Its postcondition, at the level `Proof_Only`, states for each layer `Same (BQ (J), EBQT_Ref (...))`, with the terms of the layer, the challenges of the previous layer and the hand challenges of this one, all read from `Ch`.
- **`Sumcheck_Verifier.Verifier_Core`** takes the bound quads as an input, as upstream's `aux`. The verifier keeps computing them with `Eval_Bound_Quad_T`, as now. The prover passes those of `Prove`. The contract of `Verifier_Core` does not change otherwise.
- Beyond `Max_Bindeq_Log` the verifier's evaluation without tables stays, and the prover computes it as now. No circuit in use comes near.

**The proof.** The postcondition of `Prove` comes from an invariant on coefficients, kept round by round.

- `Bindeq_Ref (C, K, I)` takes the low bit of I with `C (K)` first. `Bind_H` binds the low bit of a hand at each round, in the same order. So each round of `Bind_H` turns a factor of `Bindeq_Ref` into a factor of the coefficient.
- The challenges of later rounds are not drawn yet when a round is bound. The invariant therefore speaks of coefficients, not of the sum with the final challenges: for every pair of residual indices `(a, b)`, the sum of the coefficients of the terms left with those hands equals the sum, over the terms of the layer with that residue, of `Bound_KT` times the factors of the challenges already drawn.
- Each step uses a contract that is already Gold: `Bind_G_T` (the coefficient is `Bound_KT`), `Merge_Runs` (`Run_Sum` over terms with the same hands), `Bind_H` (`Corner_K` over the corners that `Rd` names).
- After `Logw` rounds of each hand, `Fits` leaves only the residue `(0, 0)`, and the invariant is the postcondition.
- The field laws of ADR 0070 carry the algebra. New lemmas go in `Sumcheck_Prover`, at the level `Proof_Only`.

## Alternatives considered

- **Reuse, tested only.** The contracts of `Prove` and `Verifier_Core` are Silver, so no contract would move. But the value would move from a Gold function to an unproved one. Rejected for M2 by ADR 0067. It would be the fallback if the proof fails, and then a decision of its own.
- **Keep the recomputation.** Rejected: 40.8 M products, about 1.2 s of 9.8 s on the reference VM, for a value the prover already has.
- **A postcondition on the sum with the final challenges, by a ghost history of the term arrays.** Each round would be related to the next for arbitrary later challenges, and the chain applied at the end of the layer. It needs a sequence of arrays in ghost code. The invariant on coefficients needs none.

## Consequences

- Estimated saving on the hash circuit: about 40.8 M products in the prover, about 1.2 s on the VM. The verifier does not change.
- The proofs of the CLI stay identical byte for byte. The value is the same field element.
- `prover_kat` compares, on every layer of every test circuit, the bound quad of `Prove` with `Eval_Bound_Quad_T`.
- Guide chapters 3 and 7, the trust model and the CHANGELOG are updated.

## Verification impact

- `Sumcheck_Prover` gains a functional postcondition on `Prove`, Gold. The rest of its contract stays Silver, as now.
- `Sumcheck_Verifier` and `Zk_Prover` are proved again. Their levels do not change.
- No `pragma Assume`, no weaker contract.

## References

- [ADR 0052](0052-gold-perimeter-for-the-prover.md), [ADR 0063](0063-milestone-m1-algorithmic-parity.md), [ADR 0067](0067-performance-milestones-by-trust.md), [ADR 0070](0070-sumcheck-and-ligero-kernels-as-upstream.md).
- google/longfellow-zk at d5e6be7:
  - `rust/runtime/sumcheck/src/prover.rs` (`prove_core`, `SumcheckProofAux`);
  - `rust/runtime/zk/src/symbolic_sumcheck_verifier.rs` (`aux`, `bind_quad`).
