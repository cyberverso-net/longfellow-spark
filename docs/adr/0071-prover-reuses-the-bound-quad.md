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

**The prover passes its own bound quad to the verifier core, and `Prove` proves that it equals the verifier's reference.**

- **`Sumcheck_Prover.Prove`** returns the bound quad of each layer in a new out parameter `BQ`. Its postcondition, at the level `Proof_Only`, states for every layer `Same (BQ (J), BQ_Ref (C, Ch, J))`. The rest of its contract does not change.
- **`BQ_Ref`** is a ghost function of `Sumcheck_Verifier`. It reads the terms of the layer and the challenges from `Ch`, as `Verify_Layer` does. It is `EBQT_Ref` when the layer fits the eq tables, and `EBQ_Ref` otherwise, the same split as the verifier's.
- **`Sumcheck_Verifier.Bound_Quads`** is a new pass of the verifier, between `Replay_Challenges` and `Verifier_Core`. It computes the bound quads with `Eval_Bound_Quad_T`, or `Eval_Bound_Quad` beyond the tables, as `Verify_Layer` did. It is Gold against `BQ_Ref`.
- **`Verifier_Core`** takes the bound quads as an input, as upstream's `aux`. Its precondition, at the level `Proof_Only`, states `Same (BQ (J), BQ_Ref (C, Ch, J))` for every layer. The verifier discharges it from `Bound_Quads`, the prover from `Prove`. The rest of its contract does not change.
- **Beyond `Max_Bindeq_Log`** the prover calls `Eval_Bound_Quad`, the term-by-term evaluation. No circuit in use comes near.

**The proof.** The postcondition of `Prove` comes from an invariant on coefficients, kept round by round.

- `Bindeq_Ref (C, K, I)` takes the low bit of I with `C (K)` first. `Bind_H` binds the low bit of a hand at each round, in the same order. So each round of `Bind_H` turns a factor of `Bindeq_Ref` into a factor of the coefficient.
- The challenges of later rounds are not drawn yet when a round is bound. The invariant therefore speaks of coefficients, not of the sum with the final challenges.
  - For every pair of residual indices `(a, b)`, the sum of the coefficients of the terms left with those hands
  - equals the sum, over the terms of the layer with that residue, of `Bound_KT` times the factors of the challenges already drawn.
- Each step uses a contract that is already Gold: `Bind_G_T` (the coefficient is `Bound_KT`), `Merge_Runs` (`Run_Sum` over terms with the same hands), `Bind_H` (`Corner_K` over the corners that `Rd` names).
- After `Logw` rounds of each hand, `Fits` leaves only the residue `(0, 0)`, and the invariant is the postcondition.
- The lemmas live in a ghost package of `Sumcheck_Prover`, at the level `Proof_Only`. The field laws of ADR 0070 carry the algebra, through new lemmas of `Ring_Laws`.

**How the proof is made to fit the provers.** The first attempt proved on GF(2^128) but not on P-256, where the context of every product is heavier. Five rules came out of it:

- Every ghost statement on elements uses `Same`, never the predefined `=`.
- The ghost sums use the hidden wrappers of `Sumcheck_Algebra`, not the operations of the field. Two lemmas restate the postconditions of `Bind_H` and `Merge_Runs` in that form: `Corner_W` and `Run_Sum_W`.
- The invariant is a hidden function, read through a lemma. Unfolded, its double quantifier sinks the loop.
- The invariant speaks of the terms of the circuit and the challenges, not of a ghost copy of the term array. So it can sit in the contract of an ordinary procedure: SPARK refuses a ghost formal on a non-ghost procedure.
- The work of a layer is split into three procedures, each with a small context:
  - `Merge_Terms` calls `Merge_Runs` and establishes the invariant;
  - `Bind_Round` stores the challenge of a round and calls `Bind_H`, with the invariant before and after;
  - `Prove_Layer` runs one layer and returns its bound quad.

**Changes to executable code.** None changes a value.

- The three procedures above. `Prove` keeps its loop over the layers, which now calls `Prove_Layer`.
- `Bind_Round` stores the challenge in `Ch.Layer` and in the vector of the hand. The order of the stores changes, not their values.
- A Boolean records whether the layer fits the eq tables, because a ghost condition cannot guard ordinary statements.
- At the end of each layer, one pass over the remaining terms sums their coefficients.

## Alternatives considered

- **Reuse, tested only.** The contracts of `Prove` and `Verifier_Core` are Silver, so no contract would move. But the value would move from a Gold function to an unproved one. Rejected for M2 by ADR 0067. It would be the fallback if the proof fails, and then a decision of its own.
- **Keep the recomputation.** Rejected: 40.8 M products, about 1.2 s of 9.8 s on the reference VM, for a value the prover already has.
- **`Verifier_Core` with no precondition on the bound quads.** Its contract is Silver, so it would stay true. But the value it trusts would not be named in any contract, and a reader of the code would have to find the chain through `Zk_Verifier` and `Zk_Prover`. The precondition states it where the value is used.
- **A postcondition on the sum with the final challenges, by a ghost history of the term arrays.** Each round would be related to the next for arbitrary later challenges, and the chain applied at the end of the layer. It needs a sequence of arrays in ghost code. The invariant on coefficients needs none.

## Consequences

- Field products on the hash circuit of mdoc v7, counted in an instrumented copy:

| | before | after | upstream |
|---|---|---|---|
| prover, verifier core | 41.13 M | 0.30 M | 0.20 M |
| prove, total | 143.1 M | 102.3 M | 93.3 M |
| verify, total | 59.6 M | 59.6 M | 36.6 M |

- The proofs of the CLI stay identical byte for byte. The value is the same field element.
- `prover_kat` compares, on every layer of every test circuit, the bound quad of `Prove` with that of `Bound_Quads`.
- Guide chapters 3 and 7, the trust model and the CHANGELOG are updated.

## Verification impact

- `Prove` gains a functional postcondition, Gold. The rest of the contract of `Sumcheck_Prover` stays Silver, as now.
- `Bound_Quads` is Gold against `BQ_Ref`.
- `Verifier_Core` gains a precondition. Its level does not change.
- `Sumcheck_Verifier`, `Zk_Prover` and `Zk_Verifier` are proved again. Their levels do not change.
- No `pragma Assume`, no weaker contract.

## References

- [ADR 0052](0052-gold-perimeter-for-the-prover.md), [ADR 0063](0063-milestone-m1-algorithmic-parity.md), [ADR 0067](0067-performance-milestones-by-trust.md), [ADR 0070](0070-sumcheck-and-ligero-kernels-as-upstream.md).
- google/longfellow-zk at d5e6be7:
  - `rust/runtime/sumcheck/src/prover.rs` (`prove_core`, `SumcheckProofAux`);
  - `rust/runtime/zk/src/symbolic_sumcheck_verifier.rs` (`aux`, `bind_quad`).
