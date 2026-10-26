# 0073 The verifier binds the quad of each layer as upstream does

## Status

Proposed (2026-10-26, milestone M2 of Phase D).

## Date

2026-10-26

## Context

After ADR 0072 the verifier takes 5.06 s on the hash circuit of mdoc v7. 1.72 s of it is `Bound_Quads`, the bound quad of each layer, computed with `Eval_Bound_Quad_T`. The verifier does 59.6 M field products in all, upstream's 36.6 M.

The two compute the bound quad differently.

- Ours evaluates the sum term by term: `Bound_KT (t)` times the eq factors of the two hands, read from the eq tables. That is about three products per term of the layer.
- Upstream's `bind_quad` (`symbolic_sumcheck_verifier.rs`) calls `HQuad::bind_g`, then `bind_h` once per hand and round, and reads the scalar left. That is the path of its prover: one product per term for g, then the terms merge and shrink with each round.

Our prover takes upstream's path since M1: `Bind_G_T`, `Merge_Runs`, `Bind_H`. ADR 0071 proved that the scalar it leaves equals `EBQT_Ref`, by an invariant on coefficients kept round by round. The verifier can take the same path with the same proof. Only the place of the code stands in the way: the kernels and their lemmas live in `Sumcheck_Prover`, which is generic over the sampling of the prover, and the verifier cannot depend on it.

## Decision

**The kernels of the bound quad move to a new generic, `Sumcheck_HQuad`, and the verifier uses them as the prover does.**

- **`Sumcheck_HQuad`** is generic over `Sumcheck_Algebra`. It holds:
  - the kernels `Bind_G_T`, `Merge_Runs` and `Bind_H`, with their references `Run_Id`, `Run_Sum`, `Same_Hands`, `Two`, `Rd` and `Corner_K`, and their contracts unchanged;
  - the ghost package of ADR 0071, with the invariant and its lemmas, unchanged;
  - `Merge_Terms`, unchanged;
  - a new procedure `Bind_Quad`, the verifier's form: the terms of a layer and all its challenges in, the bound quad out. Its postcondition is `Same (V, EBQT_Ref (...))`, proved with the same invariant.
- **`Sumcheck_Verifier`** instantiates it, and `Bound_Quads` calls `Bind_Quad` when the layer fits the eq tables. Beyond them it keeps `Eval_Bound_Quad`. Its contract does not change: Gold against `BQ_Ref`.
- **`Sumcheck_Prover`** uses the instance of the verifier. `Bind_Round` and `Prove_Layer` stay in it, because they store the challenges of the transcript. Their contracts do not change.
- `Bind_Quad` works on a copy of the layer's terms on the heap, as the prover does. One buffer per layer, freed on every path.
- `Eval_Bound_Quad_T` stays as a Gold kernel. No unit of the program calls it any more. `sumcheck_kat` keeps comparing it, and the term-by-term `Eval_Bound_Quad`, with the bound quads of the verifier.

## Alternatives considered

- **Keep the evaluation term by term.** Rejected: 8.3 M products of the verifier, for an algorithm whose proof already exists in the project.
- **A second copy of the kernels in the verifier.** Rejected: two copies of the same Gold code and lemmas to keep in step, and twice the proof time.
- **Move the kernels into `Sumcheck_Algebra`.** It is already large, and every unit that uses it would carry the lemmas of ADR 0071 into its proof context. A unit of its own keeps them where they are used.

## Consequences

- Field products on the hash circuit, counted on the development machine:

  | verify | before | after | upstream |
  |---|---|---|---|
  | bound quads | 40.84 M | 32.59 M | 30.87 M, with the core |
  | verifier core | 0.30 M | 0.30 M | |
  | Ligero verify | 18.44 M | 18.44 M | 5.70 M |
  | total | 59.6 M | 51.3 M | 36.6 M |

  The bound quads are now within 6 % of upstream. What remains of the gap is the encoding of the Ligero verifier, which upstream does by FFT: a candidate for M3. The prover is unchanged at 102.3 M.
- The first estimate, about 37 M products, assumed that the merged terms would remove most of the work. They remove a fifth: the work of `bind_h` over the rounds stays.
- Measured on the proving machine (c4-standard-24), proved build, mdoc v7, median of three runs in one session, 555baa0 against 947d48a:

  | | before | after | change |
  |---|---|---|---|
  | hash prove | 7.71 s | 7.69 s | 0 |
  | hash verify | 5.17 s | 4.90 s | -0.27 s (-5 %) |
  | sig prove | 0.88 s | 0.88 s | 0 |
  | sig verify | 0.63 s | 0.62 s | 0 |

  The gain in time is smaller than the gain in products. Reading the circuit now takes about half of the hash verification, most of it in the hash of the circuit id. Upstream verifies the same proof in 1.17 s with its generic field code.
- The proofs of the CLI stay identical byte for byte. The value is the same field element.
- The verifier allocates on the heap one copy of the terms of the largest layer, as upstream does.
- `prover_kat` compares the bound quads of the prover and the verifier, which now share their kernels. `sumcheck_kat` compares them with `Eval_Bound_Quad_T` and `Eval_Bound_Quad`, which do not share any.
- Guide chapters 3 and 7, the trust model and the CHANGELOG are updated.

## Verification impact

- The kernels and lemmas are proved once per field, in `Sumcheck_HQuad`, instead of in `Sumcheck_Prover`.
- `Bind_Quad` is new and Gold. `Bound_Quads` stays Gold against `BQ_Ref`.
- `Sumcheck_Prover`, `Sumcheck_Verifier` and their callers are proved again. Their levels do not change.
- `Sumcheck_Verifier` instantiates `Sumcheck_HQuad` before its `use` clauses. With the operators of `Sumcheck_Algebra` directly visible, the instance resolves one subtraction of `Corner_K` to the opaque wrapper instead of the field operation, and the lemmas of the corners no longer apply. A comment at the instantiation says so.
- `Lemma_V_End_All`, new, states the inductive step of both sums as two assertions; without them the P-256 instance does not close.
- The hardest proof observed is the postcondition of `Lemma_Bind_H_Step` on P-256: 499341 steps on the development machine, under the budget of 600000 (ADR 0020), with or without this change. The last gate on the proving machine, before this change, reported a maximum of 463202. The comment of the project file is updated.
- No `pragma Assume`, no weaker contract.

## References

- [ADR 0063](0063-milestone-m1-algorithmic-parity.md), [ADR 0067](0067-performance-milestones-by-trust.md), [ADR 0071](0071-prover-reuses-the-bound-quad.md).
- google/longfellow-zk at d5e6be7:
  - `rust/runtime/zk/src/symbolic_sumcheck_verifier.rs` (`bind_quad`);
  - `rust/runtime/sumcheck/src/hquad.rs` (`bind_g`, `bind_h`, `scalar`).
