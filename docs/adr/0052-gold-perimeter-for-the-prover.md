# 0052 Gold perimeter for the prover

## Status

Proposed (2026-10-17, block 1 of Phase C)

## Date

2026-10-17

## Context

The Gold of stages 3 and 5 is structural ([ADR 0023](0023-gold-perimeter-for-protocol-code.md), [ADR 0038](0038-gold-perimeter-for-merkle-and-ligero.md)): a procedure is proved equal to a ghost transcription of the reference's formula in a fixed order, or proved to produce a shape, and what the formula means for the protocol is tested. The prover produces the objects the verifier consumes, so its natural specifications are the verifier's own: the writers against the readers, the padded proof against the core's recomputation, the tableau against the geometry, the opening against `Merkle.Verify`.

## Decision

Silver everywhere. Gold, structural, on:

- **The writers as inverses of the readers.** For the sumcheck proof (Section 7.3, `Read_Sumcheck_Proof` of stage 4), the Ligero proof (Section 7.4, `Ligero_Proof.Read`) and the complete proof (Section 7.5, `Zk_Verifier.Read_Proof`): `Read (Write (P)) = P` with status `Ok`, the length of `Write (P)` as the reader expects, stated through the logical equality `Same` on the elements where the predefined equality is not extensional (ADR 0023). The run-length structure of Section 7.4 that the writer chooses by position ([ADR 0051](0051-constant-time-in-the-prover.md)) must be one the reader accepts: the postcondition of the writer states the reader's rules, `Well_Coded` of `Ligero_Proof` (runs alternate from a full-field run, a zero-length run only first and only once, the runs cover exactly the NROW times NREQ elements), on the bytes it produces.
- **The round evaluations of the sumcheck prover** equal to a ghost reference transcribing `eval_round_poly` of `sumcheck/prover.rs` in its order of operations, as `Eval_Bound_Quad` and `Bind_G` are to theirs in stage 3; the padded values equal to the evaluations minus the pads; the layer's claims equal to the first element of each bound hand minus its pad. If this Gold does not close within the step budget, the fallback of stage 5's Merkle applies: Silver with the vectors of [ADR 0053](0053-prover-vectors-and-cross-verification.md), and the decision is recorded, taken with the author and not alone.
- **The shapes of the tableau and the opening.** The tableau has NROW rows of NCOL elements; row IW + i holds the witnesses i WR .. i WR + WR - 1 at positions NREQ onwards of its unencoded row, zeros beyond NW; the quadratic rows hold the triples at the positions of Section 4.3; the opening produces exactly the digests `Merkle.Verify` consumes for the chosen indices (its ghost `Path_Flags` and `Missing` model, ADR 0038), so that `Verify (Build, Open)` accepts, stated as a postcondition of `Open` in that model.

Not Gold, tested: completeness, that the honest prover's proof satisfies every check of the verifier (byte identity with upstream and acceptance by both verifiers, ADR 0053); the zero-knowledge of the construction (the paper's theorem, with ADR 0050's statement on the source).

## Alternatives considered

- **Proving completeness.** Not taken: it is the statement that the Ligero tests, the sumcheck recomputation and the Merkle verification all pass on the honest prover's output, a theorem about the protocol rather than about the code (Platinum, excluded by ADR 0003), and the two verifiers test it on every proof.
- **Gold on the Reed-Solomon encoding against the interpolation property.** Not taken: `Lagrange.Build` is already Gold on its formula and the interpolation property is tested (ADR 0036, ADR 0040); the encoder is the same linear combination on all columns.

## Consequences

- Each prover unit's header lists its Gold kernels and the fallback if one is taken.
- The readers gain nothing; their contracts are the writers' specifications.
- The `prover` partition carries the new checks; chapter 7 reports them.

## Verification impact

- Provable: the round trips, the round evaluations, the shapes, the opening in the model of `Merkle.Verify`.
- Tested: completeness, byte identity, the negative cases.
- Trusted: unchanged.
- Constant time: ADR 0051.

## References

- [ADR 0003](0003-proof-policy-and-trust-model.md), [ADR 0023](0023-gold-perimeter-for-protocol-code.md), [ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md), [ADR 0038](0038-gold-perimeter-for-merkle-and-ligero.md), [ADR 0049](0049-phase-c-scope-the-prover.md), [ADR 0053](0053-prover-vectors-and-cross-verification.md).
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/sumcheck/prover.rs` (`eval_round_poly`, `sumcheck_prove_layer`), `merkle.rs` (`open_merkle_heap`), `ligero/prover.rs` (`layout_tableau`).
