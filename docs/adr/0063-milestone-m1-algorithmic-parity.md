# 0063 Milestone M1: algorithmic parity with the production verifier and prover

## Status

Proposed (2026-10-21, at the start of milestone M1 of Phase D). Amended 2026-10-22 by [ADR 0066](0066-lagrange-tables-by-prefix-and-suffix.md): the verifier's Lagrange tables are built by prefix and suffix products instead of barycentric weights. M1 closed at about 126 s ([ADR 0067](0067-performance-milestones-by-trust.md)).

## Date

2026-10-21

## Context

[ADR 0055](0055-phase-d-scope-mdoc-scale.md) sets the goal of a round trip under one second for the two mDoc proofs and their verifications, by milestones. M1 is algorithmic parity: the same amount of work as the production code, with the multiplication as it is today.

The profiles of block 4 show where the work goes. The verifier core spends most of its time in `Eval_Bound_Quad`, which computes eq bit by bit for every term, about 70 multiplications per term. The production code (`rust/runtime/sumcheck/src/eq.rs`, `hquad.rs`) builds the eq2 table once per layer and reads it, about 3 multiplications per term. The input constraint computes `Eq2` for every input in the same way.

This project's kernels are Gold against ghost references that transcribe the specification's formulas, and the Gold is structural: the provers do not know the field laws ([ADR 0023](0023-gold-perimeter-for-protocol-code.md)). That a table of bindeq equals eq bit by bit is an algebraic identity, tested today and not proved. So a table-based form cannot be proved against the existing references.

## Decision

- **Two forms of each kernel, as for the FFT** ([ADR 0057](0057-additive-fft.md)). The existing kernel stays in the code with its Gold against the specification, as the reference. The fast kernel gets its own structural Gold against a reference written in its own form, and the code uses it. The harnesses compare the two, and the proofs stay identical byte for byte.
- **The bound quad.** `Eval_Bound_Quad_T` builds E = bindeq (G0) + alpha bindeq (G1) over 2^logv entries (`Eq2_Table`) and the bindeq tables of the two hands' challenges over 2^logw, on the heap, then sums over the terms with 3 multiplications each. Its Gold is against `EBQT_Ref`, the same sum written with `Bindeq_Ref`, which transcribes the recursive definition of Section 6.2. The only tested fact behind it is the one already in the trust model: bindeq agrees with eq.
- **The input constraint.** Its coefficients come from the same eq2 table. Its Gold postcondition, set in block 2 on `Eq2`, moves to `In_Coef`: the table form when it fits, `Eq2` otherwise.
- **The fallback.** When logv or logw exceeds 24, the limit of `Bindeq`, the verifier uses the term-by-term form. Real circuits do not reach it, since a layer has at most 2^24 wires.
- **The table lengths.** The provers do not bound 2**L for a variable L, so `Table_Len` computes 2^L by doubling, with its value proved equal to `Pow2 (L)` and at most 2^24.
- **The next steps of M1**, each with the same rule: the sumcheck prover realigned with the production one (dense round polynomial and merged corners, `quad_round_poly` and `bind_h`), and barycentric weights in the verifier's Lagrange tables.

## Alternatives considered

- **Prove that the table equals eq.** It needs the field laws as axioms, or a proof per field, which changes the method of the whole stage 3. Out of scale for this milestone.
- **Replace the reference.** One kernel, Gold against the table form, and the specification form gone. It loses the executable reference the harnesses compare against.

## Consequences

- `Sumcheck_Algebra` gains `Table_Len`, `Eq2_Table`, `Beq`, `Beq2`, `Bound_KT`, `EBQT_Ref` and `Eval_Bound_Quad_T`; `Sumcheck_Verifier` gains `In_Coef` and uses the tables in `Verify_Layer` and `Input_Constraint`.
- `sumcheck_kat` compares the two bound quads on every layer of every test circuit.
- The tables take memory: up to four tables of 2^logw elements while a layer is checked.

## Verification impact

- Proved: the fast bound quad and the input coefficients against the bindeq form of Section 6.2; absence of run-time errors and the ownership checks on the tables.
- Tested: the two forms agree (the harness, the byte identity of the proofs, the recorded upstream runs).
- Trusted: unchanged; the agreement of bindeq with eq was already a tested fact.

## References

- [ADR 0023](0023-gold-perimeter-for-protocol-code.md), [ADR 0055](0055-phase-d-scope-mdoc-scale.md), [ADR 0056](0056-linear-input-constraint.md), [ADR 0057](0057-additive-fft.md).
- google/longfellow-zk at d5e6be7: `rust/runtime/sumcheck/src/eq.rs` (`eq2`, `fill_recursive`), `hquad.rs` (`bind_g`, `bind_h`), `prover.rs` (`layer`, `quad_round_poly`), `dense.rs`.
