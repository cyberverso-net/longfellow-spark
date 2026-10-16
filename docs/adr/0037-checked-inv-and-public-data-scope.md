# 0037 Checked_Inv, and the public-data scope of the Ligero units

## Status

Accepted (2026-10-15, before block 2 of stage 5)

## Date

2026-10-15

## Context

`GF2_128.Inv` and `P256_Field.Inv` are Silver: a fixed Fermat chain, total with `Inv (Zero) = Zero`, their correctness anchored by known-answer vectors ([ADR 0008](0008-inv-fixed-chain-total-function.md), [ADR 0016](0016-p256-inversion.md)). Until now no verification path called them: the Lagrange denominator inverses of stage 3 are constants checked by the harness. The Lagrange table of [ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md) needs the inverse of k products of differences of distinct evaluation points, computed at run time, on public data.

The constant-time discipline of [ADR 0006](0006-constant-time-discipline-and-scope.md) covers the field arithmetic because the prover will run it on secrets; [ADR 0029](0029-sha256-and-aes256-in-spark.md) declared it not applicable to the transcript and its primitives, which process the public content of a proof string.

## Decision

- Each field wrapper (`Field_GF2_128`, `Field_P256`) gains `Checked_Inv (D : Element; R : out Element; Ok : out Boolean)` with `Post => (if Ok then R * D = One)` through the field's own multiplication and equality, proved by definition: the body computes `Inv (D)`, multiplies back and compares. `Ok` is False on `D = Zero` and on a failed product check, that is on any case in which `Inv` did not return the inverse; nothing is assumed about `Inv`. `Field_Signature` gains the formal.
- The Lagrange table construction calls `Checked_Inv` for the k denominators and propagates a failure as the status `Matrix_Failed` ([ADR 0039](0039-sizes-allocation-and-status.md)); the denominators are never zero for distinct points, so the status is unreachable on a correct field, and the proof does not depend on that.
- The constant-time discipline is declared not applicable to the units of stage 5 (Merkle, geometry, code, Ligero verifier, readers, complete verifier), with the wording of ADR 0029 in each header: they process the proof string and the public inputs; they must not be given secret data; a prover will not reuse them on secrets without a new decision.

## Alternatives considered

- **Calling `Inv` directly, trusting its vectors.** Rejected: a wrong inverse would give a wrong table and a wrong verdict with no observable failure; the product check costs one multiplication per denominator, once per geometry, and turns the trusted item into a proved one.
- **Proving `Inv` Gold.** Not pursued (ADR 0008, ADR 0016): Fermat's theorem is out of SMT reach; the run-time check gives the verifier the same guarantee where it needs it.
- **Precomputed denominators for the known geometries.** Rejected: the configuration is an input and the tables depend on it.

## Consequences

- The README trust model moves "Inv computes the inverse" from tested to proved where it matters: on the verification path, every inverse used is checked, and the item left trusted is only that `Inv` succeeds on a correct field (a failure is a reported status, not a wrong verdict).
- Two multiplications more per denominator (the check, and the one the table needs anyway).

## Verification impact

- Provable: `Checked_Inv`'s postcondition, by definition; the table's entries use only checked inverses.
- Tested: that `Inv` does succeed (the status never fires on the vectors).
- Trusted: nothing new; the item on `Inv` weakens as above.
- Constant time: declared not applicable to stage 5, with the reason in each header.

## References

- [ADR 0006](0006-constant-time-discipline-and-scope.md), [ADR 0008](0008-inv-fixed-chain-total-function.md), [ADR 0016](0016-p256-inversion.md), [ADR 0029](0029-sha256-and-aes256-in-spark.md), [ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md).
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/algebra/interpolation.rs` (`d.inv()`).
