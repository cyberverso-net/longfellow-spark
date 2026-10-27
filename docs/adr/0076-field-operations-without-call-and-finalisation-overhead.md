# 0076 The field operations without call and finalisation overhead

## Status

Proposed (2026-10-27, milestone M2 of Phase D).

## Date

2026-10-27

## Context

The profiles of the close of M2 compare this project with upstream's generic code on the proving machine, item by item (notes of 27 October). Two costs are this project's own, and neither is work the protocol needs.

- **The GF(2^128) operations are calls.**
  - `GF2_128.Add`, `Sub`, `Neg` and `Mul` have no `Inline` aspect. In the release build `Add` and `Sub`, one xor per limb, are out-of-line calls: 151 and 83 call sites in the command-line prover. `Mul` is a call too, around the call of `Clmul_Kara`.
  - The protocol code reaches them through the wrappers of `Sumcheck_Algebra`, which are inlined. The wrappers then call the field.
  - Upstream inlines its field operations into the loops.
- **The P-256 operations run finalisation code that the proof left behind.**
  - `Add_Mod`, `Sub_Mod`, `Mul_Row` and `Mont_Mul` hold assertions on `Big_Integer` terms, at the assertion level `Proof_Only`, which is never compiled.
  - GNAT still allocates the finalisation nodes of the temporaries of those assertions when the assertion is a conditional or short-circuit form (`if`, `and then`, `or else`) or a loop invariant, and when a ghost call takes a `Big_Integer` term as an actual. The assertion is removed; the nodes and a finaliser stay.
  - Every `Add` and `Sub` of P-256 runs that finaliser: two indirect calls into the run-time library (`abort_defer`, `abort_undefer`) and nine tests. The loop of `Mont_Mul` runs one at each of its four iterations.
  - The two calls alone take 12 % of the signature proof and 14 % of the signature verification on the proving machine.

## Decision

- **`Inline` on the GF(2^128) operations** `Add`, `Sub`, `Neg` and `Mul`. The contracts do not change. `Clmul_Kara` stays a call: it is about 650 instructions, and the product is already bound by its multiplications.
- **No `Big_Integer` temporaries in the compiled bodies of P-256.**
  - The proofs of `Add_Mod` and `Sub_Mod` move into ghost lemmas on their limbs, `Lemma_Add_Mod` and `Lemma_Sub_Mod`. The precondition of each lemma states what the body computed: the calls of `Add_Limbs` and `Sub_Limbs` and the selected result. The lemma's body holds the assertions the function held, and its postcondition is the function's.
  - The conjunctions on `Big_Integer` terms in `Mul_Row` and in the loop invariant of `Mont_Mul` are split into separate assertions and invariants.
  - The last step of `Mont_Mul` goes through `Lemma_Mont_Close`, which takes the words and forms the `Big_Integer` terms that `Lemma_Mont_Final` needs.
  - The contracts of the four functions do not change.
- **The rule for later code:** in a compiled body, a `Big_Integer` term appears only in a simple assertion. Conditional and short-circuit forms, conjunctions in loop invariants, and `Big_Integer` actuals of ghost calls go into a ghost lemma. The expanded code (`-gnatG`) shows whether a body keeps finalisation nodes.

## Alternatives considered

- **A compiler switch.** None is known that removes the nodes of ignored assertions. The level `Proof_Only` is already static.
- **Inline `Clmul_Kara` as well.** Not taken: 179 call sites of `Mul` would each copy it. To be measured with the hardware variant of M3.
- **A ghost model on a non-controlled integer type.** It would remove the finalisation everywhere, but it changes the model of the whole P-256 proof.

## Consequences

- Measured on the proving machine (c4-standard-24), proved build, mdoc v7, median of three runs in one session: main d625209, then the inlining alone (2fcf767), then both changes (9ef47a3):

  | | before | inlined | both | change |
  |---|---|---|---|---|
  | hash prove | 5.08 s | 4.87 s | 4.85 s | -0.23 s (-5 %) |
  | hash verify | 2.59 s | 2.44 s | 2.44 s | -0.15 s (-6 %) |
  | sig prove | 0.62 s | 0.62 s | 0.53 s | -0.09 s (-15 %) |
  | sig verify | 0.39 s | 0.39 s | 0.33 s | -0.06 s (-15 %) |
  | round trip | 8.68 s | 8.32 s | 8.15 s | -0.53 s |

- The P-256 operations on their own, same machine, ns per operation: `Mul` 37.3 before and 32.7 after, `Add` 12.8 and 10.8, `Sub` 11.6 and 9.5. Upstream's generic code for the baseline processor takes 11.4 ns for a product and 2.0 ns for a sum: the P-256 arithmetic is still about three times slower than upstream's, with the same algorithm.
- The proofs of the command line stay identical byte for byte: the computed code is the same.
- Guide chapter 2 records the rule, and the CHANGELOG the change.

## Verification impact

- No contract changes. The proofs move from the bodies into three lemmas, with the same assertions.
- No `pragma Assume`.

## References

- [ADR 0044](0044-field-contracts-at-proof-only-level.md), [ADR 0067](0067-performance-milestones-by-trust.md), [ADR 0068](0068-release-build-without-run-time-checks.md), [ADR 0069](0069-p256-montgomery-multiplication.md), [ADR 0070](0070-sumcheck-and-ligero-kernels-as-upstream.md).
- The notes of 27 October: the gap analysis with upstream (`measure-2026-10-27-gap`).
