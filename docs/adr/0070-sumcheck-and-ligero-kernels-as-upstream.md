# 0070 The sumcheck and Ligero kernels in upstream's form

## Status

Proposed (2026-10-23, milestone M2 of Phase D).

## Date

2026-10-23

## Context

The release build of ADR 0068 takes about 11.4 s to prove the hash circuit of mdoc v7 on the reference VM. Upstream's generic build takes 2.7 s. The GF(2^128) product is not the gap: ours takes 34 ns on the VM, upstream's generic one 38 ns. The gap is in the number of products.

Field products on that circuit, counted per phase in instrumented copies of both programs:

| phase | ours | upstream |
|---|---|---|
| prover sumcheck | 106.3 M | 70.7 M |
| prover Ligero, `y_dot` | 5.7 M | 1.5 M |
| verifier core, recomputed by the prover | 63.4 M | 0.2 M |
| verifier core | 63.4 M | 30.9 M |

Inside the prover sumcheck:

| kernel | ours | upstream | cause |
|---|---|---|---|
| dense bind | 13.8 M | 6.9 M | `(1 - x) a + x b`, two products; upstream `a + x (b - a)`, one |
| binding of g | 29.4 M | 14.5 M | `Bindeq` writes `c t` and `(1 - c) t`, two products per entry; upstream writes `w g` and `w - w g`, one. `Eq2_Table` builds two tables then adds `alpha` times the second; upstream fills both in one pass, starting the second from `alpha` |
| round evaluations | 46.9 M | 33.1 M | four products per pair; upstream two |
| binding of a hand | 16.2 M | 16.2 M | equal |

In Ligero, the prover encodes the whole row of each witness block for `y_dot`, but it reads only the first `dblock` columns. Upstream interpolates to `dblock` only.

The prover recomputing the verifier core is a different question, the reuse of the bound quad. A later ADR covers it.

The stop criterion of ADR 0067 asks for upstream's algorithm wherever the proof allows it.

## Decision

**The kernels take upstream's form. Their contracts do not change.** Only the bodies change, and they are proved again, Gold, against the same references.

- **Dense bind (`Sumcheck_Algebra.Bind`):** `B (I) := A0 + X * (A1 - A0)`, one product. The Post keeps `(One - X) * A0 + X * A1`.
- **`Bindeq`:** `B (2 I + 1) := C (K) * T` and `B (2 I) := T - B (2 I + 1)`, one product per pair. The Post keeps `Bindeq_Ref`.
- **`Eq2_Table`:** both tables are filled in the same pass, the second starting from `Alpha` instead of `One`. Then one addition per entry, with no product. The Post keeps `Beq2`.
  - A ghost lemma states that the table started from `W` is `W` times `Bindeq_Ref`.
  - `Eval_Bound_Quad_T` uses `Eq2_Table` and `Bindeq`, so the verifier gains too.
- **Round evaluations (`Round_Evals_Dense`):** three products per pair instead of four.
  - The loop accumulates `a0 = sum Q0 W0`, `s1 = sum Q1 W1` and `a2 = sum (Q1 - Q0) (W1 - W0)`.
  - After the loop, `Ev2 := a0 + X2 (s1 - a0 - a2) + X2^2 a2`.
  - This is a local polynomial identity. The Post keeps `D0_Ref` and `D2_Ref`.
- **Ligero `y_dot`:** `Encode_Row` writes into `A_Enc (0 .. dblock - 1)`, so the FFT extends the row to `dblock` columns only. The Pre of the FFT path already allows an output shorter than the code word.

**`Field_Signature` gains the ring laws that the new bodies need.** Today it has only associativity of the product (ADR 0066). The new bodies also need:

- commutativity of the product;
- distributivity of the product over `+` and `-`;
- `One` as the unit of the product;
- the laws of `+` and `-` that the rewritings use: associativity, commutativity, and `(A - B) + B = A`.

Each is a ghost lemma, `Proof_Only`. Each field proves it against its own model:

- GF(2^128) against `Mul_Ref` and the exclusive or of the limbs;
- P-256 against the integer model through `Value` (ADR 0069).

## Alternatives considered

- **Round evaluations with two products per pair, as upstream.** `a1` then comes from the claimed sum of the round: `p (1) = claim - p (0)`. The identity holds only under the protocol invariant that the claim is the true sum. Proving that means a new contract for `Round_Evals_Dense` and an invariant across the prover's rounds. That would save about 12 M more products. It is left for a later step, once the three-product form is in.
- **Delayed reduction.** Upstream accumulates unreduced products (`mac`, `accum_reduce`) and reduces once per sum. That is a change to the field interface, not to the kernels. Out of scope here.
- **Keep the bodies and accept the gap.** Rejected. The proof cost is a few ring laws per field, and the kernels then match upstream line by line.

## Consequences

- Estimated saving on the hash circuit: about 38 M products in the prover, about 1.3 s on the VM. The verifier also gains through `Eval_Bound_Quad_T`.
- The proofs of the CLI stay identical byte for byte. The bodies compute the same field elements.
- `Field_GF2_128` and `Field_P256` pass the new lemmas. Each field package proves them next to `Lemma_Mul_Assoc`.
- A test checks the FFT extension to `dblock` against the first `dblock` entries of the full extension, for both fields.
- Guide chapters for the sumcheck and Ligero, the trust model and the CHANGELOG are updated.

## Verification impact

- `Sumcheck_Algebra`, `Sumcheck_Prover`, `Ligero_Prover`, `GF2_128` and `P256_Field` are proved again. The levels stay as they are: Gold for the kernels, Gold for the new lemmas.
- No `pragma Assume`, no weaker contract.
- The FFT parity part stays tested, as in ADR 0057. The shorter extension adds no proof obligation on it.

## References

- [ADR 0057](0057-additive-fft.md), [ADR 0066](0066-lagrange-tables-by-prefix-and-suffix.md), [ADR 0067](0067-performance-milestones-by-trust.md), [ADR 0068](0068-release-build-without-run-time-checks.md), [ADR 0069](0069-p256-montgomery-multiplication.md).
- google/longfellow-zk at d5e6be7:
  - `rust/runtime/sumcheck/src/dense.rs` (`bind`);
  - `rust/runtime/sumcheck/src/eq.rs` (`fill_recursive`);
  - `rust/runtime/sumcheck/src/hquad.rs` (`bind_g`);
  - `rust/runtime/sumcheck/src/prover.rs` (`quad_round_poly`);
  - `rust/runtime/ligero/src/prover.rs` (`dot_proof`).
