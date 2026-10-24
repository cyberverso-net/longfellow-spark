# 0066 The verifier's Lagrange tables by prefix and suffix products, proved

## Status

Proposed (2026-10-22, milestone M2 of Phase D). Amends the last item of the decision of [ADR 0063](0063-milestone-m1-algorithmic-parity.md): the verifier's Lagrange tables are built from prefix and suffix products, not with barycentric weights. Amended 2026-10-23 by [ADR 0070](0070-sumcheck-and-ligero-kernels-as-upstream.md): the limbs of a P-256 element are scalar components, so equal limbs give equal elements, and `Norm` leaves the code.

## Date

2026-10-22

## Context

After the new multiplication ([ADR 0065](0065-carry-less-multiplication-in-gf2-128.md)), the two Lagrange tables of the Ligero verifier take most of each verification on the proving machine ([ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md)):

- 64% of the 18 s of the mDoc hash verification, on GF(2^128);
- 96% of the 46 s of the mDoc signature verification, on P-256.

The cost comes from the way the tables are built:

- each entry T (i, x) recomputes the product over j /= i of (x - p_j), so a table of dimension K costs about K² · NREQ multiplications;
- each difference recomputes both evaluation points, so on GF(2^128) `Inject` alone takes 27%.

Upstream's verifier has no tables. It extends each row with the prover's FFT and gathers the queried columns (`interpolate_req_columns` and `dot_check` in `rust/runtime/ligero/src/verifier.rs` at d5e6be7). Doing the same here would move a proved fact to a tested one: that the verifier's polynomial side is the Lagrange encoding of Section 4.3. The FFT is tested against Lagrange, not proved ([ADR 0057](0057-additive-fft.md)), and proving it needs the algebra of LCH14 and of the real FFT, which is out of scale.

The products can be shared without changing a value. For each queried column x:

- the prefix products, from One, j ascending: P (i) = (x - p_0) ... (x - p_(i-1));
- the suffix products, from the right: S (i) = (x - p_(i+1)) (... (x - p_(K-1)));
- the product of row i is P (i) S (i), and P (K - 1) alone for the last row.

That P (i) S (i) equals the product of today, a left fold from One that skips i, needs one law of the field: the associativity of the product.

## Decision

- **The tables are built from prefix and suffix products.**
  - For each queried column, one backward pass makes the suffix products and leaves them in the column of the table itself, and one forward pass makes the prefix products and the entries P (i) S (i) Inv_D (i). No memory is added.
  - Each pass computes its evaluation points as it goes, 2 K per column, which is negligible beside the old 2 K² · NREQ.
  - The denominators are computed as today, once per row.
  - A table costs about K² + 3 K · NREQ multiplications instead of K² · NREQ.
- **The contracts do not change.** `Lagrange.Build` keeps its Gold postcondition against `Diff_Product_Ref`, and `Ligero_Verifier` keeps all of its contracts. Only the body of `Build` changes.
- **The associativity of the product, proved per field.**
  - `Field_Signature` gains one ghost formal lemma, `Lemma_Mul_Assoc`, with `Same ((A * B) * C, A * (B * C))`. Each field proves it.
  - On GF(2^128), against `Mul_Ref`: linearity in each operand, the product commutes with `Xtime` in its second operand (with x^128 = x^7 + x^2 + x + 1 checked on the basis), then induction over the bits of the third operand.
  - On P-256, from the integer model `To_Int`, by the laws of the remainder and the uniqueness of the limbs in base 2^64.
- **The normal form of a P-256 product.** `Same` is the logical equality, and it does not follow from `=` on P-256 elements. The limb array is a subtype of `Word_Array`, indexed by `Natural`, so for the provers two elements with equal limbs may still differ outside 0 .. 3. On GF(2^128) the index is a type of its own and the question does not arise.
  - `P256_Field` gains `Norm`, the element rebuilt from its four limbs, and `Eq`, a logical equality with the same status as `Same`: its body is `=`, outside SPARK.
  - `Mul` gains the postcondition `Eq (Mul'Result, Norm (Mul'Result))`, and its body returns through `Norm`, a copy of four words. For the provers each aggregate in the code is a symbol of its own, so the result must be built by the same `Norm` that the postcondition names.
  - Two products with equal limbs are then `Same`, which is all the tables need: every factor they reassociate is a product.
- **The FFT stays in reserve.** If the measured gain falls short of the goal of M2, the verifier can still encode as upstream, with the trade-off above, under a new record.

## Alternatives considered

- **The FFT as upstream.** About 0.3 s faster on the hash verification and 0.5 s on the signature, by the estimate of this record. But on the path `Verify` takes, the Lagrange encoding would be tested, not proved. Kept in reserve.
- **Barycentric tables (ADR 0063).** Same order of cost, but one inversion per entry or a batch inversion, and a longer algebraic argument.
- **Only cache the evaluation points.** No new proof, but the K² · NREQ multiplications stay.
- **Prove the FFT.** It needs the field laws, a theory of polynomials and the correctness of two FFTs. Out of scale.

## Consequences

- `Field_Signature` gains one formal lemma. `GF2_128` and `P256_Field` gain the law and the lemmas it rests on, and their `Field_*` wrappers pass it as the actual, through a child unit `Laws` that turns `=` into `Same`.
- `P256_Field.Mul` gains one postcondition, the normal form of its result. No postcondition is weakened.
- `Lagrange.Build` gets a new body: `Fill_Column` replaces `Fill_Row`. `Diff_Product` stays, for the denominators. The Lagrange vectors and the recorded upstream runs check the tables as before, and the proofs stay identical byte for byte.
- The estimate on the proving machine: the hash verification from 18 s to about 6 s, the signature verification from 46 s to about 2 s. The measurement checks it.
- The law can be reused by later steps of M2.

## Verification impact

- Proved: the tables as today, against the Lagrange formula of Section 4.3; the associativity of the product, on both fields; the normal form of the P-256 product; absence of run-time errors.
- Tested: unchanged. The interpolation property stays tested (ADR 0040).
- Trusted: one more function of the kind of `Same`, `P256_Field.Eq`, whose body is the predefined `=` outside SPARK and which the provers take as the logical equality.

## References

- [ADR 0023](0023-gold-perimeter-for-protocol-code.md), [ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md), [ADR 0037](0037-checked-inv-and-public-data-scope.md), [ADR 0057](0057-additive-fft.md), [ADR 0063](0063-milestone-m1-algorithmic-parity.md), [ADR 0065](0065-carry-less-multiplication-in-gf2-128.md).
- google/longfellow-zk at d5e6be7: `rust/runtime/ligero/src/verifier.rs`, `rust/runtime/algebra/src/interpolation.rs`.
