# 0066 The verifier's Lagrange tables by prefix and suffix products, proved

## Status

Proposed (2026-10-22, milestone M2 of Phase D). Amends the last item of the decision of [ADR 0063](0063-milestone-m1-algorithmic-parity.md): the verifier's Lagrange tables are built from prefix and suffix products, not with barycentric weights.

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
- the suffix products, from the right: S (i) = (x - p_(i+1)) (... ((x - p_(K-1)) One));
- the product of row i is P (i) S (i).

That P (i) S (i) equals the product of today, a left fold from One that skips i, needs one law of the field: the associativity of the product. It also needs A One = A.

## Decision

- **The tables are built from prefix and suffix products.**
  - The evaluation points are computed once, into an array.
  - For each queried column, one backward pass makes the suffix products, and one forward pass makes the prefix products and the entries P (i) S (i) Inv_D (i).
  - The denominators are computed as today, once per row.
  - A table costs about K² + 3 K · NREQ multiplications instead of K² · NREQ.
- **The contracts do not change.** `Lagrange.Build` keeps its Gold postcondition against `Diff_Product_Ref`, and `Ligero_Verifier` keeps all of its contracts. Only the body of `Build` changes.
- **Two laws of the product, proved per field.**
  - `Field_Signature` gains two ghost formal lemmas, `Lemma_Mul_Assoc` with `Same ((A * B) * C, A * (B * C))` and `Lemma_Mul_One` with `Same (A * One, A)`.
  - Each field proves them, nothing is assumed.
  - On GF(2^128), against `Mul_Ref`: linearity in each operand, the product commutes with `Xtime` in its second operand (with x^128 = x^7 + x^2 + x + 1 checked on the basis), then induction over the bits of the third operand.
  - On P-256, from the integer model `To_Int`, by the laws of the remainder.
- **The FFT stays in reserve.** If the measured gain falls short of the goal of M2, the verifier can still encode as upstream, with the trade-off above, under a new record.

## Alternatives considered

- **The FFT as upstream.** About 0.3 s faster on the hash verification and 0.5 s on the signature, by the estimate of this record. But on the path `Verify` takes, the Lagrange encoding would be tested, not proved. Kept in reserve.
- **Barycentric tables (ADR 0063).** Same order of cost, but one inversion per entry or a batch inversion, and a longer algebraic argument.
- **Only cache the evaluation points.** No new proof, but the K² · NREQ multiplications stay.
- **Prove the FFT.** It needs the field laws, a theory of polynomials and the correctness of two FFTs. Out of scale.

## Consequences

- `Field_Signature` gains two formal lemmas. `GF2_128` and `P256_Field` gain the two laws and the lemmas they rest on, and their `Field_*` wrappers pass them as actuals.
- `Lagrange.Build` gets a new body and a points array on the heap. `Diff_Product` stays, for the denominators and as the reference that the harness compares the tables against.
- The estimate on the proving machine: the hash verification from 18 s to about 6 s, the signature verification from 46 s to about 2 s. The measurement checks it.
- The two laws can be reused by later steps of M2.

## Verification impact

- Proved: the tables as today, against the Lagrange formula of Section 4.3; the associativity of the product and its unit, on both fields; absence of run-time errors.
- Tested: unchanged. The interpolation property stays tested (ADR 0040).
- Trusted: unchanged.

## References

- [ADR 0023](0023-gold-perimeter-for-protocol-code.md), [ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md), [ADR 0037](0037-checked-inv-and-public-data-scope.md), [ADR 0057](0057-additive-fft.md), [ADR 0063](0063-milestone-m1-algorithmic-parity.md), [ADR 0065](0065-carry-less-multiplication-in-gf2-128.md).
- google/longfellow-zk at d5e6be7: `rust/runtime/ligero/src/verifier.rs`, `rust/runtime/algebra/src/interpolation.rs`.
