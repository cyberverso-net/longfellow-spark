# 0069 P-256 in Montgomery form, with the multiplication of upstream

## Status

Proposed (2026-10-22, milestone M2 of Phase D). Amended 2026-10-23 by [ADR 0070](0070-sumcheck-and-ligero-kernels-as-upstream.md): the four limbs of an element are scalar components, read as an array through `Limbs (E)` where this record writes `E.Limbs`; the value model is unchanged.

## Date

2026-10-22

## Context

In the release build of ADR 0068, P-256 field multiplication is about 80% of the signature proof and of its verification. `Add_Term`, one stage of the reduction, is 64 to 68% on its own.

`P256_Field.Mul` computes the full 512-bit product, then reduces it by the Solinas method: eleven terms of the NIST fast reduction, each added over eight words. On the author's laptop it takes 230 ns at `-O3`. Upstream's generic code takes 13 ns (`runtime/algebra/benches/p256_benchmark.rs`, with and without `force-generic-arch`).

Upstream keeps its elements in Montgomery form and multiplies by the interleaved Montgomery method (`fp_generic.rs`, `p256/p256_64.rs`):

- four rounds, each one row a_i · b accumulated into a nine-word buffer, then one reduction step;
- for P-256, -p^-1 mod 2^64 = 1, so the step's multiplier is the low word r itself. Adding r · p is a few shifted additions and subtractions of r, because p = 2^256 - 2^224 + 2^192 + 2^96 - 1;
- one conditional subtraction of p at the end.

An unproved port to Ada of that method takes 26 ns on the same laptop at `-O3`. The stop criterion of ADR 0067 asks for upstream's algorithm wherever the proof allows it.

## Decision

- **The element holds a · R mod p, with R = 2^256.** The representation stays canonical: the stored integer is below p. Equality of elements is still the equality of their limbs, so `Same`, `Eq` and `Norm` are unchanged.
- **The ghost model gains `Value (E) = To_Int (E.Limbs) · R^-1 mod p`.** It is the field element that E denotes. Every contract that speaks of the element's integer speaks of `Value`.
- **`Mul` is upstream's `montgomery_mul` for P-256, Gold.**
  - Post: `To_Int (Mul (A, B).Limbs) = To_Int (A.Limbs) · To_Int (B.Limbs) · R^-1 mod p`, so `Value (Mul (A, B)) = Value (A) · Value (B) mod p`.
  - Each reduction step is proved by the identity a + r · p, with the low word cancelling, then exact division by 2^64. The bound of the buffer below 2p at the end comes from A, B < p < R.
  - The Solinas reduction leaves the code. Its tests stay as tests of the new `Mul`.
- **`Add`, `Sub` and `Neg`** are unchanged in code. Their Posts already hold on the stored integers, and so they hold for `Value`.
- **The boundaries convert.**
  - `From_Bytes` checks the canonical encoding as today, then stores Mul (x, R^2 mod p). Post: `Value (E) = To_Int (bytes)`.
  - `To_Bytes` stores Mul (E, 1), the canonical integer. Post: the bytes encode `Value (E)`.
  - `Of_Natural (X)` gives `Value = X`. `Zero` is 0, `One` is R mod p.
  - `Inv` keeps its algorithm, Fermat's exponent by repeated `Mul`, which is correct in either form. It stays Silver, with its known-answer tests.
- **Constants and parsers outside the package** stop writing limbs directly. A new function `From_Canonical (L : Limb_Array)`, with Pre `Is_Canonical (L)` and Post `Value (Result) = To_Int (L)`, converts them:
  - the constants of `Field_P256` (`P2`, `Half`, `Minus_One`) and the roots of unity of `Rfft_P256`, computed at elaboration;
  - the hex parsers of `longfellow_verify`, `interop_kat` and six harnesses.
- **The contract of `Field_Signature` does not change.** Its Gold users (`Lagrange`, the sumcheck, Ligero) see the same operations with the same laws, and `Lemma_Mul_Assoc` is proved again in the new model.

## Alternatives considered

- **Keep Solinas and rewrite the reduction** as one pass over columns with a single carry. That is cheaper to prove, but it is not upstream's algorithm, and its speed is unmeasured. The author chose Montgomery (2026-10-22).
- **Montgomery with the generic step** q = t_0 · m' and the full product q · p. It is simpler to prove, through the existing `Mul_Row`, but it costs sixteen more products per multiplication, and upstream does not use it for P-256.
- **Montgomery form only inside a fast path**, converting at every `Mul`. Rejected: two extra multiplications per product remove most of the gain.

## Consequences

- ADR 0013 is amended: its direct representation and Solinas reduction leave the code.
- `P256_Field`'s body is largely rewritten: the product, the reduction and their lemmas. The byte encoding, the canonical check, `Add`, `Sub` and the word primitives stay.
- The harnesses read elements through `From_Canonical` or `From_Bytes`. `p256_kat` checks `From_Canonical` and `To_Bytes` as inverse on its vectors and on random values.
- The proofs of the CLI must stay identical byte for byte. The transcript absorbs `To_Bytes`, so the canonical values are what it hashes.
- The trust model's entry for P-256 states the new model: Gold against the integer model through `Value`.

## Verification impact

- `P256_Field` is proved again, Gold for `Mul`, `Add`, `Sub`, `From_Bytes`, `To_Bytes`, `Of_Natural` and `From_Canonical`, Silver for `Inv`. No `pragma Assume`, no weaker contract.
- The units that instantiate the field are proved again unchanged, since their contracts are written against `Field_Signature`.

## References

- [ADR 0023](0023-gold-perimeter-for-protocol-code.md), [ADR 0066](0066-lagrange-tables-by-prefix-and-suffix.md), [ADR 0067](0067-performance-milestones-by-trust.md), [ADR 0068](0068-release-build-without-run-time-checks.md).
- google/longfellow-zk at d5e6be7: `rust/runtime/algebra/src/fp_generic.rs` (`montgomery_mul`, `reduction_step`, `maybe_minus_m`), `rust/runtime/algebra/src/p256/p256_64.rs` (`p256_reduction_step`).
- P. L. Montgomery, Modular multiplication without trial division, Mathematics of Computation 44 (1985).
