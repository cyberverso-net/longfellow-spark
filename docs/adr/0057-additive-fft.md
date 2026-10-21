# 0057 The additive FFT for the Reed-Solomon code

## Status

Accepted (2026-10-20, at the close of block 4 of Phase D). Proposed on 2026-10-19 in block 1; block 3 realised it for GF(2^128), block 4 for P-256; corrected while Proposed: F_p has no large roots of unity, the reference's transform on P-256 is a real FFT over F_p^2.

## Date

2026-10-19

## Context

[ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md) chose Lagrange interpolation at the queried columns for the verifier, which evaluates a row's polynomial at NREQ points and needs no FFT. The prover of Phase C reused the same tables for every parity column ([ADR 0049](0049-phase-c-scope-the-prover.md)): `Lagrange.Build` over NCOL - k columns costs k^2 (NCOL - k) multiplications per table, and the encoding of a row k (NCOL - k). At 256 columns this stayed under a second; at the mDoc scale (block 1 of this phase, [ADR 0055](0055-phase-d-scope-mdoc-scale.md)) the two tables of the signature circuit alone cost 3.4 thousand million P-256 multiplications and the hash circuit's about as many on GF(2^128), before the 266 rows are encoded.

The draft defines the code on GF(2^k) through the evaluation points inj(i) of Section 2.2.2 and the additive FFT of Lin, Chung and Han (2014) over the novel polynomial basis; the production prover (`rust/runtime/algebra/src/lch14_reed_solomon.rs`, 118 lines, with `lch14.rs`) evaluates on the subspace of the first 2^l points, l the smallest with 2^l at least the row length, by coset when NCOL exceeds 2^l, and truncates to NCOL (4151 is not a power of two). On F_p the draft leaves the algorithm free (Section 2.2.1), but the extension evaluates at the consecutive points 0 .. m - 1, which are not roots of unity, so a number-theoretic transform alone does not compute it. The production prover (`rust/runtime/algebra/src/reed_solomon.rs`, `ReedSolomon::interpolate`) computes the Lagrange extension on consecutive points as a middle product of a convolution: p(k) = (-1)^d (k - d) (k choose d) times the sum over j of p(j) (-1)^j (d choose j) / (k - j), the kernel 1 / (k - j) from a batch of inverses and the binomial factors precomputed as `leading_constant`; the convolution itself is a cyclic FFT of size the next power of two above m (`FFTExtMiddleProduct` of `middle_product.rs`, `can_encode`), which the production code runs on Fp2 (`FftInterpolatorFactory`, `fp2.rs`). F_p itself has no root of unity of order 4 or more: p - 1 = 2 q with q odd, and it is p + 1 that equals 2^96 (2^160 - 2^128 + 2^96 + 1). The roots live in F_p^2 = F_p[i] / (i^2 + 1), a genuine extension since p is 3 modulo 4, whose multiplicative group has order (p - 1)(p + 1), divisible by 2^97. The reference takes a root of order 2^31 there (`p256/mod.rs`, `P256_ROOT_OF_UNITY_RE` and `_IM`). Its transform is a real FFT (`rfft.rs`): the input lies in F_p, so the output is conjugate-symmetric and is stored in the half-complex form of FFTW, n elements of F_p, computed by a radix-4 Cooley-Tukey on the real input (`r2hc` forward, `hc2r` backward). The transform of the kernel 1 / t is computed once per pair (n, m) and scaled by 1 / P; each row costs one forward transform, a product on the conjugate pairs and one backward transform.

The additive FFT has a bound of its own: every evaluation point, cosets included, must lie in the subfield of 2^16 elements (`can_encode` of `lch14_reed_solomon.rs`: `block_enc <= 1 << subfield.dimension ()`), so NCOL is at most 2^16, the bound `Ligero_Geometry.Max_Encoded_Len` already has.

The codeword does not depend on the algorithm: the two Phase C proofs, whose rows are encoded by Lagrange, are byte for byte the upstream prover's, which encodes by the FFT.

## Decision

- **GF(2^128): the additive FFT**, in the form of the production algorithm with the points of the specification: the novel basis X_j and the subspace vanishing polynomials, the change of basis from the values on the first n points to the novel coefficients, the evaluation on 2^l points and on the cosets up to NCOL, the truncation; `Extend (F, N, M)` for any n and m within 2^l, as `lch14_reed_solomon.rs` does. Block 3, with chapter 8 and a small example worked by hand.
- **The Lagrange encoder stays** in the repository as the reference encoding: the harness compares the two codewords on random rows and on every row of the four mDoc circuits and of the two Phase C circuits; the byte identity of the `sha256` proof must stand, since the codeword is the same.
- **The verifier does not change**: it evaluates at NREQ queried columns with the Lagrange tables of chapter 5, which is linear in k per column.
- **Perimeter.** Silver everywhere; structural Gold on the shapes and the changes of basis where the provers close them; the mathematical identity between the FFT and the Lagrange codeword is tested, not proved ([ADR 0052](0052-gold-perimeter-for-the-prover.md)'s rule). Constant time by construction: butterflies on public indices, as [ADR 0051](0051-constant-time-in-the-prover.md).
- **P-256 is measured first** (block 4), after the linear constraint and the heap: if the Lagrange encoding of the signature circuit (3739 inputs, 19 rows, 4096 columns) with its tables built once stays within the target of ADR 0055, it stays and this record says so; otherwise the Lagrange extension on consecutive points by middle product, as the production prover computes it, with the convolution computed by the real FFT over F_p^2 of `rfft.rs`, transcribed in its form (half-complex storage, radix 4) with the reference's root of unity, same perimeter as the additive FFT. The numbers decide, here.
- **The bound NCOL <= 2^16** of the additive FFT (every point in the subfield) is stated where the geometry is checked (`Ligero_Geometry`, `Fits` of the prover) and in chapter 8.
- **Memory** is measured with the FFT in place (block 4): the table of bytes per circuit, the peak, and the heap of [ADR 0047](0047-heap-allocation-by-ownership.md) extended where a stack object remains.

## Block 4, as realised

- The Lagrange encoder of the signature circuit was measured against the target of ADR 0055: 1129 seconds of CPU for the version 7 signature proof, against about 27 for the two proofs together. It was replaced, as the decision above foresees.
- `Rfft_P256` transcribes `rfft.rs` with three changes of form that keep every value: recursion on quarters, one twiddle table per level built by taking every fourth entry of the level above, and the bit-reversal permutation by a recurrence. The P-256 prover encodes with it (`Use_Fft => True`), and `No_Fft_P256` is gone.
- On the proving machine, the version 7 signature circuit is proved in 41 seconds and 74 MB, against 1129 seconds and 216 MB with Lagrange, and the proof is the same bytes. The partition `ligero-prover` proves 3253 checks.

## Alternatives considered

- **Caching the Lagrange tables per configuration.** Removes the k^2 cost once per run but not the k (NCOL - k) per row, and the draft's definition of the code is the FFT; not taken.
- **The multiplicative FFT on GF(2^128).** Not possible: GF(2^128)* has no elements of order 2^k.
- **A number-theoretic transform alone on P-256.** Does not compute the extension of Section 2.2.1, whose points are consecutive integers, not roots of unity; the transform is the tool for the convolution inside the middle product. Nor can it run in F_p, which has no root of order 4.
- **A complex FFT over F_p^2, radix 2.** The same convolution with about twice the work of the real FFT (it carries imaginary parts that are zero), and much less code to prove. Measured estimates for the signature circuit: about 2 seconds against about 1 for the real FFT, both well within the target. Not taken: the author chose the reference's form.
- **The middle product computed directly, or Lagrange tables in the closed form for consecutive points.** n (m - n) multiplications per row, about 25 seconds for the signature circuit, close to the whole target on their own. Not taken.

## Consequences

- A new unit (or two: the FFT and its tables), a new proof partition `fft` if the counts require it, chapter 8.
- `Ligero_Prover.Encode_Row` delegates to the FFT on GF(2^128); the tables of parity columns disappear from the commitment for that field.

## Verification impact

- Provable: absence of run-time errors for any n, m within the bounds; the shapes; what structural Gold the provers close.
- Tested: codeword identity with Lagrange on random and real rows; the byte identity of Phase C.
- Trusted: the identity beyond the tested rows; the paper's basis.
- Constant time: by construction, declared.

## References

- draft-google-cfrg-libzk-03, Sections 2.2.1 and 2.2.2; Lin, Chung, Han, "Novel polynomial basis and its application to Reed-Solomon erasure codes", FOCS 2014.
- google/longfellow-zk at d5e6be7: `rust/runtime/algebra/src/lch14.rs`, `lch14_reed_solomon.rs` (`can_encode`), `reed_solomon.rs` (`ReedSolomon::interpolate`, `leading_constant`, `FftInterpolatorFactory`), `middle_product.rs` (`FFTExtMiddleProduct`, `can_encode`), `fp2.rs`, `fft.rs`, `rfft.rs`, `interpolator.rs`.
- [ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md), [ADR 0049](0049-phase-c-scope-the-prover.md), [ADR 0051](0051-constant-time-in-the-prover.md), [ADR 0055](0055-phase-d-scope-mdoc-scale.md).
