# 0057 The additive FFT for the Reed-Solomon code

## Status

Proposed (2026-10-19, block 1 of Phase D; realised in blocks 3 and 4)

## Date

2026-10-19

## Context

[ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md) chose Lagrange interpolation at the queried columns for the verifier, which evaluates a row's polynomial at NREQ points and needs no FFT. The prover of Phase C reused the same tables for every parity column ([ADR 0049](0049-phase-c-scope-the-prover.md)): `Lagrange.Build` over NCOL - k columns costs k^2 (NCOL - k) multiplications per table, and the encoding of a row k (NCOL - k). At 256 columns this stayed under a second; at the mDoc scale (block 1 of this phase, [ADR 0055](0055-phase-d-scope-mdoc-scale.md)) the two tables of the signature circuit alone cost 3.4 thousand million P-256 multiplications and the hash circuit's about as many on GF(2^128), before the 266 rows are encoded.

The draft defines the code on GF(2^k) through the evaluation points inj(i) of Section 2.2.2 and the additive FFT of Lin, Chung and Han (2014) over the novel polynomial basis; the production prover (`rust/runtime/algebra/src/lch14_reed_solomon.rs`, 118 lines, with `lch14.rs`) evaluates on the subspace of the first 2^l points, l the smallest with 2^l at least the row length, by coset when NCOL exceeds 2^l, and truncates to NCOL (4151 is not a power of two). On F_p the draft leaves the algorithm free (Section 2.2.1); p - 1 = 2^96 q for the P-256 base field, so a multiplicative NTT of order 2^k up to 96 exists in F_p itself; the production prover interpolates on Fp2 (`FftInterpolatorFactory` over `fp2.rs`) for reasons of its own, to be read and not copied.

The codeword does not depend on the algorithm: the two Phase C proofs, whose rows are encoded by Lagrange, are byte for byte the upstream prover's, which encodes by the FFT.

## Decision

- **GF(2^128): the additive FFT**, in the form of the production algorithm with the points of the specification: the novel basis X_j and the subspace vanishing polynomials, the change of basis from the values on the first n points to the novel coefficients, the evaluation on 2^l points and on the cosets up to NCOL, the truncation; `Extend (F, N, M)` for any n and m within 2^l, as `lch14_reed_solomon.rs` does. Block 3, with chapter 8 and a small example worked by hand.
- **The Lagrange encoder stays** in the repository as the reference encoding: the harness compares the two codewords on random rows and on every row of the four mDoc circuits and of the two Phase C circuits; the byte identity of the `sha256` proof must stand, since the codeword is the same.
- **The verifier does not change**: it evaluates at NREQ queried columns with the Lagrange tables of chapter 5, which is linear in k per column.
- **Perimeter.** Silver everywhere; structural Gold on the shapes and the changes of basis where the provers close them; the mathematical identity between the FFT and the Lagrange codeword is tested, not proved ([ADR 0052](0052-gold-perimeter-for-the-prover.md)'s rule). Constant time by construction: butterflies on public indices, as [ADR 0051](0051-constant-time-in-the-prover.md).
- **P-256 is measured first** (block 4), after the linear constraint and the heap: if the Lagrange encoding of the signature circuit (3739 inputs, 19 rows, 4096 columns) with its tables built once stays within the target of ADR 0055, it stays and this record says so; otherwise the multiplicative NTT in F_p with a root of unity of order 2^k, same perimeter as the additive FFT. The numbers decide, here.
- **Memory** is measured with the FFT in place (block 4): the table of bytes per circuit, the peak, and the heap of [ADR 0047](0047-heap-allocation-by-ownership.md) extended where a stack object remains.

## Alternatives considered

- **Caching the Lagrange tables per configuration.** Removes the k^2 cost once per run but not the k (NCOL - k) per row, and the draft's definition of the code is the FFT; not taken.
- **The multiplicative FFT on GF(2^128).** Not possible: GF(2^128)* has no elements of order 2^k.
- **Fp2 on P-256 as the reference does.** Not needed a priori: F_p has the roots; the decision waits for the measurement.

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
- google/longfellow-zk at d5e6be7: `rust/runtime/algebra/src/lch14.rs`, `lch14_reed_solomon.rs`, `fp2.rs`, `fft.rs`, `rfft.rs`, `interpolator.rs`.
- [ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md), [ADR 0049](0049-phase-c-scope-the-prover.md), [ADR 0051](0051-constant-time-in-the-prover.md), [ADR 0055](0055-phase-d-scope-mdoc-scale.md).
