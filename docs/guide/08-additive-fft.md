# Chapter 8: the additive FFT

Phase D makes the prover fast enough for the mDoc circuits of production. On the hash circuit, more than half of the prover's time went into building Lagrange tables to encode the rows of the tableau. This chapter replaces that encoder, on GF(2^128), with the additive FFT that the specification names and that the production prover uses. The decision is [ADR 0057](../adr/0057-additive-fft.md). The reference is google/longfellow-zk at d5e6be7, `rust/runtime/algebra/src/lch14.rs` and `lch14_reed_solomon.rs`.

The verifier does not change. It evaluates a row only at the NREQ opened columns, and the Lagrange tables of chapter 5 stay the right tool for that.

## 1. The mathematics

### 1.1 What the encoder computes

A row of the tableau is n values. The Reed-Solomon code of Section 2.2 reads them as the values of a polynomial p of degree below n at the first n evaluation points, and the encoded row is the values of p at the first m points, m = NCOL. The first n entries are the row itself. Only the other m - n, the parity part, need computing.

On GF(2^128) the points are fixed by Section 2.2.2. Point i is inj(i), the sum of the subfield basis elements beta_j over the set bits j of i. The sixteen beta_j span the subfield GF(2^16), so the points 0 to 2^16 - 1 are exactly the elements of that subfield, in a fixed order. `GF2_128.Inject` computes inj, and chapter 1 anchored the basis on the upstream constants.

Chapter 5 computed the parity part with Lagrange interpolation: one table entry per pair of row position and parity column, so n (m - n) multiplications per row and the same again to build each table. For the mDoc hash circuit, with rows of several hundred values and 4151 columns, the tables alone took most of the proof.

### 1.2 Why an additive FFT

The usual fast Fourier transform evaluates a polynomial at the powers of a root of unity. GF(2^128) has no element of order 2^k for k at least 1, since its multiplicative group has odd order 2^128 - 1, so that FFT does not exist here. What the field does have is additive structure. The points inj(0 .. 2^l - 1) form a subspace of dimension l over GF(2), and the next 2^l points form a coset of that subspace. An FFT that splits a subspace into a smaller subspace and its coset, instead of splitting a group of roots of unity into its even and odd powers, is the additive FFT.

### 1.3 Subspace polynomials and the novel basis

Let V_i be the span of beta_0 .. beta_i-1, the first 2^i points. Its vanishing polynomial W_i(X) is the product of (X - v) over v in V_i, of degree 2^i. Two facts make the transform work.

- **W_i is linear over GF(2).** W_i(x + y) = W_i(x) + W_i(y). So the values of W_i on the points are sums of its values on the basis elements, which is why sixteen values per level are enough.
- **There is a recursion.** W_0(X) = X, and W_i+1(X) = W_i(X) (W_i(X) + W_i(beta_i)). Since V_i+1 is V_i together with V_i + beta_i, the second factor vanishes on the coset.

The normalised polynomials are hat-W_i = W_i / W_i(beta_i), which take the value 1 at beta_i. `Additive_Fft` keeps the table hat-W_i(beta_j) for i and j below 16, computed once by that recursion, exactly as `Lch14::new` does. Below the diagonal the table is zero, since beta_j lies in V_i when j < i. The generator checks both properties.

Lin, Chung and Han (2014) write polynomials in the novel basis: the products of hat-W_i over the set bits i of an index. In that basis a polynomial of degree below 2^l splits into two halves of degree below 2^(l-1), and evaluating it on a subspace and its coset is one level of butterflies away from evaluating the two halves on the smaller subspace. A butterfly takes a pair (a, b) to (a + t b, a + t b + b), where t, the twiddle, is hat-W_i at the coset's offset. Running l levels of butterflies takes the 2^l coefficients to the 2^l values, in O(l 2^l) operations. The inverse runs the levels in the opposite order with the inverse butterflies.

### 1.4 From n values to m values

The encoder starts from values, not coefficients, and n is rarely a power of two. Let 2^l be the smallest power of two at least n. The reference proceeds in three steps.

1. **The bidirectional transform.** It takes the n known values and the 2^l - n unknown coefficients, known to be zero because the degree is below n, and returns the n coefficients and the 2^l - n missing values, in one pass. This is the truncated transform of van der Hoeven, ported to the additive FFT. It recurses on halves: when the known values fit in the left half, it finishes the right half by forward butterflies; otherwise it inverts the left half first.
2. **Copy.** The values n .. 2^l - 1 now in the buffer are the first part of the parity.
3. **Cosets.** With the coefficients alone in the buffer, the others set to zero, one forward transform per coset gives the values at points 2^l to 2^(l+1) - 1, then the next coset, until m. The last coset is cut at m.

Every point used is below m, and m is at most 2^16, so every point lies in the subfield. This is the bound `can_encode` checks upstream, and the one `Ligero_Geometry.Max_Encoded_Len` already imposed on NCOL.

### 1.5 P-256

The prime field has no subspace structure, and its points 0, 1, 2 and so on are integers, not roots of unity. Block 4 decides how to encode there, on measurements. The P-256 prover keeps the Lagrange encoder of chapter 5 until then.

## 2. The algorithm

### 2.1 A small example by hand

Take n = 3 values y0, y1, y2 at the points inj(0) = 0, inj(1) = beta_0 = 1 and inj(2) = beta_1, and m = 6. Then 2^l = 4, with l = 2, and the polynomial has degree at most 2.

- **Level 1, the top.** The two halves are the points {0, 1} and {beta_1, beta_1 + 1}. The twiddle of the top level at coset 0 is Twiddle(1, 0) = 0, the sum over no bits.
- **The bidirectional pass.** k = 3 is not below s = 2, so the left half {y0, y1} is inverted first, at level 0 with twiddle Twiddle(0, 0) = 0. The inverse butterfly with t = 0 gives (y0, y0 + y1): the coefficients of the line through the two points in the basis {1, hat-W_0}. Then the right half is completed: the one known value y2, and one unknown, the value at beta_1 + 1. The recursion finishes it with Twiddle(0, 2) = hat-W_0(beta_1) = beta_1 and the diagonal butterfly.
- **The result.** The buffer holds the three coefficients and the value at inj(3) = beta_1 + 1.
- **The coset.** For points 4 and 5, the coefficients go through one forward transform at coset 4. Its twiddles are Twiddle(1, 4) = hat-W_1(beta_2) at the top level, and Twiddle(0, 4) and Twiddle(0, 6) below.

The same steps, with numbers, are what `gen_fft_vectors.py` checks for 19 shapes, among them (3, 8) and (5, 40).

### 2.2 Two changes of form

`Additive_Fft` computes the same values as the reference, in two different forms.

- **The transforms recurse on halves.** The reference loops over the levels and, within a level, over the blocks. Here `Fft` does the top level of butterflies and then calls itself on the two halves, the right half at coset + 2^(l-1). `Ifft` does the halves first and the top level last. The butterflies of different blocks of a level do not interact, so the result is the same, and the recursion keeps every index a sum of offsets with no product to prove.
- **The twiddles are computed directly.** The reference builds the twiddles of a level incrementally (`twiddles`). Here each one is `Twiddle (I, Coset + offset)`, the sum of the table entries over the bits of the index. That costs at most sixteen additions per twiddle, which is little next to the multiplications.

## 3. The Ada/SPARK implementation

### 3.1 `Additive_Fft`

The package is not generic: it works on GF(2^128) only, with the element arrays of the GF(2^128) algebra instance.

- `W_Hat (I, J)` reads the table, computed once when the body is elaborated.
- `Twiddle (I, U)` sums `W_Hat (I, K)` over the set bits K below 16 of U. Reading only sixteen bits means that U itself needs no bound, so the coset offsets only have to avoid overflow, and the preconditions stay linear.
- `Fft`, `Ifft` and `Bidir` work on `B (Off .. Off + 2^L - 1)`, with `Subprogram_Variant => (Decreases => L)` for the recursion.
- `Extend (Row, Enc)` is the encoder. Its two work arrays, of up to 2^16 elements, are on the heap and freed before it returns.

A table built at elaboration needs one care. A constant in the specification initialised by a function of the same package would be computed before the body exists, and the program stops with `Program_Error` at start-up. The table is therefore a constant of the body, behind the function `W_Hat`.

### 3.2 Constant time

Every loop bound, index and twiddle depends on n and m, which are the public geometry of the proof. The values only go through additions and multiplications. The FFT is constant time by construction, as [ADR 0051](../adr/0051-constant-time-in-the-prover.md) asks of the prover. The branch in `Twiddle` is on the bits of a public index.

### 3.3 The encoder of `Ligero_Prover`

`Ligero_Prover` takes two new generic formals: a Boolean `Use_Fft` and a procedure `Extend`.

- With `Use_Fft => True`, `Encode_Row` calls `Extend` and then writes the systematic part itself. The commitment holds no Lagrange table, only an unused element per table. `Allocate` builds none, which is where the time went.
- With `Use_Fft => False`, `Encode_Row` is the Lagrange encoder of Phase C and `Extend` is never called. The P-256 instances pass `No_Fft_P256.Extend`, which only copies the row.

The formal procedure carries no contract. GNAT accepts a contract on a formal subprogram, but it does not resolve one that names the element types through the chain of formal packages of `Ligero_Prover`. That is not a loss: GNATprove proves a generic instance by instance, so in the GF(2^128) instance the call is proved against the contract of `Additive_Fft.Extend` itself. For the same reason `Encode_Row` rewrites the systematic part after `Extend`, so that its own postcondition needs nothing from the formal.

### 3.4 Memory

With the FFT, the commitment loses its two Lagrange tables, n (m - n) elements each, and the work arrays of `Extend` are at most 2^16 elements, allocated per row. The measurements of section 5 give the peak.

## 4. What the proofs guarantee

- Silver on `Additive_Fft` for every row of 1 to 2^16 values and every output length up to 2^16, with the ownership checks on its two work arrays.
- `Extend` leaves the first n values unchanged: the systematic part of the code.
- `Encode_Row`, conditional on the encoder ([ADR 0057](../adr/0057-additive-fft.md)). The systematic part is the row, for both fields. With the Lagrange encoder, for P-256, the parity part is the Lagrange evaluation, as in Phase C. With the FFT, for GF(2^128), the parity part is not proved equal to anything: that is the test of section 5.

The proof of the block, on the proving machine:

| Scope | Checks | Unproved |
|-------|--------|----------|
| partition `ligero-prover` (the prover, the composed prover, `Additive_Fft`, `No_Fft_P256`) | 2547 | 0 |
| the whole project (`make check`) | 17269 | 0 |

Three kinds of check needed attention, and none changed a contract. Termination: `Commit_Row` is called from procedures that declare `Always_Terminates`, so the two `while` loops of `Extend` got loop variants and the transforms an explicit `Always_Terminates`. The bound on L: the provers do not evaluate 2^16 for a variable exponent, so the loop that finds 2^L stops at L = 16 by its own condition, and a branch that is never taken covers the case 2^L < N after it. The formal contract: section 3.3.

## 5. What is only tested

- **The FFT gives the Lagrange codeword.** `gen_fft_vectors.py` transcribes `lch14.rs` and `lch14_reed_solomon.rs` in Python and checks every extension against barycentric Lagrange interpolation on the points inj(i), with no FFT. It writes the table, sample twiddles and 19 extensions to `fft.txt`. `fft_kat` checks `Additive_Fft` on that file, then against `Lagrange.Evaluate` of chapter 5 on random rows of 16 shapes, among them those of the two Phase C geometries.
- **The commitments of the prover are unchanged.** `prover_kat` compares the roots and the openings of the commitments of the small circuits with the Python reference of Phase C, which encodes by Lagrange. They still agree.
- **The two Phase C proofs are still reproduced byte for byte.** The `sha256` proof is now encoded by the FFT.
- **The mDoc proofs are the same bytes.** The version 7 hash and signature circuits were proved with seed 1 by `main`, which encodes by Lagrange, and by this block. The two hash proofs are identical, which tests the FFT on every row of the tableau of a production circuit. The signature proofs, still encoded by Lagrange on both sides, are identical too.

Times on the proving machine, version 7 circuits, default 8 MB stack:

| Run | Lagrange encoder | Additive FFT |
|-----|------------------|--------------|
| hash, prove | 19 min 59 s, 672 MB | 6 min 30 s, 599 MB |
| hash, verify | 2 min 02 s, 371 MB | 2 min 02 s, 371 MB |
| signature, prove | 18 min 51 s, 216 MB | 18 min 49 s, 216 MB |
| signature, verify | 53 s, 41 MB | 54 s, 41 MB |

The hash prover is three times faster. The verifier, which keeps Lagrange on the NREQ opened columns, does not change, nor does the signature circuit, which keeps the Lagrange encoder until block 4.

The profile of the hash prover moves accordingly. The Ligero commitment, FFT included, falls below 0.5% of the time, from 60% before. What remains is the sumcheck: the sumcheck prover takes 75% (`Round_Evals` 51%), and the verifier core the prover runs takes 24%, almost all of it `Eval_Bound_Quad`, the cost left to a later block.

## 6. What stays trusted, and the limits

- That the two encoders agree beyond the tested rows. This is the mathematics of the paper, not a proof here.
- The novel basis and the correctness of the algorithm of Lin, Chung and Han, as the reference implements it.
- The bound NCOL at most 2^16. Every evaluation point must lie in the subfield GF(2^16), as `can_encode` of the reference checks and `Ligero_Geometry.Max_Encoded_Len` imposes. A larger code would need a larger subfield.
