# Chapter 8: the additive FFT

Outline (Phase D, block 1); the sections are written as the blocks land, in the shape of the earlier chapters.

## 1. The mathematics

### 1.1 Why interpolation at all: the Reed-Solomon code of Section 2.2 and the rows of the tableau
### 1.2 Why not the multiplicative FFT in characteristic 2: no roots of unity of order 2^k in GF(2^128)
### 1.3 The evaluation points inj(i) of Section 2.2.2 and the subspace they span; the vanishing polynomials of the subspaces
### 1.4 The novel basis of Lin, Chung and Han (2014): X_j and the subspace polynomials, the change of basis from values to coefficients
### 1.5 Evaluating on 2^l points and truncating to NCOL; cosets when NCOL exceeds 2^l; every point in the subfield, hence NCOL at most 2^16
### 1.6 P-256: the extension on consecutive points as a Lagrange middle product (kernel 1 / (k - j), binomial constants), the convolution by a number-theoretic transform; p - 1 = 2^96 q gives roots of unity of order up to 2^96 in F_p itself; what the reference does with Fp2 and why this project need not

## 2. The algorithms

### 2.1 The reference: lch14.rs and lch14_reed_solomon.rs at d5e6be7 (bidirectional_fft, fft per coset, truncation)
### 2.2 A worked example on 2^3 points by hand
### 2.3 extend (f, n, m) for arbitrary n and m within 2^l
### 2.4 The Lagrange encoder of chapter 5 as the reference encoding the harness compares against

## 3. The Ada/SPARK implementation

### 3.1 The package, its generic formals and the subspace tables
### 3.2 Butterflies on public indices: constant time by construction (ADR 0051)
### 3.3 The encoder of Ligero_Prover switched to the FFT; the verifier unchanged (Lagrange on NREQ columns)
### 3.4 Memory: the tables, the row buffers, the tableau

## 4. What the proofs guarantee

### 4.1 Silver on every input; the shapes and the changes of basis the provers close
### 4.2 The verification condition table

## 5. What is only tested

### 5.1 The FFT codeword equals the Lagrange codeword, on random rows and on every row of the upstream circuits
### 5.2 The byte identity of sha256 and ecdsa2 preserved (the codeword is the same)
### 5.3 Times before and after on the mDoc hash circuit

## 6. What stays trusted, and the limits

The mathematical identity between the two encoders beyond the tested rows; the paper's basis; the bound NCOL <= 2^16 (every evaluation point in the subfield of GF(2^16), `can_encode` of the reference), the same bound `Ligero_Geometry.Max_Encoded_Len` imposes, beyond which the code would need a larger subfield.
