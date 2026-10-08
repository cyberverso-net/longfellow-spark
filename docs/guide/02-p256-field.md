# Chapter 2: the P-256 base field F_p

Outline. Stage 2 is in design; the decisions are recorded in ADR 0012 to 0017 (accepted 2026-10-09) and this chapter is written as they are implemented. Headings only.

## 1. The mathematics

### 1.1 The prime p and why this field
### 1.2 Integers modulo p: representation, canonical form, equality
### 1.3 Addition and subtraction with carries and borrows
### 1.4 Multiplication: the 512-bit product
### 1.5 Reduction: the special form of p and the fold identity
### 1.6 Inversion by Fermat and the addition chain for p - 2
### 1.7 Encoding: 32 bytes little-endian (Section 7.2.1), rejection of non-canonical input

## 2. The algorithms

### 2.1 Four 64-bit limbs and 128-bit partial products
### 2.2 Schoolbook product into eight words
### 2.3 Folding the high half, step by step, with bounds
### 2.4 Constant-time conditional subtraction
### 2.5 The inversion chain and its exponent arithmetic
### 2.6 Worked example: a product at the fold boundary

## 3. The Ada/SPARK implementation

### 3.1 Types: limbs, the predicated Element, the constants
### 3.2 The ghost model: To_Int, Weight, Partial, the prime P as a Big_Integer
### 3.3 Lemmas: the split lemma, column accumulation, the fold identity, conditional subtraction
### 3.4 Add, Sub, Neg: contracts and loop invariants
### 3.5 Mul: product, fold, final subtraction, and how the proof composes
### 3.6 From_Bytes and To_Bytes
### 3.7 Inv as a fixed chain
### 3.8 Constant-time notes specific to this package

## 4. What the proofs guarantee

### 4.1 Verification condition table and prover summary
### 4.2 Statements proved for all inputs, in plain terms
### 4.3 Lemmas used and how each is proved
### 4.4 Commands to reproduce

## 5. What is only tested

### 5.1 Vector files and tiers
### 5.2 External anchors: the curve equation at the base point, the fold identity, the inverse of two
### 5.3 Why the draft's Appendix B vectors are not field anchors

## 6. What stays trusted, and the limits

### 6.1 Fermat and the inversion chain
### 6.2 Big_Integer semantics and the SPARK lemma library
### 6.3 Constant time, 64-bit target assumption, performance
