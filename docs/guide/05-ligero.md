# Chapter 5: Ligero and the complete verifier

Stage 5 of Phase A. Outline; the sections are written as the blocks of the stage land. The Merkle commitment (`Merkle`), the geometry and the Reed-Solomon code by Lagrange interpolation (`Ligero_Geometry`, `Lagrange`), the Ligero verifier of draft Section 4.5 and its proof reader of 7.4 (`Ligero_Verifier`, generic over the stage 3 instances), the ZK proof reader of 7.5 and the complete verifier (`Zk_Verifier`), which composes stages 3, 4 and 5 into a verdict on a proof string. Decisions: [ADR 0035](../adr/0035-stage-5-scope-ligero-and-the-complete-verifier.md) to [ADR 0040](../adr/0040-ligero-vectors-and-upstream-instrumentation.md). This chapter follows the shape of the first four.

## 1. The mathematics

### 1.1 Commitments to a matrix: Reed-Solomon rows, hashed columns

Why the witness is laid out in rows, extended by a code, and committed column by column; what the rate and the number of opened columns buy (Section 4.2, 5.1).

### 1.2 Merkle trees without padding: the heap layout and batch proofs

The 2 n array, the root at 1, batch openings that share siblings (Section 4.1).

### 1.3 The low-degree test

Why a random combination of rows is still a codeword, and why a non-codeword row is caught at the opened columns (Section 4.4.1).

### 1.4 Linear constraints by a random combination; the sum check

A W + b = 0 reduced to one inner product at random coefficients; the blinding row and why the middle WR entries of the linear polynomial sum to the negative of the combined b (Section 4.4.2).

### 1.5 Quadratic constraints through copied rows

Qx, Qy, Qz, the linear ties to the witness, and the test z - x y (Section 4.4.2).

### 1.6 Composition: from the sumcheck constraints to a verdict

What the core hands to Ligero, the pad variables as witness, the quadratic triples of the claims (Section 5, zk/verifier.rs).

## 2. The algorithms

### 2.1 Merkle heap, batch opening and batch verification

With the B.1.1 vector as a worked example.

### 2.2 Geometry: from (RATE_INV, NREQ, NCOL) and (NW, NQ) to the rows

The constraints of 4.2.1, the row indices of 4.3, the B.3.2 numbers.

### 2.3 Lagrange interpolation at the queried columns

The evaluation points of the two fields, the denominators, the identity block, the tables of ADR 0036.

### 2.4 The verifier of Section 4.5, step by step

Statement hash, geometry, length checks, the four challenge vectors, the four polynomials absorbed, the chosen columns, then Merkle, LDT, linear with the sum check, quadratic.

### 2.5 Reading a Ligero proof: run-length coded columns

The rules of 7.4 and the two B.3 cases (P-256 begins with a zero-length run, GF(2^128) does not).

### 2.6 The complete proof and the complete verifier

Section 7.5; the statement hash constant; nw and the quadratic triples.

## 3. The Ada/SPARK implementation

### 3.1 Merkle: digests as byte arrays, the heap as one array, the path as a cursor

### 3.2 Geometry as a record with a predicate; every index proved in range

### 3.3 Checked_Inv and the Lagrange tables

### 3.4 The ghost references axpy, vaxpy, dot, dot1 and the four tests

### 3.5 Memory: one allocation per verification, passed by reference; the supported scale

### 3.6 The streaming element slice and the raised bounds of the transcript

### 3.7 Errors as status: the enumeration and its postconditions

## 4. What the proofs guarantee

### 4.1 Structural Gold on Merkle, the geometry, the tables and the tests

### 4.2 Silver with proved shape on the two verifiers; what soundness is and is not

### 4.3 The verification condition table

Per package and per instance, with step counts, at the closing commit of the stage.

## 5. What is only tested

### 5.1 Appendix B.1.1 and the tier 2 Merkle trees

### 5.2 Geometries and tables against an independent reference

### 5.3 The upstream recordings of the three tests

### 5.4 The two complete proofs of Appendix B.3, accepted; the negative cases

### 5.5 Errata of draft-03 found at this stage

## 6. What stays trusted, and the limits

The soundness theorem; SHA-256 beyond the vectors; that `Inv` succeeds (every failure is a status); the supported scale and the stack; the fixed statement hash; the recordings.
