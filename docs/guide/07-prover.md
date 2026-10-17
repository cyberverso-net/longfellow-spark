# Chapter 7: the prover

Outline (Phase C, block 1); the sections are written as the blocks land, in the shape of the earlier chapters.

## 1. The mathematics

### 1.1 The statement the prover proves: the outputs of layer 0 are zero
### 1.2 The sumcheck from the prover's side: round polynomials in 0, 1 and P2, binding the wires
### 1.3 One-time pads and zero knowledge: what the verifier sees, what the witness becomes
### 1.4 The Ligero commitment from the prover's side: the tableau, the random rows, the code, the tree (the 213 rows of sha256 counted)
### 1.5 The Ligero proof: y_ldt, a_full, y_dot, y_quad, the opened columns

## 2. The algorithms

### 2.1 Forward evaluation of the circuit (Eval_Circuit of chapter 3)
### 2.2 Sampling on a byte stream, in the reference's order
### 2.3 eval_round_poly, bind, the layer, the circuit
### 2.4 The tableau row by row; Reed-Solomon encoding on all columns
### 2.5 The Merkle commitment with nonces and the batch opening (4.1.3)
### 2.6 The proof, and the transcript without a copy
### 2.7 The writers: 7.3, 7.4 with the run-length structure by position (random prefix, subfield closure, the reader's rules), 7.5

## 3. The Ada/SPARK implementation

### 3.1 A generic formal for the randomness: proving a program for any source
### 3.2 Sampling, Simple_Rng in the tests, the operating system in the command line
### 3.3 Sumcheck_Prover and the Challenges record
### 3.4 Ligero_Prover: the tableau on the heap, the encoder, the opening
### 3.5 The writers and their postconditions on the readers
### 3.6 The subfield projection as a fixed linear map
### 3.7 Zk_Prover, Prover_Status (Input_Length, Not_Satisfied, Not_In_Subfield, Config_Invalid), longfellow_prove
### 3.8 Constant time in the prover: the list of ADR 0051, unit by unit

## 4. What the proofs guarantee

### 4.1 Silver on any inputs, circuit, configuration and byte stream; the ownership checks
### 4.2 Gold: the round trips, the round evaluations, the shapes, the opening
### 4.3 The verification condition table

## 5. What is only tested

### 5.1 Tier 1: the two upstream proofs reproduced byte for byte
### 5.2 Tier 2: the independent Python prover on the Appendix B.3 circuits; the writers; the projection
### 5.3 Other seeds, both verifiers; the negative cases
### 5.4 Times

## 6. What stays trusted, and the limits

The randomness source and zero knowledge; the paper's theorems; the discipline of constant time by review; memory per row and per column; the FFT and the mDoc scale.
