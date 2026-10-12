# Chapter 3: the sumcheck algebra and the symbolic verifier core

Outline; the text is written at the end of stage 3 (ADR 0022 to 0027, Proposed).

## 1. The mathematics

### 1.1 Layered circuits and the quad representation

### 1.2 Multilinear extensions, bind and the EQ array

### 1.3 The sumcheck protocol in one layer

### 1.4 Degree-two polynomials by three evaluations; the Lagrange basis

### 1.5 One-time pads and deferred verification: why the verifier emits constraints

### 1.6 The combined witness and its layout

## 2. The algorithms

### 2.1 eq, eq2, bindeq, bind

### 2.2 eval_quad and eval_circuit, with the Z assertions

### 2.3 bind_g and eval_bound_quad

### 2.4 The symbolic round and verify_layer

### 2.5 The input constraint and the quadratic triples

## 3. The Ada/SPARK implementation

### 3.1 A field as a signature package; the two instantiations

### 3.2 Circuits as data: Term, Layer, Circuit and their predicates

### 3.3 Sumcheck_Algebra: the generic and its ghost references

### 3.4 Expression: a discriminated record under a type predicate

### 3.5 The Challenges record and the symbolic core

### 3.6 Errors as status

## 4. What the proofs guarantee

### 4.1 Structural Gold, and what it does not say

### 4.2 The verification condition table, per instance

## 5. What is only tested

### 5.1 Tier 1: the explicit circuits of Appendix B.3

### 5.2 Tier 2: the algebra against an independent reference

### 5.3 Tier 3: recorded upstream runs with injected challenges

### 5.4 Errata of draft-03 found at this stage

## 6. What stays trusted, and the limits
