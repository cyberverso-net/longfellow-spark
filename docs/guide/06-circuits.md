# Chapter 6: the circuit loader, the heap and the interop proofs

Outline (Phase B, block 1); the sections are written as the blocks land, in the shape of the earlier chapters.

## 1. The format

### 1.1 Layered circuits as data: what the verifier needs of a circuit
### 1.2 LFC2: the header, the constants, the layers as deltas, segments and tokens
### 1.3 The identifier: SHA-256 of the canonical form, and what the transcript binds
### 1.4 Where this project is stricter than the upstream reader

## 2. The algorithms

### 2.1 ULEB128 and zigzag
### 2.2 Two passes: validate and count, allocate and fill
### 2.3 Expansion by prefix sums
### 2.4 Computing the identifier

## 3. The Ada/SPARK implementation

### 3.1 Access types under ownership: the circuit on the heap, the aggregate allocator, Free
### 3.2 Circuit_Reader: the generic, its formals, the status enumeration
### 3.3 Establishing Well_Formed on the allocated object
### 3.4 The working set of Verify in one allocation
### 3.5 The command-line verifier, outside the perimeter

## 4. What the proofs guarantee

### 4.1 Absence of run-time errors on arbitrary bytes, and the ownership checks
### 4.2 The verification condition table

## 5. What is only tested

### 5.1 Tier 1: the upstream files
### 5.2 Tier 2: an independent LFC2 reader and writer; the Appendix B.3 circuits in LFC2; the malformed cases
### 5.3 Tier 3: the two upstream proofs end to end

## 6. What stays trusted, and the limits

Memory per term, per input and per column; Storage_Error; the time of the input constraint; the LFC2 files as to meaning until Phase D.
