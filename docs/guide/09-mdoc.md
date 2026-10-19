# Chapter 9: the mDoc layer and the proof of age

Outline (Phase D, block 1); the sections are written as the blocks land, in the shape of the earlier chapters.

## 1. The construction

### 1.1 What an mDoc proof of age states: the two circuits (hash over GF(2^128), signature over P-256), the attribute, the issuer's key, the transcript and the date
### 1.2 The production circuits: the LFA2 archives, their versions and configurations (zk_spec.rs), what changes between versions 6 and 7
### 1.3 The MACs that bind the two proofs (mac.rs): mac_ap, the legacy construction of version 7, the modern one of version 8
### 1.4 The public inputs of each circuit (push_input_hash, push_input_sig) and the transcript (Transcript::new (transcript), the labels)
### 1.5 The proof format (MdocProof::write): six MACs, the hash proof, the signature proof
### 1.6 The witness: from the mDoc (CBOR), the MSO and its SHA-256 trace, the attribute positions, the issuer's ECDSA signature and the device key (block 6)

## 2. The algorithms

### 2.1 run_mdoc_prover_inner step by step, and what this project does the same way
### 2.2 The witness files of the artifacts as inputs; the binary input format of longfellow_prove
### 2.3 The verifier side: run_mdoc_verifier

## 3. The Ada/SPARK implementation

### 3.1 The archive reader and the committed circuits
### 3.2 The MACs, the public inputs, the transcript labels, the ZkSpec table
### 3.3 longfellow_prove_mdoc and longfellow_verify_mdoc
### 3.4 Witness generation (block 6): CBOR parsing and constant time, what is and what is not

## 4. What the proofs guarantee

## 5. What is only tested

### 5.1 The proof accepted by run_mdoc_verifier upstream (the exit criterion of the phase)
### 5.2 The upstream example proof accepted by longfellow_verify_mdoc
### 5.3 Times and memory against the targets of ADR 0055

## 6. What stays trusted, and the limits
