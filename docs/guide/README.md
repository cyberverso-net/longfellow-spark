# Guide

This guide explains the project to a reader who knows some cryptography and little or no SPARK. Each stage of the implementation has a chapter with the same shape: the mathematics, then the algorithm, then the Ada/SPARK implementation (types, contracts, ghost code, loop invariants, explained for a reader new to SPARK), then an honest account of what the proofs guarantee for all inputs, what is only tested, what remains trusted, with the verification condition table and the commands to reproduce it.

## Reading order

1. [Verification approach](verification-approach.md): what a SPARK proof can and cannot say about a zero-knowledge proof system, the assurance levels used here, and how to read a package header.
2. [Trust model](trust-model.md): every claim of the project, proved, tested or trusted, part by part.
3. [Correspondence with upstream's Lean proofs](lean-correspondence.md): how the protocol theorems upstream proves in Lean relate to the code proved here, row by row.
4. [Chapter 1, GF(2^128)](01-gf2_128.md): the binary field under the sumcheck and Ligero layers; the first complete stage.
5. [Chapter 2, the P-256 base field](02-p256-field.md): prime-field arithmetic with carries, a ghost big-integer model, and the Solinas reduction proved as a polynomial identity.
6. [Chapter 3, the sumcheck algebra and the symbolic verifier core](03-sumcheck.md): generics over a field, circuits as data, structural Gold through logical equality, sparse expressions and the constraint-emitting verifier core with challenges as input.
7. [Chapter 4, the Fiat-Shamir transcript and the challenge replay](04-transcript.md): the transcript of draft Section 3 over SHA-256 and AES-256, field serialisation and sampling, and the replay of the challenges of a proof into the record of chapter 3; the fourth complete stage.
8. [Chapter 5, Ligero and the complete verifier](05-ligero.md): the Merkle commitment, the geometry and the Reed-Solomon code by Lagrange interpolation, the Ligero proof reader and verifier, and the complete verifier from the proof string to a verdict; the fifth and last stage of Phase A.
9. [Chapter 6, the circuit loader, the heap and the interop proofs](06-circuits.md): the LFC2 format of the upstream compiler as a representation of the quad circuits of Section 6.3, the loader that proves the shape of what it returns, access types under SPARK's ownership rules, the working sets on the heap, the command-line verifier, and the two upstream proofs accepted from their files; Phase B.
10. [Chapter 7, the prover](07-prover.md): the sumcheck from the prover's side with its one-time pads, the Ligero commitment and proof, randomness as a generic formal so that a program is proved for any source, the writers as inverses of the readers, the subfield projection as a fixed linear map, the command-line prover, and the two upstream proofs reproduced byte for byte from their inputs and seeds; Phase C.
11. [Chapter 8, the additive FFT](08-additive-fft.md): the Reed-Solomon code on GF(2^128) by the FFT of Lin, Chung and Han, its subspace polynomials and novel basis, a small example by hand, the encoder of the prover switched to it, and what is proved and what is tested; Phase D.
12. [Performance](performance.md): how fast the mDoc circuits are proved and verified, the milestones, every optimisation step with its measurement, and the comparison with upstream.
13. The [architecture decision records](../adr/README.md), referenced from the chapters where a choice is explained.

Later chapters follow the roadmap: the circuit compiler (Phase D).

## Building, proving and testing

Requirements: [Alire](https://alire.ada.dev) with a GNAT toolchain selected (`alr toolchain --select`); GNATprove is a crate dependency and is run through `alr exec`. Python 3 is needed only to regenerate test vectors.

```bash
alr build                                                     # the library
alr exec -- gnatprove -P longfellow_spark.gpr
alr exec -- gprbuild -P tests/longfellow_spark_tests.gpr -p   # the test harness, assertions on
make test                                                     # the nine harnesses, concurrently
make cli                                                      # the release build: interop harness, command-line verifier and prover
python3 -I tests/vectors/gen_gf2_128_vectors.py               # regenerate vectors (optional)
python3 -I tests/vectors/gen_p256_vectors.py
python3 -I tests/vectors/gen_sumcheck_vectors.py
python3 -I tests/vectors/gen_transcript_vectors.py
python3 -I tests/vectors/gen_ligero_vectors.py
python3 -I tests/vectors/gen_circuit_vectors.py
python3 -I tests/vectors/gen_prover_vectors.py
python3 -I tests/vectors/gen_mdoc_vectors.py                  # the mDoc production circuits (Phase D)
```

`make check` runs everything in order and is the definition of done for a commit and for a pull request.

The proof summary is written to `obj/development/gnatprove/gnatprove.out`. The expected outcome at every commit is "all checks proved" and a harness run with zero failures; the chapters quote the counts of the commit they describe.

## Conventions used in the guide

- Specification sections are cited by number (draft-google-cfrg-libzk-03, see [ADR 0002](../adr/0002-pin-the-specification.md)); the text is not reproduced.
- Upstream files are cited as path and commit of google/longfellow-zk.
- "Proved" means discharged by GNATprove for all inputs; "tested" means checked on the committed vectors; "trusted" means assumed and listed as such in the [trust model](trust-model.md).
