# Guide

This guide is written for evaluators in a certification laboratory, and for anyone who wants to understand how the system works, with no expertise in cryptography or SPARK assumed (ADR 0081). It starts with a primer and a glossary; the chapters then apply what the primer explains, stage by stage.

- **The primer:** [part 1, the cryptography](00-primer-cryptography.md), and [part 2, SPARK and the evidence](00-primer-spark.md).
- **The glossary:** [one name per thing](glossary.md), with the place where each term is defined.
- **The chapters**, one per stage of the implementation, each with the same shape: the mathematics, the algorithm, the Ada/SPARK implementation, then what the proofs guarantee for all inputs, what is only tested, what remains trusted, with the table of verification conditions and the commands to reproduce it.

## How to read it

The route goes from the claim down the chain of evidence: first what is certified and what it means to certify it, then the protocol from the top, each idea in the primer followed by the chapters' sections that apply it, then the evidence item by item.

### The short path, for a first assessment

Reading time: about four hours, estimated from its length (about 23,000 words); the author's measured time will replace this estimate at the close of the milestone.

1. The repository's [README](../../README.md), its first screen; then [A11.1](00-primer-cryptography.md#a111-the-idea-in-plain-words), the idea in plain words; optionally the [system map](system-map.md), the same flow with the units; [A1](00-primer-cryptography.md#a1-the-object-certified-and-what-certifying-it-means), the object certified and what certifying it means; then [A11](00-primer-cryptography.md#a11-longfellow-all-together) in full, where [A11.4](00-primer-cryptography.md#a114-how-strong-is-the-guarantee) states how strong the guarantee is and the four things that limit it.
2. [A12](00-primer-cryptography.md#a12-who-attacks-what), who attacks what.
3. The [trust model](trust-model.md), "In short".
4. [B3](00-primer-spark.md#b3-contracts), [B4](00-primer-spark.md#b4-ghost-code-assertion-levels-and-builds), [B6](00-primer-spark.md#b6-what-a-verification-condition-says) and [B7](00-primer-spark.md#b7-proved-tested-trusted): enough SPARK to read a contract, a table of verification conditions and a row of the trusted base register; then [B10](00-primer-spark.md#b10-a-worked-evaluation), a worked evaluation.
5. [Chapter 9 Section 1](09-mdoc.md#1-the-construction), the construction of the proof of age, and [chapter 9 Section 6](09-mdoc.md#6-what-stays-trusted-and-the-limits), the supported profile and the conditions for certifying the circuit.
6. The [trusted base register](trusted-base.md), and one proof summary: chapter 9's, at the end of [chapter 9 Section 4](09-mdoc.md#4-what-the-proofs-guarantee), the checks of the mDoc partitions. The other chapters give theirs as a table of verification conditions in the same terms ([B6.4](00-primer-spark.md#b64-reading-the-summary-table)).

### The full path, for a certification

| Step | Read | Why at this point |
|---|---|---|
| 1 | The short path, steps 1 to 4 | what is claimed, and the vocabulary of the evidence |
| 2 | [A2](00-primer-cryptography.md#a2-finite-fields), [A3](00-primer-cryptography.md#a3-polynomials-and-random-points), [A4](00-primer-cryptography.md#a4-hashes-and-merkle-trees) and [A5](00-primer-cryptography.md#a5-commitments-and-the-four-kinds-of-randomness): fields, random points, hashes and Merkle trees, commitments | the prerequisites of the protocol |
| 3 | [A6](00-primer-cryptography.md#a6-circuits), then [chapter 3 Section 1.1](03-sumcheck.md#11-layered-circuits-and-the-quad-representation) and [chapter 6 Section 1](06-circuits.md#1-the-format) | circuits: what "the circuit accepts" means, and how a circuit is read from its file |
| 4 | [A7](00-primer-cryptography.md#a7-the-sumcheck), then [chapter 3 Section 1](03-sumcheck.md#1-the-mathematics) | the sumcheck, and the verifier that ends in equations |
| 5 | [A8](00-primer-cryptography.md#a8-reed-solomon-codes-and-ligero), then [chapter 5 Section 1](05-ligero.md#1-the-mathematics) | Reed-Solomon codes and Ligero |
| 6 | [A9](00-primer-cryptography.md#a9-fiat-shamir), then [chapter 4 Section 1](04-transcript.md#1-the-mathematics) | Fiat-Shamir and the transcript |
| 7 | [Chapter 1](01-gf2_128.md) and [chapter 2](02-p256-field.md) | the two fields under the protocol |
| 8 | [B8](00-primer-spark.md#b8-lean-and-spark-two-kinds-of-proof), then the [Lean correspondence page](lean-correspondence.md) | what upstream proves about the protocol, and where its proofs stop |
| 9 | [Chapter 7](07-prover.md) and [chapter 8](08-additive-fft.md) | the side that makes proofs: needed for zero knowledge and interoperability, not for soundness |
| 10 | [A10](00-primer-cryptography.md#a10-signatures-cbor-and-the-mdoc), then [chapter 9](09-mdoc.md), Sections 2 to 6 | the mDoc layer in full, the supported profile and the conditions for certifying the circuit |
| 11 | The [trusted base register](trusted-base.md), then the [trust model](trust-model.md) in full | every trusted item, now with the vocabulary to judge it |
| 12 | [B9](00-primer-spark.md#b9-reproducing-the-evidence) and the [verification approach](verification-approach.md) | reproducing the evidence |

The other sections of the primer, [B1](00-primer-spark.md#b1-ada-in-two-pages), [B2](00-primer-spark.md#b2-spark-and-what-it-rules-out) and [B5](00-primer-spark.md#b5-loops-recursion-and-termination), are reference: read them when a chapter needs them. The [performance page](performance.md) is optional for a certification.

### What comes next

- **Chapter 10, the certified circuits**, in the milestone Certified circuits ([ADR 0091](../adr/0091-certified-circuits-milestone.md)): a checker that will prove what the registered circuits compute, today trusted ([A1.5](00-primer-cryptography.md#a15-what-stays-outside)). It opens with the conditions for certifying the circuit.
- **A reading on Longfellow v2** and its version 8 circuits, in a milestone of its own: what changes for a certification.
- **The circuit compiler**, Phase E ([ADR 0055](../adr/0055-phase-d-scope-mdoc-scale.md)), after the certification block and M3 ([ADR 0082](../adr/0082-order-after-the-memory-milestone.md), confirmed at the close of Phase D by [ADR 0090](../adr/0090-mdoc-milestone-closed-phase-d-complete.md)).

## Every page

| Page | What it holds |
|---|---|
| [Primer, part 1](00-primer-cryptography.md) | what is certified; the cryptography from first principles; the adversaries |
| [Primer, part 2](00-primer-spark.md) | SPARK, contracts and the evidence; a worked evaluation |
| [Glossary](glossary.md) | one name per thing, with its aliases in the chapters |
| [System map](system-map.md) | the proof of age step by step, PS1 to PS11 and VS1 to VS8, with the units of each step |
| [Chapter 1, GF(2^128)](01-gf2_128.md) | the binary field of the hash circuit |
| [Chapter 2, the base field of P-256](02-p256-field.md) | the prime field of the signature circuit |
| [Chapter 3, the sumcheck](03-sumcheck.md) | circuits as data, the sumcheck and the verifier's equations |
| [Chapter 4, the transcript](04-transcript.md) | Fiat-Shamir, the transcript and the replay of a proof's challenges |
| [Chapter 5, Ligero](05-ligero.md) | the commitment, the three tests and the complete verifier |
| [Chapter 6, the circuits](06-circuits.md) | the circuit file, its reader, its packed form and the command-line verifier |
| [Chapter 7, the prover](07-prover.md) | the prover, its randomness and the byte identity with upstream's proofs |
| [Chapter 8, the additive FFT](08-additive-fft.md) | the encoding of the prover's rows |
| [Chapter 9, the mDoc layer](09-mdoc.md) | the proof of age: two circuits, the tags, the witness from the credential, the supported profile, the conditions for certifying the circuit |
| [Trust model](trust-model.md) | every claim, sorted into proved, tested, trusted and outside the proofs |
| [Trusted base register](trusted-base.md) | every trusted item, one row each |
| [Lean correspondence page](lean-correspondence.md) | upstream's Lean model against this project's units |
| [Verification approach](verification-approach.md) | what a SPARK proof can and cannot say here |
| [Performance](performance.md) | time and memory against upstream |
| The [ADRs](../adr/README.md) | the decision records, cited from the chapters |

## Building, proving and testing

Requirements: [Alire](https://alire.ada.dev) with a GNAT toolchain selected (`alr toolchain --select`); GNATprove is a crate dependency and is run through `alr exec`. Python 3 is needed to regenerate the test vectors and by some steps of `make cli`.

```bash
alr build                                                     # the library
alr exec -- gnatprove -P longfellow_spark.gpr
alr exec -- gprbuild -P tests/longfellow_spark_tests.gpr -p   # the test harness, assertions on
make test                                                     # the fourteen harnesses, concurrently
make cli                                                      # the release build: interoperability harness, command-line verifier and prover
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

- Specification sections are cited by number (draft-irtf-cfrg-longfellow-00, see [ADR 0002](../adr/0002-pin-the-specification.md) and [ADR 0079](../adr/0079-specification-migrated-to-draft-irtf-cfrg-longfellow-00.md)); the text is not reproduced.
- Upstream files are cited as path and commit of longfellow-zk/longfellow-zk (formerly google/longfellow-zk).
- The four kinds of claim, [proved](glossary.md#proved), [tested](glossary.md#tested), [trusted](glossary.md#trusted) and [outside the proofs](glossary.md#outside-the-proofs), are used as the glossary defines them.
