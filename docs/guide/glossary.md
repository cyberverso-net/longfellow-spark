# Glossary

One name per thing, as the [primer](00-primer-cryptography.md) uses it. Each entry gives the place where the term is defined or first matters; where the primer defines a term, the entry repeats the primer's words and links to it. **Aliases** are the other names under which the same thing appears in the chapters; **see** points to an entry that must not be confused with this one.

The entries are grouped by subject and sorted within each group.

## The object and the claims

### Attempt

One recomputation of a hash by a cheating prover in the hope of a favourable challenge. Upstream's bound counts them: N at the transcript's hash, tA at the Merkle tree's hash. ([A9.2](00-primer-cryptography.md#a92-why-the-challenges-stay-unpredictable), [A11.4](00-primer-cryptography.md#a114-how-strong-is-the-guarantee))

### Bits of security

A probability of failure of at most 2^-k gives k bits of security. Upstream's bound, (1 + N + tA) / 2^116, gives about 116 bits, less the logarithm of the number of attempts. ([A3.4](00-primer-cryptography.md#a34-bits-of-security), [A11.4](00-primer-cryptography.md#a114-how-strong-is-the-guarantee))

### Certificate

Three senses, kept apart. (1) Upstream's **Lean certificate**: its theorems of soundness at 116 bits for the version 7 configuration. (2) A **certificate for a circuit**, the untrusted data that the planned checker of ADR 0091 will check against a registered circuit. (3) An **X.509 certificate** of the issuer's key, which this project does not read: trust in the issuer's key is the relying party's. ([A11.4](00-primer-cryptography.md#a114-how-strong-is-the-guarantee), [A1.5](00-primer-cryptography.md#a15-what-stays-outside))

Aliases: "Lean certificate" (ADR 0089, chapter 9 Section 6).

### Cheating prover

Any program that sends a proof of a false statement. It skips every check of this project's builder; only the circuits and the protocol stop it. ([A12.1](00-primer-cryptography.md#a121-the-cheating-prover), [A1.6](00-primer-cryptography.md#a16-the-honest-prover-and-any-prover))

Aliases: "dishonest prover" (chapter 9).

### Completeness

Three senses. (1) **Completeness of the prover**: every proof the honest prover writes for a true statement is accepted. Tested, not proved (register row V6); soundness does not depend on it. (2) **Completeness of the Fiat-Shamir transcript**: every public value is absorbed before each challenge, or a prover could choose it after seeing the challenge. Outside the proofs, compared with upstream by reading (register row S3). (3) **Completeness conditions on issuers**, the rows of the conditions for certifying the circuit marked "completeness": a document that breaks one cannot be proved. They limit which honest holders can prove, not what a cheating prover can. Upstream's Lean also states the **completeness of the signature circuit** (the Lean correspondence page): a valid signature satisfies the circuit. ([B7.2](00-primer-spark.md#b72-tested), [B7.4](00-primer-spark.md#b74-outside-the-proofs), [chapter 9 Section 6](09-mdoc.md#6-what-stays-trusted-and-the-limits))

See: [Soundness](#soundness).

### Conditions for certifying the circuit

The table of chapter 9 Section 6: the assumptions on the issuer, the relying party and the circuit under which the version 7 pair's guarantee holds, each with what breaks if it fails. ([A1.5](00-primer-cryptography.md#a15-what-stays-outside), [chapter 9 Section 6](09-mdoc.md#6-what-stays-trusted-and-the-limits))

### Constant time

A coding discipline: no branch and no memory index depends on a secret. Not proved; scoped to the release build, with declared exceptions. ([A12.3](00-primer-cryptography.md#a123-the-observer-of-timing))

### Extraction

The form of upstream's soundness theorem: except with negligible probability, a witness can be recovered from what the prover committed, by decoding its rows. No bound on the running time of the procedure is proved. ([A11.4](00-primer-cryptography.md#a114-how-strong-is-the-guarantee), [A1.1](00-primer-cryptography.md#a11-the-situation))

### Honest prover

This project's prover working from a credential: its witness builder refuses, before any work, a credential the circuits would mishandle. Its checks protect the holder, not a verifier. ([A1.6](00-primer-cryptography.md#a16-the-honest-prover-and-any-prover))

### Imitation

In upstream's zero-knowledge theorem, a proof produced without the secret by a program that receives only the public statement and the zero pattern; the Lean correspondence page calls that program the simulator. No one making at most 2^115 queries to the Merkle tree's hash can tell it from a real proof, except with probability 2^-127. ([A11.4](00-primer-cryptography.md#a114-how-strong-is-the-guarantee), [A12.2](00-primer-cryptography.md#a122-the-curious-verifier))

See: [Zero pattern](#zero-pattern).

### Outside the proofs

The fourth kind of claim: properties no contract of this project states, such as soundness, zero knowledge and constant time, each with what stands in for a proof. Not a separate degree of trust. ([A1.4](00-primer-cryptography.md#a14-what-certifying-it-means), [B7.4](00-primer-spark.md#b74-outside-the-proofs))

### Pad, padding

Four senses. (1) The **sumcheck pads** and (2) the **MAC pads**, two of the four kinds of randomness. (3) The **padded sumcheck**, in which every value the prover sends is sent minus one of the sumcheck pads. (4) The **padding of a message into SHA-256 blocks**, the bytes the SHA-256 standard adds to complete a message's last block, which are not random. Chapter 3 also says an array is "padded with zeroes" when it is extended to a power of two. ([A5.3](00-primer-cryptography.md#a53-the-four-kinds-of-randomness), [A7.4](00-primer-cryptography.md#a74-padding-the-messages-reveal-nothing), [A12.3](00-primer-cryptography.md#a123-the-observer-of-timing))

See: [Sumcheck pads](#sumcheck-pads), [MAC pads](#mac-pads).

### Proof

Three senses. (1) A **zero-knowledge proof**: the string of bytes the prover produces and the verifier checks; for the proof of age, two Longfellow proofs and six tags, about 360 kB at version 7. (2) A **machine-checked proof** of a property of the code, by GNATprove, or of a theorem, by Lean. (3) The **proof of age**, the use case as a whole. A **batch proof** of a Merkle tree is a part of sense 1. The guide says which, when the context does not. ([A1.2](00-primer-cryptography.md#a12-the-object-certified), [B6.6](00-primer-spark.md#b66-what-proved-means-and-what-it-does-not), [B8.1](00-primer-spark.md#b81-two-tools-two-objects))

See: [Batch proof](#batch-proof).

### Proved

Shown by a machine-checked proof for every input that meets the stated preconditions. One of the four kinds of claim. ([A1.4](00-primer-cryptography.md#a14-what-certifying-it-means), [B6.6](00-primer-spark.md#b66-what-proved-means-and-what-it-does-not))

See: [Silver](#silver), [Gold](#gold).

### Prover

The party that produces a proof; in the proof of age, the holder's device. **This project's prover** is honest; **a cheating prover** may be any program. Where the subject is SPARK, "the provers" are the SMT solvers, not this party. ([A1.1](00-primer-cryptography.md#a11-the-situation), [A1.6](00-primer-cryptography.md#a16-the-honest-prover-and-any-prover))

See: [Cheating prover](#cheating-prover), [Honest prover](#honest-prover).

### Reference

Four senses. (1) A **ghost reference**: a simple ghost function that transcribes a formula of the specification, against which the code is proved. (2) **Upstream's code at the pin**, its Rust reference implementation (`docs/specs/rust`) and its production code, which chapters 3, 4, 5 and 7 call "the reference"; the Lean correspondence page uses the word for upstream's Lean sources. (3) The **references of the test vectors**, the independent scripts that compute expected answers. (4) **Reference work**, outside the claims of the supported profile: the reference program `longfellow_prove`, which proves one circuit from a JSON file, and the reference path of `longfellow_prove_mdoc`, which takes upstream's witness files (`--hash-witness`) and skips the witness builder. ([B4.1](00-primer-spark.md#b41-ghost-code-the-specification-inside-the-program), [B7.2](00-primer-spark.md#b72-tested), [chapter 7 Section 3.7](07-prover.md#37-zk_prover-prover_status-longfellow_prove), [A1.2](00-primer-cryptography.md#a12-the-object-certified))

Aliases: "the reference" (chapters 3, 4, 5, 7 for sense 2; chapter 1 for sense 1, `Mul_Ref` and `Mul_Serial`); "Rust reference" (chapters 1, 2).

### Soundness

That a false statement is accepted only with negligible probability. A theorem of upstream, for the version 7 row, at about 116 bits. ([A11.4](00-primer-cryptography.md#a114-how-strong-is-the-guarantee), [A12.1](00-primer-cryptography.md#a121-the-cheating-prover))

See: [Extraction](#extraction), [Bits of security](#bits-of-security).

### Statement

What a proof is about: the public check and its public inputs. In the proof of age, that a credential signed under the given issuer key, bound to a device key that signed this session, valid at the given date, carries the requested attribute. ([A1.1](00-primer-cryptography.md#a11-the-situation))

### Tested

Shown on test cases whose expected answers do not come from the code under test. One of the four kinds of claim. ([A1.4](00-primer-cryptography.md#a14-what-certifying-it-means), [B7.2](00-primer-spark.md#b72-tested))

### Trust model

The page that sorts every claim of the project into the four kinds, part by part. Organised by claim. ([A1.4](00-primer-cryptography.md#a14-what-certifying-it-means), [B7.5](00-primer-spark.md#b75-reading-the-trust-model-and-the-register-together))

See: [Trusted base register](#trusted-base-register).

### Trusted

Assumed, and listed so that nothing is assumed silently. A **trusted item** is one such assumption, one row of the trusted base register. One of the four kinds of claim. ([A1.4](00-primer-cryptography.md#a14-what-certifying-it-means), [B7.3](00-primer-spark.md#b73-trusted))

### Trusted base register

The page that lists every trusted item, one row each, with a stable identifier (T1, C2, R2, S1, V4, P4, ...), what depends on it and what would discharge it. Organised by assumption. ([B7.3](00-primer-spark.md#b73-trusted))

Aliases: "the register" (throughout).

See: [Trusted](#trusted).

### Verification

Two senses. (1) What the **verifier** does with a zero-knowledge proof: accept or refuse it. (2) What GNATprove does with the code: discharge its **verification conditions**. The second is never called verification of a proof in this guide. An **ECDSA verification** is the check of a signature (A10.1), which the signature circuit performs. ([A1.1](00-primer-cryptography.md#a11-the-situation), [B6.1](00-primer-spark.md#b61-from-a-check-to-a-formula))

See: [Verifier](#verifier), [Verification condition](#verification-condition).

### Verifier

The party that checks a proof; in the proof of age, the relying party. A verifier does not know who made a proof. ([A1.1](00-primer-cryptography.md#a11-the-situation), [A1.6](00-primer-cryptography.md#a16-the-honest-prover-and-any-prover))

### Witness

What only the prover knows. The **private inputs** of a circuit are the credential's values and the helper values the prover supplies; the **combined witness** is the private inputs followed by the sumcheck's pads, and it is what the prover commits. In the primer, "the witness" alone means the private inputs; chapter 5 uses it for the combined witness. Upstream's **witness files** hold a circuit's inputs, the public ones first. ([A1.2](00-primer-cryptography.md#a12-the-object-certified), [A5.2](00-primer-cryptography.md#a52-how-longfellow-commits))

Aliases: "witness vector" (chapters 5, 7, 9: the combined witness).

See: [Private inputs](#private-inputs), [Combined witness](#combined-witness).

### Zero knowledge

That the proof reveals nothing beyond the statement, apart from one stated exception, the zero pattern of the tags: the proof can be imitated by someone who does not know the secret. A theorem of upstream; it assumes fresh, secret and uniform randomness for each proof. ([A11.4](00-primer-cryptography.md#a114-how-strong-is-the-guarantee), [A12.2](00-primer-cryptography.md#a122-the-curious-verifier))

### Zero pattern

Which of the six halves bound by the tags are zero. A zero half always gives a zero tag, so upstream's zero-knowledge theorem gives this pattern to the imitation. For a real credential no half is zero in practice. ([A11.4](00-primer-cryptography.md#a114-how-strong-is-the-guarantee), [A12.2](00-primer-cryptography.md#a122-the-curious-verifier))

## The cryptography

### Assertion

A term with coefficient 0, which states that the product of its two hands is zero; it adds nothing to any wire. Not an Ada assertion (`pragma Assert`), a check the provers must prove. ([A6.2](00-primer-cryptography.md#a62-what-the-circuit-accepts-means))

Aliases: "Z assertion, Z term" (chapters 3, 6, 7, the trust model); "assert-zero term" (the Lean correspondence page).

### Batch proof

The opening of several leaves of a Merkle tree at once, sharing the digests their paths have in common. ([A4.2](00-primer-cryptography.md#a42-a-merkle-tree-a-commitment-to-a-long-vector), [chapter 5 Section 1.2](05-ligero.md#12-merkle-trees-without-padding-the-heap-layout-and-batch-proofs))

### Blinding values

Random values at the start of each row of the tableau, as many as the opened columns, and rows of pure randomness, so that what the verifier sees reveals nothing. ([A5.2](00-primer-cryptography.md#a52-how-longfellow-commits), [A8.4](00-primer-cryptography.md#a84-why-it-is-sound-and-why-it-hides))

### Challenge

A random value the verifier would choose; with Fiat-Shamir, a hash of everything written before it. ([A7.2](00-primer-cryptography.md#a72-the-rounds), [A9.1](00-primer-cryptography.md#a91-from-a-conversation-to-a-string))

### Circuit

A fixed recipe of additions and multiplications over a field, in layers, whose outputs are zero and assertions hold exactly when its check passes. ([A6.1](00-primer-cryptography.md#a61-a-check-written-as-arithmetic))

### Circuit identifier

The digest of a circuit's content that names it; the profile names each row's two identifiers. ([A6.4](00-primer-cryptography.md#a64-the-registered-circuits-are-data), [chapter 6 Section 1.4](06-circuits.md#14-the-identifier))

### Claim

A value the prover asserts and the next step must justify: at the start, that the outputs' extension at a random point is zero; after each layer, two values of the next layer's extension. ([A7.1](00-primer-cryptography.md#a71-one-claim-per-layer), [A7.2](00-primer-cryptography.md#a72-the-rounds))

### Codeword

A row of N values produced by the Reed-Solomon code. ([A8.1](00-primer-cryptography.md#a81-reed-solomon-codes))

### Combined witness

The private inputs followed by the sumcheck pads: what the prover commits. ([A5.2](00-primer-cryptography.md#a52-how-longfellow-commits), [chapter 3 Section 1.6](03-sumcheck.md#16-the-combined-witness-and-its-layout))

Aliases: "witness vector" (chapters 5, 7, 9).

### Commitment

A sealed envelope: binding, the value cannot be changed afterwards, and hiding, the envelope reveals nothing. In Longfellow, the root of the Merkle tree over the committed columns of the tableau. ([A5.1](00-primer-cryptography.md#a51-what-a-commitment-is), [A5.2](00-primer-cryptography.md#a52-how-longfellow-commits))

### Committed columns

The columns of the tableau after the first 2k − 1, hashed into the Merkle tree: 3,230 for the version 7 hash circuit, 3,187 for the signature circuit. ([A8.2](00-primer-cryptography.md#a82-the-tableau-and-the-opened-columns))

### Digest

The output of a hash function. ([A4.1](00-primer-cryptography.md#a41-what-a-hash-function-promises))

### Example circuits

Upstream's two small example circuits `sha256` and `ecdsa2`, with their example proofs, used by chapters 5 to 7. Not the hash and signature circuits of the proof of age. ([chapter 6 Section 3.5](06-circuits.md#35-memory-and-the-supported-scale))

### Fiat-Shamir

The transform that replaces each challenge of a conversation by a hash of everything written before it, so that a proof is one string checked without dialogue. ([A9.1](00-primer-cryptography.md#a91-from-a-conversation-to-a-string))

### Frame

The encoding of one value absorbed by the transcript, which records its kind and, for a value of variable length, its length. Not a frame of the CBOR parser's stack (chapter 9), nor a frame condition of a loop invariant (chapter 7). ([A9.4](00-primer-cryptography.md#a94-how-the-transcript-makes-challenges), [chapter 4 Section 2.1](04-transcript.md#21-the-tlv-codec-of-section-32))

Aliases: "TLV codec" (chapter 4: the encoding of the frames).

### Frozen Heart

The name of a class of failures of Fiat-Shamir in other systems that forgot to hash the public inputs. ([A9.3](00-primer-cryptography.md#a93-everything-must-go-in-and-in-order))

### Hand

One of the two wires a term multiplies. ([A6.1](00-primer-cryptography.md#a61-a-check-written-as-arithmetic))

### Hash circuit

The circuit of the proof of age over GF(2^128): it hashes the MSO and the item, and compares the dates. ([A1.2](00-primer-cryptography.md#a12-the-object-certified), [A11.2](00-primer-cryptography.md#a112-the-two-circuits-of-the-proof-of-age))

### Hash function

A function from inputs of any length to a short digest of fixed length, with preimage and collision resistance. SHA-256 here, 32 bytes. ([A4.1](00-primer-cryptography.md#a41-what-a-hash-function-promises))

### Layer

A group of wires of a circuit; layer 0 holds the outputs, the last layer the inputs. ([A6.1](00-primer-cryptography.md#a61-a-check-written-as-arithmetic))

### Leaf nonce

A fresh random value hashed with each committed column, so that a column's digest reveals nothing. Not the relying party's nonce. ([A4.2](00-primer-cryptography.md#a42-a-merkle-tree-a-commitment-to-a-long-vector), [A5.3](00-primer-cryptography.md#a53-the-four-kinds-of-randomness))

Aliases: "nonce" (chapters 5 and 7).

### Ligero

The commitment scheme and its three tests that prove the sumcheck's linear and quadratic equations about the committed witness, opening only a few random columns. ([A8](00-primer-cryptography.md#a8-reed-solomon-codes-and-ligero))

### Linear test

Ligero's check of the linear equations of the sumcheck, combined into one with random weights. ([A8.3](00-primer-cryptography.md#a83-the-three-tests))

### Low-degree test

Ligero's check that the witness rows are codewords, or close to them, by a random combination of them. ([A8.3](00-primer-cryptography.md#a83-the-three-tests))

### MAC pads

Random values in both witnesses of the proof of age, one per tag, that hide the three bound values in the six public tags; one-time, fresh for each proof. ([A5.3](00-primer-cryptography.md#a53-the-four-kinds-of-randomness), [A12.2](00-primer-cryptography.md#a122-the-curious-verifier))

Aliases: "one-time pads" (chapter 9 Section 1.3); "mac_ap" (chapter 9); "share" (the Lean correspondence page).

See: [Pad, padding](#pad-padding).

### Merkle tree

A tree of digests that gives one short root for a long list of leaves; opening a leaf costs one digest per level. ([A4.2](00-primer-cryptography.md#a42-a-merkle-tree-a-commitment-to-a-long-vector))

Aliases: "Merkle heap" (chapter 5: the tree stored in one array).

### Opened columns

The committed columns the verifier draws at random and the prover reveals with a batch proof: 132 at version 7, 128 at version 6. Chapter 5 calls their number NREQ. ([A8.2](00-primer-cryptography.md#a82-the-tableau-and-the-opened-columns), [chapter 9 Section 1.2](09-mdoc.md#12-the-production-circuits))

Aliases: "queries, queried columns, openings" (chapters 5, 6, 7, 8, the Lean correspondence page).

### Private inputs

The inputs of a circuit that only the prover knows: the credential's values and the helper values it supplies. The witness. ([A1.2](00-primer-cryptography.md#a12-the-object-certified), [A6.3](00-primer-cryptography.md#a63-helping-the-circuit-what-the-prover-supplies))

### Public inputs

The inputs both sides know, which the verifier rebuilds from its own data: for the proof of age, the issuer's key, the session transcript, the requested attribute, the date and the document type, with the tags. ([A1.2](00-primer-cryptography.md#a12-the-object-certified))

### Quad

The form of a layer in the specification: its terms, each a coefficient and three wire indices. ([A6.1](00-primer-cryptography.md#a61-a-check-written-as-arithmetic), [chapter 3 Section 1.1](03-sumcheck.md#11-layered-circuits-and-the-quad-representation))

### Quadratic test

Ligero's check of the products x · y = z at the witness positions, by a random combination of the differences. ([A8.3](00-primer-cryptography.md#a83-the-three-tests))

### Random oracle

An idealised hash function that answers every new input with an independent random value. An assumption of upstream's theorems (register row S2). ([A4.1](00-primer-cryptography.md#a41-what-a-hash-function-promises), [A9.2](00-primer-cryptography.md#a92-why-the-challenges-stay-unpredictable))

### Rate

The ratio of a row's length to the committed part of its codeword: the configuration's nominal 1/7 at version 7, 1/4 at version 6. Chapters 5 and 9 give its inverse, 7 and 4, as RATE_INV, the inverse rate or the rate inverse. ([A8.2](00-primer-cryptography.md#a82-the-tableau-and-the-opened-columns), [A1.2](00-primer-cryptography.md#a12-the-object-certified), [chapter 9 Section 1.2](09-mdoc.md#12-the-production-circuits))

### Reed-Solomon code

A code that turns a row of k values into N values, the evaluations of the polynomial of degree below k through them. ([A8.1](00-primer-cryptography.md#a81-reed-solomon-codes))

### Registered circuit

A circuit file pinned by its SHA-256 in the supported profile, produced by upstream's generator and read as data. A **circuit file** in general is any file in upstream's LFC2 format, which the reader of chapter 6 accepts whether registered or not. ([A6.4](00-primer-cryptography.md#a64-the-registered-circuits-are-data), [A1.2](00-primer-cryptography.md#a12-the-object-certified), [chapter 6 Section 1.2](06-circuits.md#12-lfc2))

### Rejection sampling

Drawing again until a value is acceptable: field elements on P-256, the positions of the opened columns on both fields. Terminates with probability one, not provably (register row V4). ([A9.4](00-primer-cryptography.md#a94-how-the-transcript-makes-challenges), [B5.4](00-primer-spark.md#b54-termination))

### Root

The single digest at the top of a Merkle tree. Publishing it fixes every leaf. The root of the prover's tree is its commitment. Not a root of a polynomial, a point where it is zero (A3.3). ([A4.2](00-primer-cryptography.md#a42-a-merkle-tree-a-commitment-to-a-long-vector), [A5.2](00-primer-cryptography.md#a52-how-longfellow-commits))

### Round

One step of the sumcheck: the prover sends a polynomial of degree 2 that fixes one bit of one hand, and a challenge fixes that bit to a random value. Not a round of SHA-256, nor of the Montgomery multiplication. ([A7.2](00-primer-cryptography.md#a72-the-rounds))

### Seed

The option `--seed` of the two command-line provers, which replaces the operating system's generator by a predictable one, meant only for tests: a proof made with it is predictable by design (register row C1). With it, this project's prover writes upstream's example proofs byte for byte. Not the seed the transcript derives from its digest to draw a challenge (A9.4). ([A5.3](00-primer-cryptography.md#a53-the-four-kinds-of-randomness), [B7.2](00-primer-spark.md#b72-tested))

See: [Byte identity](#byte-identity).

### Signature circuit

The circuit of the proof of age over the base field of P-256: it verifies the two signatures. ([A1.2](00-primer-cryptography.md#a12-the-object-certified), [A11.2](00-primer-cryptography.md#a112-the-two-circuits-of-the-proof-of-age))

### Sumcheck

The protocol that reduces "the circuit accepts" to claims about the inputs, layer by layer, by rounds of polynomials of degree 2. ([A7](00-primer-cryptography.md#a7-the-sumcheck))

Aliases: "padded sumcheck" (Lean correspondence page).

### Sumcheck pads

Random values in the combined witness, one per value the sumcheck sends plus one per layer for a product, so that each message looks random. ([A5.3](00-primer-cryptography.md#a53-the-four-kinds-of-randomness), [A7.4](00-primer-cryptography.md#a74-padding-the-messages-reveal-nothing))

Aliases: "pads, pad variables" (chapter 3); "one-time pads" (chapter 3 Section 1.5, chapter 7 Section 1.3).

See: [Pad, padding](#pad-padding).

### Tableau

The table of the prover's rows, each blinded and extended into a codeword. Not the commitment, which is the root over its committed columns; not the matrix A of the linear equations of the sumcheck; and not "the matrix" of the Lean correspondence page, which is its table. ([A5.2](00-primer-cryptography.md#a52-how-longfellow-commits), [A8.2](00-primer-cryptography.md#a82-the-tableau-and-the-opened-columns))

Aliases: "the matrix" (chapter 5 Section 1.1).

### Term

A constant coefficient times the product of two wires of the next layer, its hands; a wire is a sum of terms. In chapter 3, the terms of an `Expression` of the symbolic verifier are pairs of a variable and a coefficient. ([A6.1](00-primer-cryptography.md#a61-a-check-written-as-arithmetic))

### The circuit accepts

Every output wire is zero and every assertion holds. ([A6.2](00-primer-cryptography.md#a62-what-the-circuit-accepts-means), [chapter 3 Section 1.1](03-sumcheck.md#11-layered-circuits-and-the-quad-representation))

### Transcript

The record of everything written so far in a Fiat-Shamir proof, from which each challenge is drawn. Not the session transcript, which it absorbs first. ([A9.1](00-primer-cryptography.md#a91-from-a-conversation-to-a-string), [A9.4](00-primer-cryptography.md#a94-how-the-transcript-makes-challenges))

See: [Session transcript](#session-transcript).

### Wire

One value of a layer. Every wire is a function of the inputs: there are no free wires. ([A6.1](00-primer-cryptography.md#a61-a-check-written-as-arithmetic), [A6.2](00-primer-cryptography.md#a62-what-the-circuit-accepts-means))

## Fields and polynomials

### Base field of P-256

The prime field of the 256-bit prime p = 2^256 − 2^224 + 2^192 + 2^96 − 1, in which the coordinates of the points of P-256 live; the field of the signature circuit. ([A2.2](00-primer-cryptography.md#a22-arithmetic-modulo-a-prime))

Aliases: "P-256 base field, F_p" (chapter 2); "P-256" (chapter 3 Section 5.1, for the field).

### Bind

Evaluating a multilinear extension one variable at a time; each step halves the table. ([A3.5](00-primer-cryptography.md#a35-tables-as-polynomials-multilinear-extensions), [chapter 3 Section 1.2](03-sumcheck.md#12-multilinear-extensions-bind-and-the-eq-array))

### Canonical

Written in its one standard form, below the modulus. ([A12.3](00-primer-cryptography.md#a123-the-observer-of-timing), [chapter 2 Section 1.2](02-p256-field.md#12-representation-and-canonical-form))

### Characteristic 2

The property of a field where 1 + 1 = 0, so that every element is its own opposite and subtraction is addition. ([A2.3](00-primer-cryptography.md#a23-the-field-of-two-elements))

### Field

A set of numbers with an addition and a multiplication that behave as the familiar ones, where every element but zero has an inverse. ([A2.1](00-primer-cryptography.md#a21-what-a-field-is))

### GF(2)

The field of the two elements 0 and 1, where addition is exclusive or and multiplication is and. ([A2.3](00-primer-cryptography.md#a23-the-field-of-two-elements))

### GF(2^128)

The field of 2^128 elements: polynomials of degree below 128 with bits as coefficients, multiplied modulo Q(x) = x^128 + x^7 + x^2 + x + 1. The field of the hash circuit. ([A2.4](00-primer-cryptography.md#a24-gf2128-polynomials-of-bits), [chapter 1 Section 1.1](01-gf2_128.md#11-the-field))

### Interpolation

Rebuilding a polynomial of degree d from its values at d + 1 points, by Lagrange's formula. ([A3.2](00-primer-cryptography.md#a32-a-polynomial-is-fixed-by-a-few-values))

### Inverse

The element whose product with a given one is 1, computed by a fixed chain of multiplications. That the chain gives the inverse is tested (register row V3); the Ligero verifier checks each inverse it uses. ([A2.5](00-primer-cryptography.md#a25-inverses-and-why-the-code-avoids-most-of-them))

### Limb

One machine word of a field element: two 64-bit limbs for GF(2^128), four for the base field of P-256. ([chapter 1 Section 1.2](01-gf2_128.md#12-representation), [chapter 2 Section 1.2](02-p256-field.md#12-representation-and-canonical-form))

### Multilinear extension

The one polynomial of degree at most 1 in each of n variables that equals a table of 2^n values at the points made of 0s and 1s. ([A3.5](00-primer-cryptography.md#a35-tables-as-polynomials-multilinear-extensions), [chapter 3 Section 1.2](03-sumcheck.md#12-multilinear-extensions-bind-and-the-eq-array))

### Polynomial

An expression c0 + c1·x + … + cd·x^d over a field; d is its degree. ([A3.1](00-primer-cryptography.md#a31-polynomials-over-a-field))

### Prime field

The integers modulo a prime p. ([A2.2](00-primer-cryptography.md#a22-arithmetic-modulo-a-prime))

### Scalar field of P-256

The integers modulo n, the number of points of the curve. ECDSA's equation lives here; it is not a field of the circuits. Chapter 9 Section 3.5 and the trust model call the order n "q". ([A2.2](00-primer-cryptography.md#a22-arithmetic-modulo-a-prime), [A10.1](00-primer-cryptography.md#a101-ecdsa-on-p-256))

### Schwartz-Zippel lemma

Two different polynomials of total degree d agree at a random point with probability at most d / |F|. ([A3.3](00-primer-cryptography.md#a33-few-roots-so-rare-agreement))

### Subfield GF(2^16)

The field of 2^16 elements inside GF(2^128), whose values are sent in two bytes; its basis of sixteen elements, the beta basis of chapter 1, is fixed by the specification. ([A2.4](00-primer-cryptography.md#a24-gf2128-polynomials-of-bits), [chapter 1 Section 1.6](01-gf2_128.md#16-the-subfield-gf216-and-the-beta-basis))

## The mDoc and the proof of age

### Archive

Upstream's file that ships the two circuits of one row, named by a combined identifier. ([chapter 9 Section 1.2](09-mdoc.md#12-the-production-circuits))

### Attribute

The data element a relying party asks about, such as `age_over_18`, with the value asked for. Not an Ada attribute such as `'Length` or `'Old` (B1.2). ([A1.2](00-primer-cryptography.md#a12-the-object-certified))

### av

The key of the tags, a challenge drawn from the transcript after both commitments. ([A11.2](00-primer-cryptography.md#a112-the-two-circuits-of-the-proof-of-age), [A9.3](00-primer-cryptography.md#a93-everything-must-go-in-and-in-order))

Aliases: "key share, MAC key share" (the Lean correspondence page).

### CBOR

The binary encoding of structured data of RFC 8949, used throughout the mDoc. ([A10.2](00-primer-cryptography.md#a102-cbor-and-cose))

### COSE

The format of signed CBOR of RFC 9052; a signature is computed over a `Sig_structure`. ([A10.2](00-primer-cryptography.md#a102-cbor-and-cose))

### Device key

The key pair of the holder's device, whose public half the MSO carries and whose private half never leaves the device. ([A1.1](00-primer-cryptography.md#a11-the-situation), [A10.3](00-primer-cryptography.md#a103-the-credential-and-its-three-digests))

### Document type

The type of the credential, a public input. The hash circuit does not read it: it enters only through e2, so the guarantee rests on the relying party accepting only issuers' keys that sign that document type and no other. ([A1.2](00-primer-cryptography.md#a12-the-object-certified), [A1.5](00-primer-cryptography.md#a15-what-stays-outside))

Aliases: "docType" (chapter 9: the key of the MSO).

See: [Conditions for certifying the circuit](#conditions-for-certifying-the-circuit).

### e

The digest the issuer signed: the SHA-256 of the signed message, which contains the MSO. ([A1.3](00-primer-cryptography.md#a13-the-three-digests), [A10.3](00-primer-cryptography.md#a103-the-credential-and-its-three-digests))

Aliases: "the digest the issuer signed, the issuer's signature digest" (chapter 9).

### e2

The digest the device signed: the SHA-256 of a structure built from the session transcript and the document type. The verifier computes it. ([A1.3](00-primer-cryptography.md#a13-the-three-digests), [A10.3](00-primer-cryptography.md#a103-the-credential-and-its-three-digests))

Aliases: "the device authentication digest" (chapter 9 Section 6, the trusted base register).

### ECDSA

The signature scheme of both signatures, on the curve P-256: a signature (r, s) with 1 ≤ r, s < n on a digest e. ([A10.1](00-primer-cryptography.md#a101-ecdsa-on-p-256))

### Entry point

One library entry point per role, which enforces the supported profile: `Mdoc_Prover.Prove_Profile` for the prover, `Mdoc_Verifier.Verify_Profile` for the verifier. The claims are scoped to them; the generic entry points stay for reference work, outside the claims. ([A1.2](00-primer-cryptography.md#a12-the-object-certified), [chapter 9 Section 6](09-mdoc.md#6-what-stays-trusted-and-the-limits))

See: [Reference](#reference).

### Holder

The person who keeps the credential on a device. ([A1.1](00-primer-cryptography.md#a11-the-situation))

### Issuer

The party that signs the credential, for example a national authority. ([A1.1](00-primer-cryptography.md#a11-the-situation))

### Issuer-signed item

One data element of the credential: a CBOR map with `digestID`, `random`, `elementIdentifier` and `elementValue`. ([A10.3](00-primer-cryptography.md#a103-the-credential-and-its-three-digests))

Aliases: "item" (chapter 9, where "a CBOR item" is any encoded value).

### Key

Three keys, kept apart. (1) The **issuer's key**, under which the issuer signs the MSO; a public input. (2) The **device key**, the key pair of the holder's device. (3) **`av`**, called the key of the tags: not a signature key but a challenge drawn from the transcript after both commitments. Also, by context: a **key of a CBOR map**, such as `validUntil`; and the **AES key** of the transcript's generator. ([A10.1](00-primer-cryptography.md#a101-ecdsa-on-p-256), [A1.2](00-primer-cryptography.md#a12-the-object-certified), [A9.3](00-primer-cryptography.md#a93-everything-must-go-in-and-in-order))

See: [Public key and private key](#public-key-and-private-key), [Device key](#device-key), [av](#av).

### MAC

A message authentication code; here the computation of the tags. ([A11.2](00-primer-cryptography.md#a112-the-two-circuits-of-the-proof-of-age))

### mDoc

The mobile document of ISO/IEC 18013-5: a credential whose data elements are signed by an issuer and bound to a key of the holder's device. ([A1.1](00-primer-cryptography.md#a11-the-situation))

Aliases: "credential" (throughout).

### MSO

The mobile security object: the CBOR map the issuer signs, with the value digests, the device key, the validity dates and the document type. ([A10.3](00-primer-cryptography.md#a103-the-credential-and-its-three-digests))

### Nonce

The relying party's fresh random value in the session transcript, whose freshness and single use are the relying party's. Not the leaf nonces of the Merkle tree. ([A1.5](00-primer-cryptography.md#a15-what-stays-outside), [A12.5](00-primer-cryptography.md#a125-the-replayer-the-cloner-and-the-willing-helper))

### P-256

The elliptic curve of ECDSA here, defined over the base field of P-256. ([A10.1](00-primer-cryptography.md#a101-ecdsa-on-p-256))

### Point at infinity

The neutral element of the addition of points, which plays the role of zero. ([A10.1](00-primer-cryptography.md#a101-ecdsa-on-p-256))

### Public key and private key

On P-256, a private key is a number d between 1 and n − 1; the public key is the point K = d·G, where G is the point fixed by the standard. Recovering d from K is believed infeasible. ([A10.1](00-primer-cryptography.md#a101-ecdsa-on-p-256))

See: [Key](#key).

### Relying party

The party that asks for a proof of age and verifies it. ([A1.1](00-primer-cryptography.md#a11-the-situation))

### Session transcript

The record of the exchange between the device and the relying party, defined by ISO/IEC 18013-5, which carries the relying party's fresh nonce. ([A1.1](00-primer-cryptography.md#a11-the-situation))

See: [Transcript](#transcript).

### Supported profile

The table of two rows, version 7 and version 6 with one attribute, that the system accepts. Each row names its two circuit files by their hashes, and says what may be claimed. ([A1.2](00-primer-cryptography.md#a12-the-object-certified))

Aliases: "profile" (throughout).

### Tag

One of six public values, tag = (av + pad) · half, that bind the two circuits to the same e and device key without revealing them. Not a CBOR tag, such as tag 24, nor the tag of a transcript frame (chapter 4). ([A11.2](00-primer-cryptography.md#a112-the-two-circuits-of-the-proof-of-age))

### Value digest

The SHA-256 of one issuer-signed item, as the MSO lists it. ([A1.3](00-primer-cryptography.md#a13-the-three-digests), [A10.3](00-primer-cryptography.md#a103-the-credential-and-its-three-digests))

### Version 6 and version 7

The two rows of the supported profile, named by the version of upstream's circuits. They run the same code, with the same proofs and tests. Version 7 has the nominal rate 1/7 and 132 opened columns, and upstream's theorems are stated for it; version 6 has the rate 1/4 and 128 opened columns, and no theorem covers it. What differs is what may be claimed. ([A1.2](00-primer-cryptography.md#a12-the-object-certified), [chapter 9 Section 1.2](09-mdoc.md#12-the-production-circuits))

See: [Supported profile](#supported-profile).

### Witness builder

The code that builds the witness from a credential, and refuses, before any work, one the circuits would mishandle. ([A1.6](00-primer-cryptography.md#a16-the-honest-prover-and-any-prover))

### Witness file

Upstream's files that hold a ready witness; the prover's reference path (`--hash-witness`) takes them and skips the witness builder. ([A1.2](00-primer-cryptography.md#a12-the-object-certified), [A1.6](00-primer-cryptography.md#a16-the-honest-prover-and-any-prover))

## SPARK, Ada and the evidence

### Ada

The programming language of this project, designed for systems where errors are costly. ([B1](00-primer-spark.md#b1-ada-in-two-pages))

### Always_Terminates

The aspect that, set to `False`, says that termination is not claimed; used by the rejection samplers and their callers. ([B5.4](00-primer-spark.md#b54-termination), [chapter 4 Section 3.4](04-transcript.md#34-procedures-that-may-not-terminate-always_terminates))

### Assertion level

A level at which a contract part is placed, which decides the builds that compile it: no level, `Proof_Only` and `SPARKlib_Full`, `Runtime`. ([B4.2](00-primer-spark.md#b42-assertion-levels-which-contracts-ever-run))

### Byte identity

From the same inputs and seed, this project's prover writes upstream's example proofs byte for byte. ([B7.2](00-primer-spark.md#b72-tested))

### Check

Four senses. (1) A **check GNATprove must prove**: a run-time check of Ada, or a contract, an assertion, a loop invariant or a termination. (2) The **check a circuit expresses**, written as arithmetic. (3) **`make check`**, the whole of the evidence run in order, which the gate runs. (4) The **checker** planned by ADR 0091, which will check a certificate against a registered circuit. ([B2.3](00-primer-spark.md#b23-run-time-errors-and-why-their-absence-matters), [A6.1](00-primer-cryptography.md#a61-a-check-written-as-arithmetic), [B9.2](00-primer-spark.md#b92-the-commands), [A1.5](00-primer-cryptography.md#a15-what-stays-outside))

See: [Run-time check](#run-time-check), [Circuit](#circuit), [Gate](#gate).

### Contract

A statement attached to a subprogram: a precondition, a postcondition, and what state it touches. ([B3.1](00-primer-spark.md#b31-what-a-contract-is))

### Expression function

A function whose body is one expression, written in the specification; the provers see the expression. ([B1.3](00-primer-spark.md#b13-subprograms), [B4.1](00-primer-spark.md#b41-ghost-code-the-specification-inside-the-program))

### Flow analysis

GNATprove's first phase: no variable read before it is written, and each subprogram touches only the state it declares. ([B2.2](00-primer-spark.md#b22-flow-analysis))

### Generic

A package with parameters, written once and instantiated for each set of them; the protocol is generic over a field. An **instance** is the package one instantiation produces. ([B1.4](00-primer-spark.md#b14-generics))

Aliases: "signature package" (chapter 3: Field_Signature).

### Ghost code

Code that exists only for the proofs, marked `Ghost`; removing it leaves the same program. ([B4.1](00-primer-spark.md#b41-ghost-code-the-specification-inside-the-program))

### Ghost reference

A simple ghost function that transcribes a formula of the specification, against which the efficient code is proved. ([B4.1](00-primer-spark.md#b41-ghost-code-the-specification-inside-the-program))

### Global

The aspect that says which state outside its parameters a subprogram reads or writes; `Global => null`, none. ([B3.1](00-primer-spark.md#b31-what-a-contract-is))

### GNATprove

SPARK's proof tool: flow analysis, then verification conditions sent to the solvers. ([B2.1](00-primer-spark.md#b21-a-subset-with-a-proof-tool), [B6.1](00-primer-spark.md#b61-from-a-check-to-a-formula))

### Gold

The functional contracts a unit declares are proved; what Gold covers is what the contracts state. ([A1.4](00-primer-cryptography.md#a14-what-certifying-it-means), [B7.1](00-primer-spark.md#b71-the-ladder-of-proof))

### Gold by composition

A thin wrapper over a Gold unit, whose contract follows from that one's. ([B7.1](00-primer-spark.md#b71-the-ladder-of-proof))

### Gold by definition

A function that is itself the transcription of a formula, checked by reading. ([B7.1](00-primer-spark.md#b71-the-ladder-of-proof))

### Harness

A test program that runs known-answer vectors: under `tests/` in the test build, and `interop_kat` and `first_step_bench` in the release build. ([B7.2](00-primer-spark.md#b72-tested))

### Header

The comment at the top of a specification that states what the unit implements and what is proved, tested and trusted about it. When documents disagree, it is checked against the code first, then the documents are corrected. Not the header of a circuit file (chapter 6). ([B1.1](00-primer-spark.md#b11-packages-specification-and-body), [B7.5](00-primer-spark.md#b75-reading-the-trust-model-and-the-register-together))

### Heap

Two senses. (1) The **Merkle heap**: a Merkle tree stored in one array. (2) The **heap** as memory, which a program allocates while it runs; the working sets of a verification or a proof are there, and enough of it is trusted (register row P1). ([chapter 5 Section 2.1](05-ligero.md#21-merkle-heap-batch-opening-and-batch-verification), [chapter 5 Section 3.5](05-ligero.md#35-memory-the-working-set-as-locals-sized-by-the-geometry-the-supported-scale))

See: [Merkle tree](#merkle-tree).

### Interoperability

Two directions, both tested. Upstream's proofs are accepted by this project's verifier, in the `cli` step wherever it runs. This project's proofs are accepted by upstream's verifier, in the `cli` step on the proving machine only, which holds a copy of upstream. ([B7.2](00-primer-spark.md#b72-tested), [B9.2](00-primer-spark.md#b92-the-commands))

Aliases: "interop" (chapter 6).

See: [Byte identity](#byte-identity).

### Justified

Accepted by a reviewer's comment instead of a proof. Never used in this project. ([B6.2](00-primer-spark.md#b62-who-proves-the-formulas), [B6.4](00-primer-spark.md#b64-reading-the-summary-table))

### Known-answer vector

A test case with its expected answer, from the specification, from upstream or from an independent script. ([B7.2](00-primer-spark.md#b72-tested))

Aliases: "vector" (tests and harnesses; elsewhere a vector may be a mathematical one, as the vector of challenges).

### Lemma

In SPARK, a ghost procedure whose content is its postcondition, proved once and called to hand that fact to the provers. In Lean, a lemma is a theorem, cited by its name. ([B3.4](00-primer-spark.md#b34-lemmas-theorems-the-provers-use))

### Logical_Eq

A different function: SPARKlib's equality of functional sequences, used by the transcript's ghost model. Not `Same`, although chapter 4 also calls it a logical equality. ([chapter 4 Section 3.2](04-transcript.md#32-transcript-a-package-with-state-and-the-ghost-absorbed-sequence))

### Loop invariant

A property stated inside a loop and proved true each time the loop passes it; afterwards, the main thing the provers know about the loop. ([B5.1](00-primer-spark.md#b51-loop-invariants))

### Package

The unit of organisation of Ada code: a specification (`.ads`) and usually a body (`.adb`). ([B1.1](00-primer-spark.md#b11-packages-specification-and-body))

### Partition

A group of units proved in one run of GNATprove; every non-generic unit under `src/` belongs to one. ([B6.5](00-primer-spark.md#b65-partitions-and-the-whole))

### Platinum

Full functional correctness of the whole system; not a goal of this project. ([B7.1](00-primer-spark.md#b71-the-ladder-of-proof))

### Postcondition

What is true when a subprogram returns, provided its precondition held. ([B3.1](00-primer-spark.md#b31-what-a-contract-is))

### Precondition

What must be true when a subprogram is called: an obligation on the caller. ([B3.1](00-primer-spark.md#b31-what-a-contract-is))

### Proof_Only

The project's assertion level: proved, never compiled in any build. ([B4.2](00-primer-spark.md#b42-assertion-levels-which-contracts-ever-run))

See: [SPARKlib_Full](#sparklib_full).

### Release build

The build the programs ship in: optimised, without assertions but `Runtime`, the library without run-time checks (`-gnatp`). ([B4.3](00-primer-spark.md#b43-the-builds-and-what-each-one-checks))

Aliases: "proved build" (the performance page).

### Run-time check

A condition Ada checks while the program runs: an index in range, no overflow, no division by zero, a value in its type's range. ([B2.3](00-primer-spark.md#b23-run-time-errors-and-why-their-absence-matters), [B3.3](00-primer-spark.md#b33-functional-contracts-and-the-absence-of-errors))

### Runtime

The assertion level compiled in every build, the release build included, for cheap checks on public values, with three declared exceptions. ([B4.2](00-primer-spark.md#b42-assertion-levels-which-contracts-ever-run), [A12.3](00-primer-cryptography.md#a123-the-observer-of-timing))

### Same

The logical equality of the field elements, annotated `Logical_Equal`, which lets the provers substitute equals; its body is the predefined `=`, outside SPARK (register row T6). ([B4.4](00-primer-spark.md#b44-logical-equality-same))

Aliases: "logical equality" (chapters 1, 3, 6, 7).

See: [Logical_Eq](#logical_eq).

### Silver

No run-time error, for any input that meets the preconditions. Every SPARK unit under `src/`. ([A1.4](00-primer-cryptography.md#a14-what-certifying-it-means), [B7.1](00-primer-spark.md#b71-the-ladder-of-proof))

### Silver with proved shape

Silver, with some facts about the result proved as well, not every value. ([B7.1](00-primer-spark.md#b71-the-ladder-of-proof), [chapter 5 Section 4.2](05-ligero.md#42-silver-with-proved-shape-on-the-two-verifiers-what-soundness-is-and-is-not))

### SMT solver

An automatic prover of formulas: CVC5, Z3 and Alt-Ergo here, reached through Why3. Called "the provers" where the subject is SPARK. ([B6.2](00-primer-spark.md#b62-who-proves-the-formulas))

See: [Prover](#prover).

### SPARK

A subset of Ada together with GNATprove, a tool that proves properties of the source without running it. ([B2.1](00-primer-spark.md#b21-a-subset-with-a-proof-tool))

### SPARKlib_Full

The assertion level of SPARK's own library, which no build compiles; the twin of `Proof_Only`. ([B4.2](00-primer-spark.md#b42-assertion-levels-which-contracts-ever-run))

### Steps

The machine-independent measure of a solver's work; the budget is 600,000 per check. ([B6.2](00-primer-spark.md#b62-who-proves-the-formulas), [B6.4](00-primer-spark.md#b64-reading-the-summary-table))

Not the steps PS1 to VS8 of the system map ([Step](#step)).

### Stone and Bronze

The lower steps of the ladder: the code is in the SPARK subset, and flow analysis passes. ([B7.1](00-primer-spark.md#b71-the-ladder-of-proof))

### Structural Gold

Gold against a ghost reference that transcribes a formula in a fixed order of operations; algebraic truths about the formula are tested. ([B7.1](00-primer-spark.md#b71-the-ladder-of-proof), [chapter 3 Section 4.1](03-sumcheck.md#41-structural-gold-and-what-it-does-not-say))

### Test build

The build of `tests/`, with assertions on (`-gnata`): it runs every executable contract while the harnesses run. Not the **tested build** planned for M3 (ADR 0067), a variant with hardware instructions whose units are tested rather than proved, beside the default, proved one. ([B4.3](00-primer-spark.md#b43-the-builds-and-what-each-one-checks))

Aliases: "assertion-enabled build, assertion-enabled test build" (chapters 4, 5 and 6).

### Type predicate

A property every value of a type must have, checked wherever a value is made. ([B3.5](00-primer-spark.md#b35-other-contracts-an-evaluator-meets))

Aliases: "Dynamic_Predicate" (the code).

### Unit

One package, its specification and body together. Proof partitions are lists of units. ([B1.1](00-primer-spark.md#b11-packages-specification-and-body))

Aliases: "SPARK unit" (a unit in SPARK).

### Unproved

A verification condition no solver closed within the budget; not evidence that the check is false. None is ever merged. ([B6.2](00-primer-spark.md#b62-who-proves-the-formulas), [B6.3](00-primer-spark.md#b63-reading-a-vc-message))

### Variant

A quantity that decreases, or increases within a bound, at every iteration or call, which proves termination: `Loop_Variant`, `Subprogram_Variant`. ([B5.4](00-primer-spark.md#b54-termination))

### Verification condition

The formula GNATprove writes for one check: if the program reaches this point, with what is known there, the check holds. ([B6.1](00-primer-spark.md#b61-from-a-check-to-a-formula))

Aliases: "VC" (throughout).

### Why3

The intermediate tool through which GNATprove sends verification conditions to the solvers. ([B6.2](00-primer-spark.md#b62-who-proves-the-formulas))

## Lean

### Axioms

What a Lean proof relies on beyond the kernel, printed by `#print axioms`; the standard ones are `propext`, `Classical.choice` and `Quot.sound`. ([B8.2](00-primer-spark.md#b82-what-makes-a-lean-proof-trustworthy))

### By reading

Linked by a person comparing two texts, not by a tool: the link between upstream's model and this project's code. ([B8.5](00-primer-spark.md#b85-how-the-two-chains-meet))

### Kernel

The small program at the heart of Lean that checks every step of a proof. ([B8.1](00-primer-spark.md#b81-two-tools-two-objects), [B8.2](00-primer-spark.md#b82-what-makes-a-lean-proof-trustworthy))

### Lean

An interactive theorem prover for mathematics, whose small kernel checks every step of a proof. Upstream proves its protocol theorems in Lean. ([B8.1](00-primer-spark.md#b81-two-tools-two-objects))

### Lean correspondence page

The page that compares upstream's Lean model with this project's units, row by row. ([B8.5](00-primer-spark.md#b85-how-the-two-chains-meet))

### Mathlib

The library of mathematics proved in Lean that upstream's proofs use. ([B8.1](00-primer-spark.md#b81-two-tools-two-objects))

### Model

Upstream's verifier written a second time, as mathematical definitions in Lean, with ideal objects for the hash and the transcript; upstream's theorems are about it. Not a ghost model, such as the integers of chapter 2 against which the field's limbs are proved. ([B8.1](00-primer-spark.md#b81-two-tools-two-objects))

### native_decide

A Lean feature that settles a computation by compiled code, trusting Lean's compiler as well as its kernel. Not evidence for this project's lemmas; used in upstream's numerical results. ([B8.2](00-primer-spark.md#b82-what-makes-a-lean-proof-trustworthy), [B8.6](00-primer-spark.md#b86-the-rule-on-native_decide-and-upstreams-own-evidence))

### sorry

A step left unproved in Lean; a theorem whose proof contains it is not proved. ([B8.2](00-primer-spark.md#b82-what-makes-a-lean-proof-trustworthy))

## The project's own words

### ADR

An architecture decision record in `docs/adr/`, numbered; an Accepted record's body does not change. ([the records](../adr/README.md))

Aliases: "record, decision record" (throughout).

### Block

Three senses. (1) A **block** of this project's work, delivered by one pull request. (2) A **SHA-256 block** of 64 bytes, the unit the hash processes; the hash circuit's capacity is counted in blocks, 40 at version 7 and 35 at version 6. (3) **BLOCK**, in Ligero's geometry, the length of a row of the tableau before it is extended into a codeword: 461 for the version 7 hash circuit. Also, by context: a 16-byte block of AES in the transcript's generator, an Ada `declare` block, the blocks of the additive FFT, and the "six message blocks" of the Lean correspondence page, which are the six halves the tags bind. ([A12.3](00-primer-cryptography.md#a123-the-observer-of-timing), [chapter 9 Section 3.7](09-mdoc.md#37-the-two-witnesses-and-the-proof-from-the-document), [chapter 5 Section 2.2](05-ligero.md#22-geometry-from-rate_inv-nreq-ncol-and-nw-nq-to-the-rows))

See: [Phase, milestone, block, stage](#phase-milestone-block-stage).

### Certification block

A later stage of this project's plan: traceability matrix, coverage and the evidence bundle. ([A12.3](00-primer-cryptography.md#a123-the-observer-of-timing))

### Certified circuits

A later milestone of this project, in which a checker will prove what the registered circuits compute (ADR 0091). ([A1.5](00-primer-cryptography.md#a15-what-stays-outside), [B8.4](00-primer-spark.md#b84-why-this-project-uses-both))

### Gate

The two checks a pull request needs: `verify` on GitHub Actions and `prove` posted by the proving machine. Not a gate of a circuit: this guide's circuits have terms, and "gate arity" on the verification approach page is the number of a term's hands. ([B9.3](00-primer-spark.md#b93-the-proving-machine-and-the-gate))

### Longfellow v2

Upstream's next version, under development on its branch `v2`, with new circuits (version 8); not implemented here. A reading of it is planned in a milestone of its own. ([chapter 9 Section 6](09-mdoc.md#6-what-stays-trusted-and-the-limits))

### Phase, milestone, block, stage

The project's units of work and time: phases A to E, milestones within them, blocks of one pull request, and the stages of Phase A. The guide states the current design; the records keep the history. ([the README](../../README.md))

### Proving machine

The dedicated virtual machine on Google Cloud (c4-standard-24) that checks every change before it is merged. ([B9.3](00-primer-spark.md#b93-the-proving-machine-and-the-gate))

Aliases: "prove-runner" (the gate's status).

### Reuse of a proof

When the proof inputs of a change (the files a proof depends on, named by their digest; ADR 0088) are those of a commit already proved, the gate reuses that proof and runs everything else, and says so. ([B6.5](00-primer-spark.md#b65-partitions-and-the-whole), [B9.3](00-primer-spark.md#b93-the-proving-machine-and-the-gate))

### Short path and essential route

Two readings, one inside the other. The **essential route** is the part of the primer a first reading needs: A1, A11, A12, B3, B4, B6, B7 and B10, marked in the primer's contents. The **short path**, in the guide's README, is the reading for a first assessment: the essential route plus the trust model's summary, chapter 9 Sections 1 and 6 and the trusted base register. ([the README](README.md#the-short-path-for-a-first-assessment))

### Specification

The IETF draft draft-irtf-cfrg-longfellow-00, cited by section. In Ada, "specification" is also the `.ads` file of a package; and `Mdoc_Spec.Specification` is a row of upstream's table of archives (chapter 9). ([A1.2](00-primer-cryptography.md#a12-the-object-certified), [B1.1](00-primer-spark.md#b11-packages-specification-and-body))

Aliases: "the draft" (throughout); "draft-03, draft-google-cfrg-libzk-03" (chapters 2 to 5: the earlier version of the same text, ADR 0079).

### Step

One of the stages of the proof of age on the [system map](system-map.md): PS1 to PS11 for the prover, VS1 to VS8 for the verifier, the rows of the performance matrix. Not a row of the trusted base register, whose identifiers P1 to P4 and V1 to V7 name trusted items, and not GNATprove's [steps](#steps), which count a solver's effort.

### The pin

The commit of upstream's code this project follows, d5e6be7; upstream's Lean is read at 7bf8a6b. ([A1.2](00-primer-cryptography.md#a12-the-object-certified))

### Upstream

The original project, Longfellow ZK, created at Google and donated on 2 September 2026 to the Post-Quantum Cryptography Alliance, a foundation under Linux Foundation Europe. ([A1.2](00-primer-cryptography.md#a12-the-object-certified))
