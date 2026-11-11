# Trust model

Every claim this project makes about its code falls into one of three groups ([ADR 0003](../adr/0003-proof-policy-and-trust-model.md)):

- **Proved.** GNATprove has shown it for every possible input.
- **Tested.** It holds on the committed test vectors, which come from sources outside this repository.
- **Trusted.** It is assumed. We list it here so that nothing is assumed silently.

A fourth group covers what SPARK cannot express at all, such as soundness or constant time, and says what stands in for a proof there.

The [verification approach](verification-approach.md) explains why the line falls where it does. The [trusted base register](trusted-base.md) lists the trusted items one per row, each with an identifier, what depends on it and what would discharge it. Each package header gives the same information for its own subprograms. If a header and this page disagree, the header is the one to fix.

## In short

- No run-time error is possible in the SPARK code, for any input that meets the preconditions of the units. This is the Silver level, and it holds for the whole project. A failed allocation, code outside SPARK and the probabilistic termination of the samplers stay outside, as listed below.
- The arithmetic of both fields is proved equal to a simple reference written for clarity. That the reference is the one the specification means is tested.
- The building blocks of the verifier and the prover are proved against transcriptions of the specification's formulas. That those formulas fit together into a sound protocol is a theorem of the protocol, not something SPARK can prove.
- The verifier accepts the proofs the upstream prover makes. The prover reproduces upstream's proofs byte for byte. Both facts are tested.
- The mDoc layer makes, from the credential, an mDoc proof of age in upstream's format that upstream's verifier accepts, and accepts upstream's example proofs. Both facts are tested; the layer's layouts are specified by upstream's code, not by the pinned draft, and are trusted as such. The supported profile is two rows of upstream's table, version 7 and version 6 with one attribute, enforced by one entry point per role (ADR 0089); the 116-bit Lean certificate applies to the version 7 row only.
- The toolchain, the specification, the operating system's random generator and the circuit files are trusted.
- No check is justified away and no `pragma Assume` is used. Full functional correctness of the whole system (Platinum) is not a goal.

## What is proved

**Everywhere.** Every SPARK unit is Silver for every input that meets its preconditions: no overflow, no index out of range, no division by zero, no read of an uninitialised value. This is not a claim of availability: a failed allocation is outside the proofs, and an input within the bounds can still ask for much memory and time. Units that use the heap also pass SPARK's ownership checks on every allocation. Gold, a proved functional contract, applies only where a package header declares it.

Many of these contracts are stated at the assertion level `Proof_Only`. GNATprove proves them, but they are never compiled into an executable, so the test harnesses check those units through their vectors.

**The two fields** (chapters 1 and 2).

- `GF2_128.Add`, `Xtime`, `Mul` and `Square` are proved. `Mul` and `Square` are proved equal to the ghost reference `Mul_Ref`.
- `Mdoc_Witness.Hash_Witness` and `Sig_Witness` (block 6 of Phase D, ADR 0086) write every element of their arrays, their three encoders write bit K, chunk K and pair K of their value at position K of the piece (Gold), and when `Hash_Witness` accepts the hash witness ends with the six pads where `Mdoc_Inputs.Witness_Parts` reads them (Gold on the count, and on the pads under `Result = Ok`; on a refusal the array is zero); `Mdoc_Prover.Prove_Mdoc` reports `Parse_Failed` exactly when the parse refused the document, one of the four builders' statuses when a witness cannot be built (`Prove` is then not called, and the proof is empty), and the statuses of `Prove` otherwise. That the elements are upstream's is tested (below).
- `Q256_Field`, the scalar field of P-256 (the integers modulo the order q of the group, block 6 of Phase D, ADR 0086), carries the same contracts as `P256_Field` with the constants of q, proved the same way; the one difference of its Montgomery round, the multiplication of the low word by q' = -q^-1 mod 2^64, is proved to clear that word (`Lemma_Low_Word_Clears`). `P256_Curve.Select_Element`, `Select_Point` and `Select_8` return the point the mask or the index names (Gold); `Ecdsa_Witness.Push_Legacy` changes nothing outside the 1,034 positions it is given (Gold on the frame; what it writes inside them is tested).
- `P256_Field.Add`, `Sub`, `Neg`, `Mul`, `Square`, `Is_Canonical`, `From_Bytes`, `To_Bytes`, `From_Canonical`, `To_Canonical` and `Of_Natural` are proved against a ghost integer model, `To_Int`, and a ghost prime `P`. Elements are stored in Montgomery form, x 2^256 mod p, and `Mul` is proved to be the Montgomery product A B 2^-256 mod p (ADR 0069).
- `P` is defined from the limbs of p. The proof shows that it equals 2^256 - 2^224 + 2^192 + 2^96 - 1, as a polynomial identity in 2^32.

**The sumcheck algebra** (chapter 3, for each of the two fields).

- `Eq`, `Bindeq`, `Bind`, `Lagrange_Basis`, `Eval_Quad`, `Eval_Circuit`, `Bind_G`, `Eval_Bound_Quad` and every `Expression` operation are proved equal to a ghost reference. Each reference transcribes the draft's formula in a fixed order of operations. Equality is the logical equality `Same`.
- `Eval_Circuit` carries the semantics of the Z assertions. `Symbolic_Round` is the draft's formula by definition.
- `Verifier_Core` is Silver. It is proved to emit only terms the Ligero verifier can index, with the right pad indices for the quadratic triples.
- `Verifier_Core` takes the shape of the circuit and the bound quad of each layer as inputs (ADR 0071, ADR 0080). That each bound quad equals the ghost reference `BQ_Ref` is proved where they are produced and asserted at the two calls of the core: the verifier computes them from the packed circuit with `Zk_Verifier.Bound_Quads`, through the merged runs of `Packed_HQuad` as upstream does (ADR 0073, ADR 0080); the prover takes them from its sumcheck, which uses the same kernels, and the postcondition of `Sumcheck_Prover.Prove` proves them equal to `BQ_Ref`. The core's own postcondition does not depend on that fact.
- `Input_Constraint` is Gold against the formula of Section 6.7. Term W of the constraint has witness W and coefficient `Eq2 (npublic + W)`. The constant is the public binding, summed over the public inputs in order, minus the final claim. The last terms are the claim pads, built with the operations of `Expression` (Phase D, ADR 0056).
- These are structural proofs. Their contracts say nothing about the laws of the field. That `Bindeq` agrees with `Eq`, that the Lagrange basis interpolates, and that the constraints are the upstream verifier's, are all tested. Some bodies use the ring laws of the field, each proved by the field, to reach their references with fewer products (ADR 0070).

**The transcript** (chapter 4).

- The frames of `Transcript` and the statement of `Sumcheck_Transcript` are proved on a ghost sequence of the absorbed bytes.
- `Nat` returns a value below n. `Choose` returns distinct values below n.
- `GF2_128.To_Bytes` and `From_Bytes` are proved.

**Ligero and the complete verifier** (chapter 5).

- `Merkle.Build` is proved against the recursive heap of the tree. `Merkle.Verify` accepts only when every index is below n, no index repeats and the proof is consumed exactly. The root is node 1 of the node model.
- `Ligero_Geometry.Make` is proved against `LigeroGeometry::new` and Section 4.2.1, with every row index in range.
- `Lagrange.Build` and `Evaluate` are proved against the Lagrange matrix at the queried columns. Every inverse they use multiplies back to one.
- `Ligero_Proof.Read` accepts only columns that follow the rules of Section 7.4.
- The three tests of `Ligero_Verifier` are proved against the combinations of Sections 4.4 and 4.5, through `axpy`, `vaxpy`, `dot` and `dot1`. The slice frames are proved by recursion.
- `Verifier_Core` emits only terms below `Witness_Count`.
- The two verifiers are Silver, and the status they return is proved to match its cause.

**The circuit loader** (chapter 6).

- `Uleb128.Read` returns the value of the one to four bytes it consumed.
- `Circuit_Reader.Read` returns, on `Ok`, a circuit that satisfies `Well_Formed` and whose identifier is the stored one, recomputed. Otherwise it returns null.
- `Circuit_Reader.Read_Pinned` proves the same, except that the identifier is the one the caller gives, not recomputed (ADR 0074).
- `Circuit_Reader.Read_Packed` keeps the circuit in the form of the file, without expanding the terms (ADR 0080). It proves the same on the ghost expansion `Expand (P)`: `Well_Formed`, `Isolated`, `Dead_End` and the identifier. Its walks are proved to read the layers of `Expand (P)`, each coefficient by `Same`.
- `Packed_HQuad` does the first step of a layer from the packed form: `Bind_Merge` binds g and merges the runs of equal hands from the walk, `Bind_Quad_Packed` is the verifier's bound quad on it, `Eval_Bound_Quad_Packed` the form without tables. Each is Gold on the layer of `Expand (P)`, with the references of `Sumcheck_HQuad` (ADR 0080, block 2); `Bind_Merge` without the eq2 table (Logv above 24) proves the run count only, as `Merge_Terms` does, and its coefficients are tested (below). The verifier and the prover take the packed circuit (block 3); the prover takes that branch on a layer whose Logv is above 24, where the rounds on the merged entries keep the assurance they have had since ADR 0063, tested against the reference terms.
- `Zk_Verifier.Verify` takes the packed circuit, with the loader's postcondition as its precondition at level `Proof_Only`. `Zk_Verifier.Bound_Quads` is Gold against `BQ_Ref` on the expansion `Expand (P)`; `Shape_Of (P)` is proved to satisfy `Shape_Ok` under the same hypotheses (ADR 0080, block 3).
- `Packed_Circuits.Pack` is Gold: on a well-formed circuit its result is valid and its expansion is the circuit. It serves the tests, which build circuits by hand.
- `Packed_Eval.Eval_Circuit` evaluates the packed circuit from the walk, Gold on the expansion `Expand (P)` against the references of the expanded `Eval_Circuit` (`Layer_Holds`, `Layer_Z`, the inputs copied, the status); `Sumcheck_Prover.Prove` takes the packed circuit and its bound quads are Gold against `BQ_Ref` on the expansion (ADR 0080, block 3).
- From block 3 the semantics of the two executable programs is stated on the ghost expansion `Expand (P)`, which never runs. The chain that makes it credible: `Read_Packed` is proved on the expansion and tested against `Read` term for term on every shipped circuit (block 1); the kernels of `Packed_HQuad` are proved on the layer of the expansion and tested against the expanded kernels on the small layers (block 2); `Zk_Verifier.Bound_Quads` from the packed form is proved against `BQ_Ref` on the expansion and tested against `Eval_Bound_Quad` and `Eval_Bound_Quad_T` on the expanded layers in `sumcheck_kat`, and against `Eval_Bound_Quad` on every layer of the mDoc circuits by `first_step_bench --check` in the release build (block 3); `Packed_Eval.Eval_Circuit` is proved on the expansion and tested against the expanded `Eval_Circuit` wire by wire in `prover_kat` (block 3); the plain-Ghost postconditions of `Eval_Quad` and `Eval_Circuit`, which run in the test build, are untouched.
- `Circuit_Reader.Read` and `Read_Pinned`, `Eval_Quad` and `Eval_Circuit` on the expanded circuit, `Bind_G_T`, `Merge_Runs` and `Merge_Terms`, and `Eval_Bound_Quad` stay proved as the oracles of the harnesses. None of them is on the path of the two command-line programs.

**The prover** (chapter 7).

- The writers of Sections 7.3, 7.4 and 7.5 write exactly `Proof_Len` bytes. The Ligero part satisfies the reader's rules, `Well_Coded`, at the reader's offset, with the root first.
- `Round_Evals` is proved equal to a ghost transcription of `eval_round_poly`.
- In `Encode_Row`, the systematic part equals the row; the parity part equals `Lagrange.Evaluate` for an instance that encodes with Lagrange. Both production instances encode with the FFT: there the FFT's parity equal to Lagrange is tested with vectors, not proved (register row V2).
- Each row is placed in the tableau without touching the others. The witness slots of each row hold the witnesses, the values of the triples, or zeros.
- `Merkle.Open` produces exactly the digests `Merkle.Verify` consumes, stated in `Verify`'s own model.
- `Lqc_Triples` equals the core's layout. The pad layout gives `Witness_Count` as the private inputs plus `Pad_Total`.
- Every prover unit is Silver for any circuit, inputs, configuration and random byte stream. The subfield projection and `In_Subfield` are Silver.
- `Additive_Fft` and `Rfft_P256` are Silver for every row of up to 2^16 values, and each `Extend` keeps the row as the first part of its output. In `Encode_Row`, the parity part is proved equal to the Lagrange evaluation only with the Lagrange encoder; both fields now encode by an FFT, and the parity part is tested (Phase D, ADR 0057).
- `Zk_Prover.Commit` and `Prove_Committed`, `Zk_Verifier.Receive` and `Verify_Received` are the two phases of each unit on a transcript the caller opens; `Prove` and `Verify` are their composition and keep their contracts (ADR 0085). The statuses of the phases are proved as stated, with the heap state of the record between them (`Is_Null`, `Fits`).

**The mDoc layer** (chapter 9).

- `Mdoc_Mac.Legacy_Tags` returns the six products (av + ap) m of the legacy tags, stated with the field's `Mul` and `Add` on the halves of each message.
- `Cbor_Encode.Head` returns the bytes of the CBOR head of a string of any length, by the cases of the standard.
- `Mdoc_Inputs.Hash_Inputs` fills exactly `Hash_Count` elements, the constant one first, the six tags and av last; `Sig_Inputs` fills 900 with the constant one, the key and e2 first. `Witness_Parts` returns the last six elements of the witness as the pads when it accepts.
- `Mdoc_Proof.Write_Tags` and `Read_Tags` place each tag at its offset at the front of the proof.
- `Mdoc_Prover.Prove` and `Mdoc_Verifier.Verify` are Silver with the ownership checks on the two commitments, the two proofs received and the proof buffers; their statuses are proved as stated.
- The entry points of the supported profile (ADR 0089): `Mdoc_Spec.Select_Profile` accepts only a row whose name, circuit identifiers and number of attributes are the ones given; `Mdoc_Prover.Prove_Profile` and `Mdoc_Verifier.Verify_Profile` begin with it and meet the preconditions of the flows they call from the row's values and their own checks (the prover's entry point refuses circuits that do not fit the row's configurations and buffers that are not the row's lengths); the prover's three buffers, the two witnesses and the proof, are zero on every refusal, of the profile, of the request, of the witness or of the proof; on success the witnesses hold the credential's secrets and the caller wipes them once the proof is written. What the entry points leave to their caller, as preconditions or as an obligation the contracts cannot state: the bounds of the request (at most four attributes, a date of at most 20 bytes, a document type of at most 65,535 bytes, and for the verifier a proof buffer that starts at zero), the loader's validity of the two circuits (`Circuit_Reader.Read_Packed`'s postcondition), that the circuits given are the ones their identifiers name (the entry points compare the identifiers with the row's, and the binding of an identifier to a circuit is the loader's, by the identifier it computes or, on the command line, by the SHA-256 of the pinned file; ADR 0074, the register's row C2), and, for the prover, that the one-time pads of the MAC it is given are fresh for each proof, secret and uniform: the tags hide the digest and the device key only under such pads, and pads used under two challenges reveal them (chapter 9 Section 1.3). `longfellow_prove_mdoc` draws them for each proof; the privacy of the bound values claimed here is conditional on them. Drawing them inside the entry point needs a random source in the library and is deferred to Phase E, beside the nonce (#156).
- `Cbor_Parse.Parse_Exact` is Silver on any bytes within the bound, and Gold on the invariants of its table (`Valid`): every element's range inside the parsed bytes, the head before the content, every child inside its parent, the links forward within the table, the root and only the root without a parent. `Mdoc_Parse.Parse` is Silver on any document and Gold on its ranges and offsets lying inside the document and the MSO (`In_Bounds`); `Sha256.Trace.Pad_Message` is Gold on the layout of the padded buffer.

## What is tested

The vectors live in `tests/vectors/`. Each generator is an independent Python program that aborts when its own anchors disagree with the external constants it embeds.

**The two fields.**

- `GF2_128.Mul_Ref`, and so `Mul`, follows the convention of the pinned specification: bit i is the coefficient of x^i, and reduction is by Q(x). The checks are in `gf2_128_mul.txt` and `gf2_128_square.txt`, run by `gf2_128_kat`.
- These files have three tiers. The anchors are checked against the subfield basis constants of upstream (longfellow-zk/longfellow-zk at d5e6be7, `gf2_128.rs` and `gf2_128_test.cc`). Structural cases come from the field definition. Random cases come from a Python reference built differently from `Mul_Ref`: a schoolbook product, then long division.
- `GF2_128.Inv` computes the inverse. `gf2_128_inv.txt` checks `Inv (beta_i) = g^(65535 - i)`, `E * Inv (E) = 1` on random elements and `Inv (Zero) = Zero`. Two Python references, Fermat exponentiation and the extended Euclid algorithm, must agree. The harness checks `E * Inv (E) = One` again at run time.
- The limbs of `P_Limbs` are the prime of Table 1, and the byte encoding is that of Section 7.2.1. The files `p256_add.txt`, `p256_mul.txt` and `p256_bytes.txt` are anchored on b, Gx and Gy of RFC 5903, through the curve equation.
- `P256_Field.Inv` is the inverse, by `p256_inv.txt`, with the same two references and the same run-time check.
- `Q256_Field` is the scalar field of P-256, by `q256_field.txt` (`gen_q256_vectors.py`): the order q of RFC 5903 checked by q G = O on the curve, its Montgomery constants re-derived, the window chain of `Inv` checked to read q - 2, the inverse by the same two references and the same run-time check; `q256_kat`.
- `P256_Curve` and `Ecdsa_Witness` are upstream's curve formulas and ECDSA witness, by `ecdsa_witness.txt` (`gen_ecdsa_witness_vectors.py`): the complete addition and doubling on the base point, the RFC 5903 Section 8.1 points and random non-normalised projective points, against an independent transcription; `Scalar_Mul` on the RFC 5903 key pairs and shared secret; the witness of random valid signatures as a digest; and the two signatures of upstream's test document, whose witnesses equal the signature witness files of both archives element by element (`ecdsa_kat`, the `witness_file` cases). The group law itself is not proved (register row V7).
- The generator `gen_p256_vectors.py` also re-derives the inversion chain, and the Solinas reduction table, a cross-check kept from before the Montgomery form of ADR 0069.

**The sumcheck algebra.**

- The explicit circuits of draft Appendix B.3 use the term lists of the upstream unit tests. The errata of the appendix are in ADR 0027.
- The algebra is checked against an independent Python reference, in `sumcheck_gf2_128.txt` and `sumcheck_p256.txt`. The harness also checks the Lagrange constants by `d * inv (d) = 1`, and `Bindeq` against `Eq`.
- `Verifier_Core` agrees with the upstream verifier on recorded runs with injected challenges, in `tests/vectors/upstream/`. The recordings are produced outside this repository. The harness reads them when present.

**The transcript.**

- SHA-256 and AES-256 are checked against FIPS 180-4, CAVP, FIPS 197 and SP 800-38A.
- The transcript matches draft Appendix B.2 byte for byte, over 78 chained steps (`transcript_fs.txt`).
- The GF(2^128) encoding matches Appendix B.3.3 (`gf2_128_bytes.txt`).
- Challenge derivation is checked end to end. `Replay_Challenges` and the proof reader match the recorded upstream runs on the two Appendix B.3 proofs, both with injected and with replayed challenges. An independent Python transcript recomputes every value.

**Ligero and the complete verifier.**

- The Merkle tree matches Appendix B.1.1 and an independent reference. The vectors open every subset of trees with up to nine leaves, plus eight negative cases.
- The geometry and the Lagrange tables match an independent reference. The interpolation property is checked through a Vandermonde system.
- The proof reader is tested on subfield runs and on each of the rules of Section 7.4, broken one at a time.
- The Ligero verifier is checked step by step against recorded upstream runs on the two Appendix B.3 proofs: every challenge, every chosen column, and both sides of each test. The nonces match Appendix B.3.1.
- `Zk_Verifier` accepts the two complete proofs from the proof string, on both fields. It refuses the negative cases of ADR 0040 with the expected status.

**The circuit loader.**

- The LFC2 format is checked against an independent Python reader and writer, and against the two upstream circuit files. The identifier the generator computes must equal the one each upstream file stores.
- The Appendix B.3 circuits, written in LFC2 in two encodings, load term for term. Twenty-eight malformed files are refused with their status.
- Every circuit load is repeated with `Read_Packed`. It gives `Read`'s status and header, malformed files included, and on `Ok` its walk gives `Read`'s terms, on every shipped circuit, the mDoc circuits included. Pinned, it gives `Read_Pinned`'s status and header. A third encoding of the Appendix B.3 circuits has tokens of empty segments, which `Read_Packed` does not keep.
- `sumcheck_kat` packs its two hand-built circuits with `Pack`: the walk of the packed form gives their terms back, the bound quads of the verifier from the packed form equal `Eval_Bound_Quad` and `Eval_Bound_Quad_T` on the expanded layers on every layer under the recorded challenges, and the end-to-end proofs are verified on the packed form. `prover_kat` evaluates every test circuit from the packed form and finds the wires of the expanded evaluation, proves on the packed load of the same bytes, and finds the prover's bound quads equal to the verifier's from the packed form. `interop_kat` verifies the upstream proofs on the packed load and finds, on each pinned file, the pinned packed load equal to the full one. `prover_kat` verifies its proofs on the packed load of the same bytes.
- On every layer of every circuit loaded, the run count of the packed form equals a count made on the expanded layer. On the small layers (Logv at most 10 with the eq tables, at most 128 terms without them) the first step from the packed form gives what the expanded path gives, with pseudo-random challenges: the merged terms of `Merge_Runs`, the bound quad of `Eval_Bound_Quad_T`, the value of `Eval_Bound_Quad`. The larger layers rest on the proof, which covers every size, except the merged coefficients of `Bind_Merge` without the eq2 table, which its contract does not state; `first_step_bench --check`, in the release build, compares the packed first step with `Eval_Bound_Quad` on every layer of the two mDoc version 7 circuits inside `make check` (block 3).
- The two proofs the upstream prover made, for `sha256` on GF(2^128) and `ecdsa2` on P-256, are accepted from their files. Changing one byte of the root, the sumcheck part or the Ligero part makes them fail with `Merkle_Failed`. This runs in the release build (`interop_kat`).

**The prover.**

- `longfellow_prove` reproduces the two upstream proofs byte for byte from their inputs, under the seeds of the upstream test. This is the exit criterion of Phase C.
- Proofs made under another seed, or with the system's random generator, are accepted by `longfellow_verify`.
- Piece by piece, the prover matches an independent Python transcription of the reference prover: the pads and padded sumcheck proofs, the Merkle roots, the unencoded rows and the openings of the commitment.
- The writers rewrite every proof in the repository identically.
- The complete proofs of the small circuits are accepted by `Zk_Verifier`. The statuses `input_length`, `not_satisfied`, `not_in_subfield` and `config_invalid` are each triggered. A prover with input checks turned off makes proofs of false statements, and the verifier refuses them.
- The claim of each round, which the prover tracks to take p (1) from it as upstream does, is checked at the end of every layer of every test circuit against the two claims times the bound quad (ADR 0075). The round evaluations equal the reference ones only when that claim is the true sum.
- The sixteen masks of the subfield projection are checked on all 65536 subfield elements.
- The shape of the whole tableau is checked slot by slot (ADR 0052).
- Both FFTs give the Lagrange codeword. Python transcriptions of the upstream transforms are checked against Lagrange interpolation (`gen_fft_vectors.py` for GF(2^128), `gen_rs_p256_vectors.py` for the real FFT over F_p^2), `fft_kat` checks the Ada units on those vectors and against `Lagrange.Evaluate` on random rows, and the prover's commitments and the two upstream proofs stay those of the Lagrange encoder (Phase D).
- A proof file made by this project was verified by the upstream `ZkVerifier`, by hand, through `tests/vectors/upstream/verify_proof_file.rs`.

**The mDoc layer.**

- The public parts of upstream's three witness files (the hash circuit's at versions 7 and 6, the signature circuit's) are rebuilt byte for byte from the parameters of the test case they come from, by the Python transcription of upstream's builders in `gen_mdoc_layer_vectors.py` and by `Mdoc_Inputs` in `mdoc_kat`; the six tags of each hash witness are recomputed from its ends and equal the file's and the example proof's. This is how the test case was identified (chapter 9 Section 2.2).
- The CBOR heads, the tags, e2 and the table of specifications match the Python transcription on synthetic cases: the boundaries of the heads, random tags, an empty transcript, a long document type, two attributes, a short date.
- Fresh pads placed in both witnesses by `Mdoc_Inputs.Place_Pads` are read back by `Witness_Parts` and `Sig_Pads_Match`, and the file's pads are found where the layout says, in `mdoc_kat` on both archives.
- `longfellow_prove_mdoc` makes an mDoc proof from the witness files on each archive, `longfellow_verify_mdoc` accepts it and accepts upstream's example proof of the archive, and refuses a wrong date, a wrong value, a wrong document type, a tag altered and a proof cut short: the `cli` step of `make check` (`scripts/measure-mdoc.sh mdoc`).
- `Cbor_Parse`, `Mdoc_Parse` and `Sha256.Trace` are upstream's parser, `parse_mdoc` and SHA-256 trace, by `mdoc_parse.txt` (`gen_mdoc_parse_vectors.py`, an independent Python transcription that checks itself against the front of the hash witness files of both archives before it writes): the table of 23 CBOR items and the status of 18 refused ones, 8 traces over fixed numbers of blocks, upstream's 38 test documents parsed field by field, the items of the Mustermann document in clear, 39 synthetic documents accepted or refused with upstream's status; and `mdoc_parse_kat` compares the front of each archive's hash witness file (the 768 bits of the bound values, the block count, the four offsets) with the Ada parse. The trace's state after the last block equals `Sha256.Digest` of the message on every trace vector (the two compressions share their round functions and constants).
- `Mdoc_Witness` builds upstream's two witnesses: from the Mustermann document and the pads of the archive's hash witness file, both witnesses equal the private parts of the four witness files of the two archives element by element (`mdoc_witness_kat`, `witness_file`); on the 38 test documents at version 7 and the 28 at version 6 that the builder accepts, under fixed pads and one to four attributes, the digests of both witnesses equal those of an independent Python transcription of upstream's builders (`gen_mdoc_witness_vectors.py`, which checks itself against the four files before it writes; `mdoc_witness.txt`, 66 documents and versions; the eight other documents that fit at version 6 are refusals with a zero witness, below); the refusals, an identifier the document does not hold, an item of 120 bytes, a signature value s equal to the group order, at version 6 an item whose `elementValue` entry does not follow its `elementIdentifier` entry (the eight test documents in another order, and eighteen of the 24 orders on a synthetic item, the other six and all 24 at version 7 accepted), each with its status; an item of 119 bytes accepted.
- `longfellow_prove_mdoc --mdoc` makes the proof of age from the Mustermann document at both versions and from upstream's `TEST_DATA` document, `longfellow_verify_mdoc` accepts the three, and the prover refuses an attribute the document does not hold, a file that is not CBOR, a value the document contradicts (`hash_failed not_satisfied`) and both input forms at once: the `cli` step of `make check`. `make mdoc-cases` proves and verifies every one of upstream's 38 test documents at both versions with upstream's own requests, the six negative cases refused by the circuit, at version 6 the eight documents whose item order the circuit does not frame refused by the builder, and the two documents beyond the version 6 capacity refused at the parse.
- The proofs this project makes are accepted by upstream's `run_mdoc_verifier`, and a copy with one tag altered is refused by it, through `tests/vectors/upstream/verify_mdoc.rs` built on a working copy of upstream at the pin: the last part of the `cli` step of `make check` on the proving machine, which holds cargo and a clone of upstream (`scripts/cross-check-upstream.sh`, ADR 0087); where a machine has no clone of upstream, as the hosted `verify` workflow, the step says so and is skipped (chapter 9 Section 5.1).

**Where the vectors are.**

| Area | Vector files | Generator | Harness |
|------|--------------|-----------|---------|
| GF(2^128) | `gf2_128_*.txt` | `gen_gf2_128_vectors.py` | `gf2_128_kat` |
| P-256 field | `p256_*.txt` | `gen_p256_vectors.py` | `p256_kat` |
| P-256 scalar field | `q256_field.txt` | `gen_q256_vectors.py` | `q256_kat` |
| P-256 curve and ECDSA witness | `ecdsa_witness.txt` | `gen_ecdsa_witness_vectors.py` | `ecdsa_kat` |
| The parse of the mDoc and the SHA-256 trace | `mdoc_parse.txt` | `gen_mdoc_parse_vectors.py` | `mdoc_parse_kat` |
| The two witnesses of the mDoc proof | `mdoc_witness.txt`, `upstream/mdoc/*_witness.bin` | `gen_mdoc_witness_vectors.py` | `mdoc_witness_kat` |
| Sumcheck | `sumcheck_*.txt`, `upstream/sumcheck_core_*.txt` | `gen_sumcheck_vectors.py` | `sumcheck_kat` |
| Transcript | `sha256.txt`, `aes256.txt`, `transcript_fs.txt`, `zk_proof_*.txt` | `gen_transcript_vectors.py` | `transcript_kat`, `sumcheck_kat` |
| Ligero | `merkle.txt`, `ligero_geometry.txt`, `lagrange_*.txt`, `ligero_proof.txt`, `upstream/ligero_*.txt` | `gen_ligero_vectors.py` | `ligero_kat`, `sumcheck_kat` |
| Circuits | `circuit_summary.txt`, `circuit_lfc2.txt` | `gen_circuit_vectors.py` | `circuit_kat` |
| FFTs (Phase D) | `fft.txt`, `rs_p256.txt` | `gen_fft_vectors.py`, `gen_rs_p256_vectors.py` | `fft_kat` |
| mDoc circuits (Phase D) | `mdoc_summary.txt`, from the archives in `upstream/mdoc/` | `gen_mdoc_vectors.py` | `circuit_kat` |
| mDoc layer (Phase D) | `mdoc_layer.txt`, with the witness files in `upstream/mdoc/` | `gen_mdoc_layer_vectors.py` | `mdoc_kat`; `make cli` for the round trip and the example proofs |
| Interop | `interop.txt` | `gen_circuit_vectors.py` | `interop_kat` (release build) |
| Prover | `writer.txt`, `sumcheck_prover.txt`, `ligero_commit.txt`, `zk_prove.txt` | `gen_prover_vectors.py` | `writer_kat`, `prover_kat`; `make cli` for the byte identity |

The `upstream/` recordings are produced outside this repository, by the instrumented upstream code described in ADR 0027 and ADR 0040.

## What is trusted

Each item below has a row in the [trusted base register](trusted-base.md).

**Randomness and the protocol's theorems.**

- The operating system's generator, `/dev/urandom`, read outside SPARK by `Os_Random`. Zero knowledge of the proofs `longfellow_prove` makes without `--seed` depends on it. A proof made with `--seed` is predictable by design.
- That `Simple_Rng` is the generator of the upstream test. It was transcribed, and the byte identity confirms it.
- The soundness, completeness and zero-knowledge theorems of the padded sumcheck, of Ligero and of their composition (ADR 0035, 0050, 0052). Upstream now proves soundness and zero knowledge in Lean for a model of the v7 verifier this project implements: 116-bit soundness for the pair of mDoc circuits (at 7bf8a6b), and zero knowledge within 2^-127. They stay trusted here, because the link between that model and this code is mostly by reading. [The correspondence page](lean-correspondence.md) lists it row by row. The certificate is about the version 7 geometry (rate 1/7, 132 columns): the version 7 row of the supported profile may cite it under the register's entries R2, S1, S2 and R8 to R12; the version 6 row may not, and no security level is claimed for it (ADR 0089).
- The fixed statement hash `DEFAULT_STATEMENT_HASH` of the reference (ADR 0035).

**Tools.**

- The GNAT compiler and GNATprove, including GNATprove's model of `Big_Integers`, which the P-256 ghost model uses.
- The SMT solvers: CVC5, Z3 and Alt-Ergo.
- SPARKlib's functional sequences, used as a ghost model (ADR 0031).
- That `Same`, the logical equality of each field wrapper, is the equality of its element type. Its body is the predefined `=`, outside SPARK (ADR 0023).
- The release build relies on the proof instead of checking at run time. The units of `src/` are compiled without run-time checks, because GNATprove proves that none can fail; the units of `cli/src/` keep theirs (ADR 0068). `scripts/check.sh cli` reads the switches each unit was compiled with from its ALI file, and fails if a unit of `cli/src/` was compiled without checks or a unit of `src/` with them. The instances of the library's generics made in `cli/src/` are compiled with the checks on. This holds only under the preconditions of the units. The command-line programs establish the preconditions of `Circuit_Reader.Read_Packed`, `Zk_Verifier.Verify` and `Zk_Prover.Prove` in code before each call, and `Cli_Random.Fill` changes no state the prover reads. The prover instances of the command line keep their checks, except the predicate checks of the circuit inside `Sumcheck_Prover` and `Zk_Prover`, bodies and specification, which GNATprove proves. The circuit is checked once, explicitly, where it enters the program, and the calls of the programs do not check it again (ADR 0072).

**Inputs and references.**

- The pinned specification itself.
- The upstream circuit files, as to what they compute, until this project compiles its own. Their shape is proved `Well_Formed` on load and their identifier is recomputed (ADR 0046), except for the pinned list below.
- The list of `Pinned_Circuits` in the command line: the digest of each circuit file and its identifier, checked once by a full `Read` in `interop_kat`. A file in the list is loaded without recomputing its identifier (ADR 0074).
- The upstream production reader at d5e6be7, as the definition of the LFC2 format.
- That the recordings of the upstream Ligero verifier are faithful to d5e6be7 (ADR 0040).
- The construction of the mDoc layer as upstream's code specifies it, since no document of the pinned draft covers it: the legacy tags, the layouts of the public inputs of both circuits, the fixed CBOR headers of the device authentication digest, the table of specifications (ADR 0058; register rows R8, R9). Tested against upstream's witness files and example proofs.
- The parameters of the test case the witness files and the example proofs were made from (`FAMILYNAME_MUSTERMANN_MDOC_3` of upstream's test cases), recovered by matching the files, not recorded by upstream (register row R10).
- The bound of 65,000 bytes on the session transcript, taken from upstream's pull request 223 before its merge (ADR 0058; issue #122).

**Properties tested but not proved.**

- That `Sha256` and `Aes256` compute SHA-256 and AES-256 beyond the NIST and Appendix B.2 vectors. Both are Silver (ADR 0029).
- That the two FFTs and the Lagrange encoder agree beyond the tested rows, and the algorithms as the reference implements them: Lin, Chung and Han on GF(2^128), the real FFT over F_p^2 with the reference's root of unity on P-256 (ADR 0057).
- Fermat's little theorem, behind the test anchors of both `Inv`. On the verification path every inverse is checked at run time by `Checked_Inv` (ADR 0037).
- That the absorption into the transcript is complete beyond the two Appendix B.3 proofs. The sequence of calls in `Replay_Challenges` is the checklist.
- The termination of the rejection samplers and of their callers. `Transcript.Nat` draws the Ligero columns through `Choose`, on both fields, and on P-256 the field elements are also sampled by rejection, so the verifier and the prover of both fields are declared possibly non-terminating. It is a probabilistic property, declared with `Always_Terminates` (ADR 0030).

**The machine.**

- Enough memory for one circuit and the two working sets of a verification, all on the heap. A failed allocation raises `Storage_Error`, which is outside the proofs (ADR 0047).
- GNAT building an aggregate allocator in place. The spike of ADR 0047 observed it, but the language does not guarantee it.
- A 64-bit target, behind `Unsigned_128` (ADR 0012).

## Outside the proofs, and what covers it

- **Soundness and zero knowledge of the protocol.** These are probabilistic properties, not contracts of a subprogram. The implementation follows the pinned specification step by step and cites each section, so that it is an instance of the analysed protocol and not a variant.
- **Completeness of the Fiat-Shamir transcript.** The order in which `Replay_Challenges` absorbs values was compared with the reference by reading, and is tested on the Appendix B.3 proofs. On the prover side, the byte identity with the upstream proofs tests every draw and every absorption. For the mDoc layer, the order of the two roots, the draw of av and the two statements on one transcript was compared with upstream's prover and verifier by reading, and is tested by the acceptance of upstream's example proofs and by upstream's acceptance of this project's proofs (chapter 9).
- **What the relying party checks outside the proof.** The trust in the issuer's key, the freshness of the nonce in the session transcript and the choice of the date are the relying party's; the layer binds what it is given (chapter 9 Section 6).
- **Constant time.** It is a coding discipline, documented in each package header. The guarantee holds only for builds with assertions disabled, because enabled contracts and ghost code branch on secret values (ADR 0006); the contract parts at the level `Runtime` stay on in every build, and each is on a public datum (chapter 4 Section 3.2) but two, both in `From_Bytes` over P-256, whose `Runtime` postcondition can reveal by its time at most whether the value decoded is canonical: the prover's random draws (`Sampling`), where the rejection loop branches on that anyway and ADR 0051 declares the sampling's time a function of the randomness, not of the witness; and the private inputs of the reference program `longfellow_prove`, which the procedure's result reveals anyway. It does not apply to `Transcript`, `Sha256`, `Aes256` or the units of chapter 5, which handle only the public content of a proof (ADR 0029, 0037). Nor does it apply to the parse of the credential (`Cbor_Parse`, `Mdoc_Parse`) and the padding of a message into its blocks (`Sha256.Trace.Pad_Message`), declared outside it by ADR 0086: their time depends on the structure of the holder's credential (its lengths, the positions of its fields, the number of its items), and the UTF-8 check reads the bytes of its text strings; not on the signatures, the digests or the coordinates, which the parse copies by length. The discipline applies to every operation on a value once it is extracted: the SHA-256 trace over the circuit's maximum number of blocks, the encodings of the witness, the two fields, the curve arithmetic of the ECDSA witness. Since M2, the multiplication in GF(2^128) uses integer multiplications on masked words: it assumes, as upstream does, that the processor's multiplier takes a time independent of its operands (ADR 0065). The prover is constant time by construction, unit by unit. The run-length structure of Section 7.4 depends only on position, the subfield projection is a fixed linear map, and the re-injection selects the basis elements with masks. Two branches on values derived from the witness are declared (ADR 0051).
