# Chapter 7: the prover

This chapter covers the other half of the protocol: from a circuit, its inputs and a source of randomness to the proof string of Section 7.5 of the specification. The prover follows the order of operations of upstream's reference, so its proofs are upstream's byte for byte:

- the mathematics of the prover's side: the sumcheck, the one-time pads, the Ligero commitment and the Ligero proof (Section 1);
- the algorithms as the reference writes them (Section 2);
- the Ada/SPARK implementation, with the constructs new to the prover explained at first use (Section 3);
- what is proved, with the verification conditions and how to reproduce them (Section 4), what is only tested (Section 5) and what stays trusted (Section 6).

The records are [ADR 0049](../adr/0049-phase-c-scope-the-prover.md) (the scope), [ADR 0050](../adr/0050-randomness-as-a-byte-stream.md) (the randomness), [ADR 0051](../adr/0051-constant-time-in-the-prover.md) (constant time), [ADR 0052](../adr/0052-gold-perimeter-for-the-prover.md) (what is proved), [ADR 0053](../adr/0053-prover-vectors-and-cross-verification.md) (the vectors), [ADR 0071](../adr/0071-prover-reuses-the-bound-quad.md) and [ADR 0075](../adr/0075-round-evaluations-from-the-claim.md) (the sumcheck as upstream's), [ADR 0080](../adr/0080-milestone-memory.md) (the packed circuit and the wires per layer) and [ADR 0085](../adr/0085-prover-and-verifier-in-two-phases.md) (the two phases). The reference is longfellow-zk/longfellow-zk at d5e6be7: `docs/specs/rust/src/sumcheck/prover.rs`, `sumcheck/pad.rs`, `ligero/prover.rs`, `ligero/reed_solomon.rs`, `merkle.rs`, `zk/prover.rs`, `zk/common.rs` and the writers of `proto/src/writer/`, with `prover.rs` and `hquad.rs` of the production code for the sumcheck.

**Before reading:** the primer's sumcheck ([A7](00-primer-cryptography.md#a7-the-sumcheck)), Reed-Solomon codes and Ligero ([A8](00-primer-cryptography.md#a8-reed-solomon-codes-and-ligero)) and Fiat-Shamir ([A9](00-primer-cryptography.md#a9-fiat-shamir)); chapter 3 (the sumcheck verifier), chapter 4 (the transcript) and chapter 5 (the Ligero verifier).

## 1. The mathematics

### 1.1 The statement

A circuit of Section 6.3 is a stack of layers. The inputs are the wires of the deepest layer, and each layer computes its outputs as quadratic forms of the layer below. The statement is that the outputs of layer 0 are all zero, and that every assertion holds: an assertion is a term with coefficient 0, which states that the product of its two input wires is zero.

- The prover knows every wire.
- The verifier knows the circuit, its identifier, the public inputs and the proof.

Chapter 3 built the verifier's side: the sumcheck of Section 6 reduces the statement, layer by layer, to claims about the inputs, and the symbolic core turns those claims into linear constraints on a vector the prover has committed to with Ligero. This chapter builds what produces the proof the core consumes.

### 1.2 The sumcheck from the prover's side

For one layer, the verifier of chapter 3 holds a claim about the layer's outputs at a random point. It checks, round by round over the bits of the two input indices, a polynomial of degree two in the round variable, given by its values at 0, 1 and a fixed point P2. The prover computes those values.

It holds the wires of the layer below as two copies, one per hand (the two input indices h0 and h1 of a term), bound progressively to the challenges. In round r of hand h, for every term t = (g, h0, h1, k) with its current coefficient k:

- the two wires of the pair (the bound hand's index with its lowest bit cleared and set) give w0 and w1;
- the other hand's wire gives `other`, and `coef = k * other`;
- the polynomial at 0 collects `coef * w0` over the terms whose index is even;
- the polynomial at P2 collects `(coef * (1 - P2)) * (w0 + P2 (w1 - w0))` over the even terms and `(coef * P2) * (w0 + P2 (w1 - w0))` over the odd ones.

These are `eval_round_poly` of `sumcheck/prover.rs`, transcribed in its order of operations by the ghost functions `Ev0_Ref` and `Ev2_Ref` of `Sumcheck_Prover`. The value at 1 is not emitted, since the verifier derives it from the claim.

After the round the prover binds the hand's wires to the challenge c (`bind` of chapter 3: w(x) := w0 + c (w1 - w0) over pairs) and updates every term's coefficient by `1 - c` or `c` according to the parity of its index, halving the index. At the end of the layer the two bound copies hold one wire each; those two values, minus their pads, are the claims the verifier checks against the next layer.

### 1.3 One-time pads and zero knowledge

Every value the prover sends in the sumcheck is computed from the wires, which are secret: p(0) and p(P2) are sums, over the terms of the layer, of products of two wire values, so a verifier that saw them in the clear could learn about the wires. Section 6.5 hides them:

- for every round and hand the prover draws two random pads hp0, hp1 and sends `p(0) - hp0` and `p(P2) - hp1`;
- for every layer it draws two claim pads c0, c1 and sends the claims minus them.

The pads are part of the committed witness vector, after the private inputs: three per layer plus four per round, the third of a layer being the product c0 c1 for the quadratic constraint that ties the claim pads (`generate_lqc_triples`).

The verifier of chapter 3 works on the padded values symbolically. Its constraints are affine in the committed witness variables, the pads among them, with the received messages as constants (Section 6.7), plus one quadratic constraint per layer on the product pad; the Ligero commitment binds them. What the verifier sees of the wires is a one-time padded image of these sums of products.

The construction is zero knowledge because the pads are uniformly random and used once. [ADR 0050](../adr/0050-randomness-as-a-byte-stream.md) states the consequence of a weak source: a predictable pad lets a verifier recover the wire from the message, and does not let a prover make a false statement pass, whose soundness rests on the challenges. What is proved and what is not:

- the theorem is the paper's and stays trusted (register row S1);
- the layout of the pads in the witness vector is proved (`Lqc_Triples`, `Lemma_Pads_Below`);
- the order in which the pads are drawn is tested against upstream's bytes.

### 1.4 The Ligero commitment from the prover's side

Section 4.3 lays out the witness vector in a tableau of NROW rows and NCOL columns. With the geometry of chapter 5 (BLOCK, DBLOCK = 2 BLOCK - 1, NREQ queries, WR = BLOCK - NREQ witnesses per row), the unencoded rows are:

1. row 0, BLOCK random elements, for the low-degree test;
2. row 1, DBLOCK random elements, the sum of whose witness slots is subtracted from the first of them so that the row's witness part sums to zero, for the linear test;
3. row 2, DBLOCK random elements with the witness slots zeroed, for the quadratic test;
4. one row per WR witnesses, each a prefix of NREQ random elements followed by the witnesses, zero beyond the vector;
5. three groups of rows, x, y and z, holding the three members of each quadratic triple at the position of the triple, with the same random prefix.

The prefix is what makes the opened columns reveal nothing: the verifier opens NREQ columns, and each row's opened values are the Reed-Solomon encoding of a polynomial whose NREQ free coefficients are uniform. A row whose witnesses lie in the subfield GF(2^16), and whose prefix is sampled in the subfield, encodes into the subfield; the proof writes its opened values in two bytes instead of sixteen (Section 7.4). The subfield boundary of the circuit file says which rows those are.

Each row is encoded on all NCOL columns: the polynomial of degree below the row's length that interpolates the row at the first points is evaluated at the other NCOL - BLOCK (or NCOL - DBLOCK) points. The first columns are the row itself; the parity columns are computed by the encoder of chapter 8. Then each committed column (NCOL - DBLOCK of them, the columns beyond the double block) is hashed with a fresh 32-byte nonce into a leaf, and the Merkle heap of chapter 5 gives the root.

The two upstream test circuits:

| Circuit | Witnesses | Rows of 256 columns | BLOCK | WR | Leaves |
|---|---|---|---|---|---|
| `sha256` | 6,657 inputs + 576 pads = 7,233 | 213 | 51 | 35 | 155 |
| `ecdsa2` | 1,042 + 485 = 1,527 | 65 | 42 | 26 | 173 |

### 1.5 The Ligero proof

After the sumcheck, the transcript holds the root, the statement and every padded value. The constraints of the core are a matrix A over the witness vector and a vector b with A w + b = 0 (the reference proves that form, "marginally more convenient"). Section 4.4: the verifier draws

- u_ldt, one per witness and quadratic row;
- alphal, one per constraint;
- alphaq, three per triple;
- u_quad, one per quadratic row.

The prover answers with four polynomials, each a combination of rows of the tableau on their systematic columns:

- y_ldt, the LDT row (row 0) plus u_ldt[i] times row 3 + i, for each of the NQW witness and quadratic rows, on BLOCK columns: y_ldt = T[ILDT] + sum u_ldt[i] T[IW + i], as in chapter 5 Section 1.3 and upstream's `prove_compute_y_ldt`; the linear and quadratic blinding rows 1 and 2 are not in it;
- y_dot, the linear row plus, row by row, the row times the encoding of that row's slice of a_full, on DBLOCK columns, where a_full is the vector over all slots that collects the alphal-weighted coefficients of A and the alphaq terms of the triples (the same `Build_A_Full` the verifier uses);
- y_quad, the quadratic row plus u_quad times (z - x y) over the three rows of each triple, on DBLOCK columns.

The transcript absorbs the polynomials (y_quad as its first NREQ and its last DBLOCK - BLOCK values) and chooses NREQ of the committed columns. The proof carries those columns of every row, their nonces and the Merkle opening of Section 4.1.3. Chapter 5 is the other side of each of these equations.

## 2. The algorithms

### 2.1 Forward evaluation

The prover evaluates the circuit first and refuses to prove when an output of layer 0 is not zero or an assertion fails (`Not_Satisfied`). It evaluates the packed circuit of chapter 6, Section 3.7, as upstream's `eval_circuit` does with `for_each_term`:

- `Packed_Eval.Eval_Layer` walks the deltas of a layer and accumulates each term as `Eval_Quad` of chapter 3 does;
- `Packed_Eval.Eval_Circuit` drives the layers;
- each layer's wires go in a heap segment of their own (`Seg_Array` of chapter 3, Section 2.2), as upstream's `eval_circuit` returns one vector per layer. The input wires of layer j are the outputs of layer j + 1, segment j + 1.

The sumcheck prover frees the segment of a layer once the layer is proved, so the wires alive at the peak are those of the layers still to prove. The sizes come from the shape of the packed circuit.

### 2.2 Sampling on a byte stream

The reference draws through one trait with one method, `Rng::bytes`, and builds every sample on it:

- a GF(2^128) element is 16 bytes;
- a P-256 element is 32 bytes little-endian, rejected at or above p and drawn again;
- a subfield element is 2 bytes mapped on the basis;
- a nonce is 32 bytes.

The order of consumption in `ZkProver::commit`:

1. the pads, layer by layer; per round hp0 of hand 0, hp1 of hand 0, hp0 of hand 1, hp1 of hand 1; then c0 and c1 (the product is computed);
2. the tableau rows in the order of Section 1.4, the x, y and z rows of one triple row interleaved as they are sampled though placed in three groups;
3. the nonces, all before any leaf is hashed.

`prove` consumes no randomness. Byte identity with the shipped proofs depends on this order and nothing else.

### 2.3 The sumcheck layer

For each layer, from 0 downwards:

1. take the layer's terms and its input wires, segment j + 1;
2. draw alpha and beta and bind the output index g to the claim point;
3. for each round and each hand, compute the two evaluations, subtract the two pads of the round and hand, write them to the transcript, draw the challenge, bind the hand's wires to it and update the terms;
4. after the rounds, write the two claims, the first wire of each bound copy minus the claim pads;
5. free segment j + 1, as upstream's `prove_core` drops each layer's vector.

The reference clones the transcript before the sumcheck and replays the symbolic core on the original. This project's transcript has state and no copy ([ADR 0028](../adr/0028-stage-4-scope-and-challenge-replay.md)), so:

- the prover runs on the live transcript and records every challenge it draws in the `Challenges` record of chapter 3, alpha_input last;
- the core runs with the challenges as input ([ADR 0022](../adr/0022-stage-3-scope-and-challenges-as-input.md));
- the transcript's state after that is the one the reference has after its replay, since the same bytes were absorbed and the same draws made.

### 2.4 The tableau row by row

1. Allocate the commitment.
2. For each row of Section 1.4, fill the unencoded row, encode it (the systematic part is the row, the parity part is the encoder's) and write it into the tableau.
3. Draw the nonces, hash the leaves and build the heap.

The encoder is the additive FFT on GF(2^128) and the real FFT on P-256 (chapter 8). The Lagrange encoder of chapter 5, k multiplications per parity column per row, stays in the code as the reference encoder.

### 2.5 The Merkle opening

`open_merkle_heap` of `merkle.rs` walks the heap from node N - 1 down to 1 and, for every node on a path from an opened leaf, pushes the digest of the child that is not on a path. `Merkle.Verify` of chapter 5 consumes exactly those digests in that order; `Merkle.Open` produces them, and its postcondition says so in `Verify`'s own model (Section 3.4).

### 2.6 The proof, and the writers

`Zk_Prover.Prove` composes `zk/prover.rs`:

1. validate (Section 3.7);
2. draw the pads, assemble the witness vector (the private inputs, then the pads), generate the triples, commit;
3. reset the transcript to the label, write the root and the statement (identifier, public inputs, a zero, the term count);
4. run the sumcheck and the core;
5. run the Ligero proof under the fixed statement hash of `zk/common.rs` (register row R6);
6. write the bytes with the writers of chapter 7 of the draft: the root; the sumcheck part (Section 7.3: per layer and round, hand 0 at 0, hand 1 at 0, hand 0 at P2, hand 1 at P2, then the two claims); the Ligero part (Section 7.4: the four polynomials, the nonces, the opened columns in runs of full-field and subfield elements, the path).

The run-length structure of Section 7.4 is decided by position, not by value ([ADR 0051](../adr/0051-constant-time-in-the-prover.md)). The reference writer tests each opened element for subfield membership and groups the rows accordingly. This project groups the three random rows, then the witness rows wholly below the subfield boundary, then the rest. That gives the same runs: a subfield row encodes into the subfield by closure, and a full-field row encodes outside it except with probability 2^-112 per element, thanks to its random prefix.

- The shipped `sha256` proof shows the three runs the rule predicts: 48, 1,360 and 2,000 elements.
- On P-256 the field is its own subfield, and the reference writes one subfield run of every element at full width, which the `ecdsa2` proof shows.

## 3. The Ada/SPARK implementation

### 3.1 A generic formal for the randomness

Every unit of the prover that draws randomness is generic over the source. `Sampling` takes a field signature and a formal procedure `Fill (B : out Byte_Array)`; `Sumcheck_Prover`, `Ligero_Prover` and `Zk_Prover` take an instance of `Sampling` among their formal packages.

GNATprove analyses an instance, not the generic, so a proof holds for whatever `Fill` the instance names: the library instances name `Simple_Rng.Fill`, the command-line provers' instances `Cli_Random.Fill`, which reads the operating system's generator, or `Simple_Rng` under `--seed` (Section 3.2). Nothing in the proofs depends on the bytes being random. What is proved is absence of run-time errors and the structural contracts, for any byte stream; what the randomness buys, zero knowledge, is the paper's theorem (register row S1).

The sampling loops of P-256 are literal rejection loops with no cap, declared possibly non-terminating as in chapter 4 (`Always_Terminates => not Sampling_Rejects`, register row V4). On GF(2^128) the loop is dead and the procedure is proved terminating.

A procedure formal, rather than a type with state, is the smallest interface that matches the reference's trait, and a source with state is one instance of it. The formal has no Global aspect, so the global state of the source is whatever the actual's is. The units that call through it leave their own Global aspects to be synthesised, since the generic cannot name a state it does not know; `Zk_Prover.Prove` says so in its header.

### 3.2 Sampling, Simple_Rng and the command line

`Simple_Rng` is the linear congruential generator of upstream's reference test (`tests/test_reference.rs`): state times 6364136223846793005 plus 1442695040888963407 modulo 2^64 per byte, the byte being bits 32 to 39 of the new state (register row R7).

- It is a SPARK library package with one abstract state, because the library-level instances of the prover units name their source at instantiation and GNATprove analyses only those ([ADR 0050](../adr/0050-randomness-as-a-byte-stream.md)).
- It is a test source: `longfellow_prove` offers it only behind `--seed`.

The default source of the command line is `Os_Random`, which reads `/dev/urandom` and is `SPARK_Mode (Off)`, since it does input on a device file (register rows C1 and P4). One procedure, `Cli_Random.Fill`, reads one or the other according to whether a seed was set, so the command line has one chain of instances over it, where two chains would have been instantiated inside the program's generic body.

### 3.3 Sumcheck_Prover

`Sumcheck_Prover` is generic over the transcript glue of chapter 4 (which carries the algebra and the verifier core, hence the layouts of the padded proof, the challenges and the pad variables), over `Sampling`, and over the packed kernels of `Packed_HQuad` (chapter 3, Section 3.5). Its parts:

- `Sample_Pads` fills the pad vector in the reference's order.
- `Lqc_Triples` numbers the quadratic constraints of the claim pads as `Verifier_Core` emits them, proved equal to the core's `Pad_Off` layout.
- `Prove` runs the layers on the live transcript and fills the `Challenges` record and the padded `Sumcheck_Proof` of chapter 3. It takes the segments of `Packed_Eval.Eval_Circuit`, reads segment j + 1 for layer j and frees it once the layer is proved, segment 0 (the outputs, read by no layer) first. Its precondition asks every segment at its size (`Segs_Shape`), its postcondition leaves every one null (`Segs_Null`).
- `Prove_Layer` runs one layer and returns its bound quad.
- `Bind_Round` keeps the invariant of the rounds across one hand of one round.

`Prove_Layer` runs the sumcheck as upstream's production prover does (`prover.rs` and `hquad.rs`):

- **The terms, bound and merged from the walk.** `Bind_Merge` of `Packed_HQuad` binds g with the eq2 table of chapter 3 (one product per term instead of an eq per term) and merges the consecutive terms with the same hands into one, into a working array of `Layer_Runs` entries, one per run of equal hands. On the mDoc hash circuit the merging cuts the terms visited by the rounds fifteen times. Beyond the size of the eq tables the bound quad is `Eval_Bound_Quad_Packed`, a sum over the walk, as the verifier's.
- **The round polynomial in the dense form.** `Round_Evals_Dense` adds, for each term, k times its other-hand wire to one vector, then sums over the pairs. It takes two products per pair, as `quad_round_poly` does ([ADR 0075](../adr/0075-round-evaluations-from-the-claim.md)): a0 = sum q0 w0 and a2 = sum dq dw, with s1 = p (1) taken as the claim of the round minus a0, as the verifier does. Then p (P2) = a0 + P2 (s1 - a0 - a2) + P2^2 a2.
- **The claim, tracked as upstream does:** claim0 + alpha claim1 at the start of a layer, then p at the challenge after each round.
- **The hands, bound where they are,** as upstream's `layer` does. Hand 1 is the wire segment itself, bound in place by `Bind_In_Place` of chapter 3; hand 0 reads the same segment at round 0 and is bound out of place by `Bind` into a vector of half the width, then in place. One accumulator serves the round polynomial: one and a half vectors of the layer's width beside the segment.
- **The terms, at every round:** `Bind_H` merges the two corners 2i and 2i + 1 of the bound hand by affine interpolation, in place, so the terms shrink with the rounds.
- **The bound quad,** returned for each layer, as upstream's `SumcheckProofAux` ([ADR 0071](../adr/0071-prover-reuses-the-bound-quad.md)). After the last round of a layer, the terms left all have both hands at 0, and the sum of their coefficients is the bound quad. `Zk_Prover` passes it to `Verifier_Core`, which does not recompute it for the prover: on the mDoc hash circuit, 41.1 M field products become 0.3 M.

What the contracts say:

- `Round_Evals_Dense` is Gold against `QW_Ref` and `D0_Ref`. The postcondition states upstream's formula for p (P2) for any claim, and `D2_Ref` when the claim given is the true sum (`Lemma_D2_Split`, by induction over the pairs, and `Lemma_Cancel_L_F`; the identities come from `Ring_Laws`, restated by `Sumcheck_Algebra` on the field operations the prover uses). That the tracked claim is the true sum is the completeness of the sumcheck: tested, not proved (register row V6).
- `Bind_In_Place` is Gold against the reference of `Bind` on the vector as it came: entry i from entries 2i and 2i + 1, which are read before they are overwritten.
- `Bind_H` is Gold, structurally, against `Rd` (where output k reads) and `Corner_K` (the interpolation).
- The postcondition of `Prove`, at the level `Proof_Only`, is that each bound quad equals `BQ_Ref` of chapter 3 on the ghost expansion `Exp (P)` of the packed circuit. It is the precondition of `Verifier_Core`.

The proof of the bound quad is an invariant on coefficients, kept round by round: for each pair of residual hands, the coefficients of the terms left equal the bound terms of the layer times the factors of the challenges drawn so far. It is stated on `Bound_Layer` of `Packed_HQuad`, the layer of the expansion bound with g, a value of level `Proof_Only`. The executable statements read the shape of the packed circuit, the references the shape of the expansion, equal field by field; `Lemma_Chal_Off_Eq` of `Sumcheck_Verifier` joins the two at the offset of each layer, since `Chal_Off` hides its recursion.

The reference forms stay in the code, proved, as the oracles of the harnesses: `Round_Evals` (the transcription of `eval_round_poly` through the ghost references, with the logical equality `Same` of chapter 3), `Bind_G`, `Update_Terms`, `Bind_G_T`, `Merge_Runs` (Gold, structurally, against `Run_Id` and `Run_Sum`), `Merge_Terms` and `Eval_Bound_Quad`. The harness runs both forms on every layer, every round and both hands, and checks that the round polynomials agree; `prover_kat` also checks, on every layer of every test circuit, that the prover's bound quad equals the verifier's (`Zk_Verifier.Bound_Quads` on the packed load of the same bytes), and makes upstream's check at the end of each layer, the claim tracked from the unpadded proof by Lagrange against the two claims times the bound quad.

### 3.4 Ligero_Prover: the tableau on the heap, the encoder, the opening

`Ligero_Prover` is generic over the Ligero verifier of chapter 5 (which carries the transcript glue, the proof record, the Lagrange tables and the geometry), over `Sampling` and over the encoder of chapter 8.

- **The commitment.** The `Commitment` record holds the tableau (a two-dimensional array of NROW by NCOL elements), the nonces and the Merkle heap, in one heap allocation under the ownership discipline of [ADR 0047](../adr/0047-heap-allocation-by-ownership.md). `Prover_Fits` says which geometries the prover handles: the proof fits, every column is an evaluation point, the double block fits the encoder, with the Lagrange encoder the parity columns fit a table of 4,096 columns, and the tableau fits 2^26 elements.
- **The encoder.** `Encode_Row` writes the systematic part, the row, and the parity part from the encoder; with the Lagrange encoder each parity column is `Lagrange.Evaluate`. Both are in its postcondition (chapter 8 Section 3.3).
- **The rows.** `Commit` builds the rows in three groups (`Fixed_Rows`, `Witness_Rows`, `Quad_Rows`), each row through `Commit_Row`, which encodes into a scratch buffer, a heap object of its own, and writes the tableau's row; its postcondition says that the row holds the encoding and the other rows are untouched. `Commit` asserts after each call what it needs of it.
- **The leaves.** `Hash_Leaves` draws the nonces, hashes the leaves and builds the heap.
- **The proof.** `Prove` is Section 1.5. It reuses `Draw_Challenges`, `Build_A_Full`, `Absorb_Polynomials` and `Choose_Columns` of the verifier, so that the two sides draw and absorb the same bytes by construction; it computes the four polynomials with `Axpy` and `Vaxpy` of chapter 5 on row buffers, opens the tree with `Merkle.Open` and copies the queried columns.

`Merkle.Open` lives in `Merkle` of chapter 5, with the digests only. Its postcondition is `Verify`'s model:

- the count of digests is `Missing_Before (0, N, Path_Flags (N, Indices))`, the number `Verify` consumes;
- for every node on a path, each child `Verify` reads, through the ghost `Child`, is the heap's node.

Two lemmas, `Lemma_Missing_Mono` and `Lemma_Reads_Below`, carry the fact that the positions already written are below the position being written.

### 3.5 The writers and their postconditions on the readers

`Proof_Writer` is generic over the Ligero verifier and writes the three parts of the proof string.

- `Write_Sumcheck_Proof` permutes the pad order of chapter 3 into the order of Section 7.3.
- `Write_Ligero_Proof` writes the fixed part, then the runs chosen by position (`Sub_Row`, `Lead_Rows`, `Sub_Rows`, `Trail_Rows`), then the path, at the reader's offset in the buffer. Its postcondition is that the bytes satisfy `Well_Coded` of chapter 5, the reader's own rules: that is how the writer is proved to produce what the reader accepts.
- `Write_Proof` composes them with the root, and its postcondition names the first 32 bytes.

The equality `Read (Write (P)) = P` is not a theorem the generics can state, because `To_Bytes` and `From_Bytes` are formals without contracts. It follows from the proved layouts and the byte-level facts of chapters 1 and 2, and it is tested on every proof of the repository, read and rewritten identical ([ADR 0052](../adr/0052-gold-perimeter-for-the-prover.md)).

### 3.6 The subfield projection as a fixed linear map

Section 7.4 writes a subfield element as two bytes: its coordinates on the basis of GF(2^16) in GF(2^128) that chapter 5 injects. The inverse of the injection on its image is linear over GF(2), so sixteen masks suffice: coordinate i is the parity of the element's low limb and the i-th mask (`GF2_128.Subfield_Mask`, `Parity`, `Subfield_Coords`).

- The masks are precomputed by Gaussian elimination in the generator, checked there on all 65,536 subfield elements, and tested in `gf2_128_kat` (register row V8).
- `In_Subfield` is the round trip through the injection.
- No linear system is solved at run time, and the projection costs the same on every element ([ADR 0051](../adr/0051-constant-time-in-the-prover.md)).
- The re-injection is branch free too: `GF2_128.Inject` selects each basis element with a mask built from the bit, as `Mul` does, because the prover applies it to the coordinates of private inputs.

`Field_Signature` has one formal for this, `To_Subfield_Bytes`, realised by the projection on GF(2^128) and by `To_Bytes` on P-256.

### 3.7 Zk_Prover, Prover_Status, longfellow_prove

`Zk_Prover` is generic over the Ligero prover, the packed kernels of `Packed_HQuad`, the sumcheck prover over the same transcript glue and those kernels, the writers, the evaluation of the packed circuit (`Packed_Eval`), and a Boolean `Validate` that only the test project sets to False.

It has the two phases of the reference as procedures of their own ([ADR 0085](../adr/0085-prover-and-verifier-in-two-phases.md)):

- **`Commit`** takes the private inputs. It checks their count and the subfield, draws the pads, forms the witness vector, builds the Ligero commitment and writes its root to the transcript as it is. It hands back a `Committed`, a private record that holds the commitment, the working set and the shape of the circuit on the heap; the second phase requires a circuit of that shape, since the pads and the triples are laid out by it.
- **`Prove_Committed`** takes the public inputs. It checks their count and the first input, evaluates the circuit on the public and the private inputs together and checks the satisfiability, writes the statement, runs the sumcheck, the core and the Ligero proof, writes the bytes and frees the record. `Release` frees the record without proving.
- **`Prove`** is the composition on a fresh transcript: the two checks on the inputs, `Reset` with the label, `Commit`, `Prove_Committed`.

The mDoc layer needs the phases apart: it commits both circuits, draws from the transcript the value the MACs use, builds the public inputs from it, and only then proves (chapter 9). The satisfiability check runs in the proving phase, since the circuit can be evaluated only once the public inputs exist.

`Prove` takes the label, the circuit identifier and subfield boundary of the file, the Ligero configuration, the packed circuit and the inputs. It fills a buffer of `Max_Proof_Len` bytes (the writer's length with the longest opening) with the proof of `Len` bytes, or reports a status of `Prover_Status`:

- `Input_Length`: the inputs are not ninput elements;
- `Input_Not_One`: the circuit has public inputs and the first is not 1 ([ADR 0064](../adr/0064-lean-circuit-premises.md));
- `Not_Satisfied`: `Packed_Eval.Eval_Circuit` says so;
- `Not_In_Subfield`: a witness the writer will project does not lie in GF(2^16). These are the witnesses of the rows wholly below the boundary (`Proof_Writer.Sub_Rows`), checked by projecting, re-injecting and comparing, with the differences accumulated in one mask over the bytes; never on P-256. The check follows the rows the writer projects: with WR 4 and boundary 4 no row is wholly below the boundary, nothing is projected, and the proof is valid;
- `Config_Invalid`: with the Lagrange encoder, a Lagrange denominator has no inverse. The caller checks beforehand that the prover handles the geometry (`Config_Fits`, which `Prover_Fits` decides), and the precondition requires it;
- `Exhausted`: the transcript's generator passed its bound ([ADR 0043](../adr/0043-exhausted-status-and-streaming-slice.md)).

The working set (pads, witness vector, triples, the padded proof, the challenges, the constraints, the Ligero proof record) is one heap allocation, freed on every path. The wires are not in it: `Allocate_Segs` of chapter 3 gives the array of null segments, `Packed_Eval.Eval_Circuit` fills it, the sumcheck prover frees each segment as its layer is proved, and `Release_Segs` frees the array and whatever an early exit leaves, on every path.

`longfellow_prove` (`cli/`, `SPARK_Mode (Off)`, register row C2):

- parses the command line, reads the circuit file and the inputs file in the format of upstream's test data: a JSON array of decimal strings; on GF(2^128) the integer's little-endian bytes are the element, on P-256 the integer is reduced modulo p, through `Ada.Numerics.Big_Numbers`;
- loads the circuit in its packed form, through `Pinned_Circuits.Read_Packed` as the verifier does (chapter 6, Section 3.6), and checks once, where the circuit enters the program, the executable part of what the prover asks of it: the indices of the form, its layers and its shape. The rest of the precondition, at the level `Proof_Only`, is the loader's postcondition;
- checks the configuration, selects the source and writes the proof file;
- exits with status 0 when the proof is written, 1 on a prover status, 2 on a usage or file error, like the verifier.

Its chain of generic formals is given in full, as the verifier's, so that the circuit the reader loads is the circuit the prover takes.

### 3.8 Constant time in the prover

[ADR 0051](../adr/0051-constant-time-in-the-prover.md) lists the units (register row S4).

Constant time by construction:

- `Sumcheck_Prover` loops over the terms of a layer, a public structure; it branches on the parity of a wire index, merges terms by comparing their wire indices and tests a term's constant against zero, all public;
- `Ligero_Prover` branches on positions, the geometry and the boundary, copies witnesses in fixed loops and multiplies them by public coefficients;
- the hashes run over fixed-length data;
- no inversion on a secret: the inverses are those of public Lagrange denominators.

Written with care: the run-length structure by position (Section 2.6) and the fixed projection (Section 3.6).

Two branches on witness-derived values, declared: the satisfiability check and the subfield check. Each is a fixed loop that accumulates its result without a branch on the values (a byte mask in the subfield check, a Boolean `and` on the comparison with zero in `Packed_Eval`), then one branch on the result, the prover's own decision whether to produce a proof. The binary of both was inspected on arm64 and x86-64.

Out of the perimeter, public: the transcript and its challenges, the circuit, the public inputs, the serialised proof, the opened columns and the path. The guarantee is scoped to builds with assertions disabled, as everywhere in this project ([ADR 0006](../adr/0006-constant-time-discipline-and-scope.md)).

## 4. What the proofs guarantee

### 4.1 The properties

For every input that meets the preconditions, GNATprove proves:

- No run-time error in any prover unit, for any circuit, inputs, configuration and byte stream, including the ownership checks on every heap object: no null or dangling dereference, every allocation freed on every path that does not return it, no aliasing.
- The lengths and offsets of the proof string: the writers write exactly `Proof_Len` bytes, the Ligero part satisfies `Well_Coded` at the reader's offset, the first 32 bytes are the root.
- The bound quad that `Prove` returns for each layer equals the verifier's reference `BQ_Ref` on the ghost expansion of the packed circuit (ADR 0071, ADR 0080).
- `Packed_Eval.Eval_Circuit` computes, from the packed circuit, the wires the expanded `Eval_Circuit` computes, one heap segment per layer: every segment is the quad sum of the next (`Layer_Holds_Seg` on the expansion), the last segment is the inputs, every segment has the size of its layer (`Segs_Shape`), and the status is "all assertions hold and every output wire is zero" (`Packed_Eval`, proved in the partition `packed_hquad`).
- The round evaluations equal the ghost transcription of `eval_round_poly` in its dense form (`QW_Ref`, `D0_Ref`), and the evaluation at P2 equals `D2_Ref` when the claim of the round is the true sum, which the honest prover's is: the claim itself is tested (ADR 0075).
- The systematic part of every encoded row is the row; with the Lagrange encoder the parity part is `Lagrange.Evaluate` (chapter 8 for the FFTs, register row V2). Each row of the tableau receives its encoding and the other rows are untouched; the witness slots of each unencoded row hold the witnesses, the triples' values or zeros, as Section 1.4 says; the witness slots of row 2 are zero.
- The opening is the one `Merkle.Verify` consumes, in its model; the triples are the core's.
- The pad layout: `Witness_Count (C)` is the private inputs plus `Pad_Total (C)` (`Lemma_Pad_Shift`), and every triple lies below it.

What the proofs do not say, and is tested:

- that the composition of the row shapes over the whole tableau holds as one postcondition of `Commit`: proved row by row, tested slot by slot ([ADR 0052](../adr/0052-gold-perimeter-for-the-prover.md));
- that the four polynomials of the Ligero proof are the reference's sums;
- that the verifier accepts the proof, the completeness (register row V6).

### 4.2 The verification conditions

The proof of the units of this chapter, from a run of the partitions `prover`, `ligero-prover` and `packed_hquad` ([B6.5](00-primer-spark.md#b65-partitions-and-the-whole)) on the proving machine; the two encoders of `ligero-prover` are counted in chapter 8 and the kernels of `packed_hquad` in chapter 3:

- **commit** 7221059 (main) for `prover` and 4f1e104 (main) for `ligero-prover` and `packed_hquad`, with the same proof inputs `be44efe9bc9d` (`scripts/remote-check.sh --digest`);
- **toolchain** GNATprove 16.1.0 with gnat_native 16.1.0 (Alire); the prover configuration of `package Prove` in the project file, CVC5, Z3 and Alt-Ergo with `--steps=600000` and `--timeout=120` ([ADR 0020](../adr/0020-prover-configuration-step-budget.md));
- **command** `make prove-partition PARTITION=<name>` for each of the three;
- **run** 15 November 2026, on the proving machine, one partition at a time from a clean session: proved, not reused from an earlier proof.

How to read the tables: [B6.4](00-primer-spark.md#b64-reading-the-summary-table). In the columns with two counts, the GF(2^128) instance comes first, then the P-256 one; the P-256 instances carry the canonical-form predicate of their elements.

**The partition `prover`.**

| Check | `Proof_Writer_*` | `Sumcheck_Prover_*` | `Sampling_*` | `Simple_Rng` | `Prover_Status` | Discharged by |
|---|---|---|---|---|---|---|
| Data dependencies (`Global`) | 25 / 25 | 34 / 34 | 0 / 0 | 2 | 0 | flow analysis |
| Flow dependencies (`Depends`) | 0 / 0 | 0 / 0 | 0 / 0 | 1 | 0 | flow analysis |
| Initialisation | 8 / 8 | 44 / 44 | 5 / 7 | 2 | 0 | flow analysis |
| Termination | 10 / 10 | 14 / 11 | 2 / 0 | 0 | 0 | flow analysis |
| Range checks | 37 / 37 | 396 / 396 | 0 / 0 | 1 | 0 | provers |
| Division checks (`/`, `mod`) | 2 / 2 | 26 / 26 | 0 / 0 | 0 | 0 | provers |
| Overflow checks | 201 / 201 | 286 / 286 | 0 / 0 | 0 | 0 | provers |
| Index checks | 60 / 60 | 151 / 151 | 0 / 0 | 0 | 0 | provers |
| Length checks | 10 / 10 | 7 / 7 | 0 / 0 | 0 | 0 | provers |
| Discriminant checks | 0 / 0 | 2 / 2 | 0 / 0 | 0 | 0 | provers |
| Null dereferences | 0 / 0 | 50 / 50 | 0 / 0 | 0 | 0 | provers |
| Type predicates | 16 / 28 | 95 / 270 | 0 / 4 | 0 | 0 | provers |
| Preconditions of the calls | 111 / 111 | 320 / 320 | 2 / 2 | 0 | 0 | provers |
| Assertions | 19 / 19 | 24 / 24 | 0 / 0 | 0 | 0 | provers |
| Loop invariants (base case and preservation) | 42 / 42 | 58 / 58 | 0 / 0 | 0 | 0 | provers |
| Postconditions | 16 / 16 | 22 / 22 | 0 / 0 | 0 | 0 | provers |
| Variants of the recursive functions | 1 / 1 | 13 / 13 | 0 / 0 | 0 | 0 | provers |
| Memory leaks (an allocation freed) | 0 / 0 | 8 / 8 | 0 / 0 | 0 | 0 | provers |
| **Total** | **558 / 570** | **1550 / 1722** | **9 / 13** | **6** | **0** | all proved: none justified, none unproved, no `pragma Assume` |

`Prover_Status` declares only the list of statuses and has no check.

**The partition `ligero-prover`, the units of this chapter.**

| Check | `Ligero_Prover_*` | `Zk_Prover_*` | Discharged by |
|---|---|---|---|
| Data dependencies (`Global`) | 17 / 17 | 9 / 9 | flow analysis |
| Initialisation | 13 / 13 | 20 / 20 | flow analysis |
| Non-aliasing | 13 / 13 | 22 / 22 | flow analysis |
| Termination | 14 / 8 | 10 / 10 | flow analysis |
| Range checks | 189 / 189 | 108 / 108 | provers |
| Division checks (`/`, `mod`) | 4 / 4 | 6 / 6 | provers |
| Overflow checks | 120 / 120 | 33 / 33 | provers |
| Index checks | 117 / 117 | 19 / 19 | provers |
| Length checks | 44 / 44 | 20 / 20 | provers |
| Discriminant checks | 6 / 6 | 5 / 5 | provers |
| Null dereferences | 117 / 117 | 86 / 86 | provers |
| Type predicates | 13 / 63 | 40 / 57 | provers |
| Preconditions of the calls | 63 / 63 | 68 / 68 | provers |
| Assertions | 8 / 8 | 12 / 12 | provers |
| Loop invariants (base case and preservation) | 20 / 20 | 0 / 0 | provers |
| Postconditions | 17 / 17 | 7 / 7 | provers |
| Variants of the recursive functions | 0 / 0 | 1 / 1 | provers |
| Memory leaks (an allocation freed) | 12 / 12 | 15 / 15 | provers |
| **Total** | **787 / 831** | **481 / 498** | all proved: none justified, none unproved, no `pragma Assume` |

**The partition `packed_hquad`, the unit of this chapter.**

| Check | `Packed_Eval_*` | Discharged by |
|---|---|---|
| Data dependencies (`Global`) | 11 / 11 | flow analysis |
| Initialisation | 5 / 5 | flow analysis |
| Termination | 3 / 3 | flow analysis |
| Range checks | 42 / 42 | provers |
| Overflow checks | 50 / 50 | provers |
| Index checks | 78 / 78 | provers |
| Length checks | 1 / 1 | provers |
| Null dereferences | 27 / 27 | provers |
| Type predicates | 11 / 14 | provers |
| Preconditions of the calls | 91 / 91 | provers |
| Assertions | 19 / 19 | provers |
| Loop invariants (base case and preservation) | 26 / 26 | provers |
| Postconditions | 8 / 8 | provers |
| Memory leaks (an allocation freed) | 3 / 3 | provers |
| **Total** | **375 / 378** | all proved: none justified, none unproved, no `pragma Assume` |

In all, 4,428 checks in `prover` and 3,535 in `ligero-prover`, of which 938 are the two encoders of chapter 8; `Packed_Eval` has 753 of the 2,397 of `packed_hquad`. The flow analysis also prints warnings, which are not checks and are not counted in the tables. Their counts, as `vc-count.py` prints them: `Sampling_GF2_128` 4 and `Sampling_P256` 2 in `prover`; `Ligero_Prover` 5 and 5, `Zk_Prover` 6 and 6 in `ligero-prover`; none in `Packed_Eval`.

In plain terms, for every input, not on samples:

- no run-time error occurs in the prover, on any circuit, any inputs and any byte stream of the source;
- the proof string has the layout the reader of chapter 5 accepts;
- the bound quads the prover hands to the core are the verifier's;
- every row of the tableau holds its encoding, and every allocation is freed or returned.

Reproduce with:

```bash
make prove-partition PARTITION=prover
python3 -I scripts/vc-count.py --partition prover
make prove-partition PARTITION=ligero-prover
python3 -I scripts/vc-count.py --partition ligero-prover ligero_prover_gf2_128 ligero_prover_p256 zk_prover_gf2_128 zk_prover_p256
make prove-partition PARTITION=packed_hquad
python3 -I scripts/vc-count.py --partition packed_hquad packed_eval_gf2_128 packed_eval_p256
```

Each `make` command proves one partition and prints GNATprove's summary; run the `python3` command after it, before the next `make` cleans the files. The `python3` command checks that the files are those of a run of that partition and that its units add up to the summary, then prints the table from the files GNATprove writes for each unit (`obj/development/gnatprove/<unit>.spark`) and says whether any check is unproved or justified or any unit has a `pragma Assume`. The lessons of these proofs are in the verification approach, "Lessons of the proofs".

## 5. What is only tested

### 5.1 Tier 1: the two upstream proofs reproduced byte for byte

The `cli` step of `make check` runs `longfellow_prove` on the two upstream circuits and compares the files with upstream's proofs with `cmp`:

- `sha256_circuit.lfc2` with `sha256_inputs.json`, label `sha256_spec_test`, rate 3, 16 queries, 256 columns and `--seed 12345`, against `sha256_proof.bin` (49,936 bytes);
- `ecdsa2` with `ecdsa2_inputs.json`, `ecdsa2_spec_test`, rate 4, 16, 256 and `--seed 123456789`, against `ecdsa2_proof.bin` (56,268 bytes).

Both are identical. This is the exit criterion of the prover ([ADR 0049](../adr/0049-phase-c-scope-the-prover.md)): every byte the reference prover writes, from the same inputs and the same generator, this prover writes, which tests the order of every draw, every absorption and every write.

The parts are tested the same way:

- the writers rewrite every proof of the repository identical (`writer.txt`, `writer_kat`);
- the Merkle roots of the two upstream proofs are reproduced from the inputs and seeds by `Commit` alone (`ligero_commit.txt`, `prover_kat`).

`writer_kat` prints:

```
checks by section:
  tests/vectors/writer.txt: passed 4, failed 0
passed 4, failed 0
```

### 5.2 Tier 2: the independent Python references

`gen_prover_vectors.py` transcribes the reference prover piece by piece, sharing no code with the Ada:

- `SimpleRng`, the samplers, the pads, `eval_round_poly`, `round_poly`, `bind` and the term update: `sumcheck_prover.txt`, five cases on the Appendix B.3 circuits and the circuit with an assertion of chapter 3, the pads and the padded proof of Section 7.3 byte for byte;
- `layout_tableau`, `commit_merkle_heap` and `open_merkle_heap`, with the Lagrange matrix of `gen_ligero_vectors.py`: `ligero_commit.txt`, six commitments (the root, every unencoded row against the systematic part of the tableau, one batch opening equal to the reference's and accepted by `Merkle.Verify`, one case with a subfield boundary that exercises the subfield sampler) and the two roots of the upstream proofs.

The subfield projection's masks are derived in `gen_gf2_128_vectors.py` and checked on all 65,536 subfield elements (`gf2_128_kat`, chapter 1).

The complete reference prover is not written: the constraints of the Ligero proof come from the symbolic core, which the generators do not transcribe ([ADR 0053](../adr/0053-prover-vectors-and-cross-verification.md)). Tier 1 and completeness cover the composition.

### 5.3 Completeness, other seeds, the negative cases

Completeness (register row V6):

- `prover_kat` runs `Zk_Prover.Prove` on the small circuits with chosen seeds, and `Zk_Verifier` must accept each proof (`zk_prove.txt`, eight proofs of 2,568 to 5,580 bytes). For each, two proofs on one transcript are accepted, with the same bytes drawn on both sides, and the altered second proof, a short buffer and wrong public inputs are refused.
- On `sha256` and `ecdsa2`, the `cli` step proves under another seed and under the system source, and `longfellow_verify` accepts.
- The same step runs `scripts/measure-mdoc.sh` once, with the default 8 MB stack, so that the four production mDoc circuits are proved from upstream's witnesses and every proof is accepted inside `make check`.

The negative cases of `zk_prove.txt`:

- `input_length`;
- `input_not_one`, on two circuits;
- `not_satisfied`, on three circuits, one through an assertion;
- `not_in_subfield`: boundary 4 with WR 2, where the first witness row is projected and 0x6c is not in GF(2^16); boundary 4 with WR 4 is `ok`, since nothing is projected;
- `config_invalid`, on both fields: 70,000 columns at inverse rate 2, beyond the 2^16 points every encoded row may use (`Ligero_Geometry.Max_Encoded_Len`), a configuration that `Valid` refuses, checked by the harness as a caller must, before `Config_Fits` is asked. No vector reaches the prover's own status `Config_Invalid`, which only the Lagrange encoder can return.

For each refused case that has a proof to refuse, the prover instance with `Validate => False` produces a proof that `Zk_Verifier` refuses: `linear_sum_failed` for the unsatisfied circuits, `merkle_failed` for the projected element.

`prover_kat` prints:

```
checks by section:
  tests/vectors/sumcheck_prover.txt: passed 5, failed 0
  tests/vectors/ligero_commit.txt: passed 8, failed 0
    commit: passed 6, failed 0
    root: passed 2, failed 0
  tests/vectors/zk_prove.txt: passed 17, failed 0
passed 30, failed 0
```

`verify_proof_file.rs` under `tests/vectors/upstream/` verifies a proof file of this project with upstream's `ZkVerifier`. The author runs it with `cargo` on the two files the `cli` step leaves under `cli/out/`, outside the gate, as the README there says.

### 5.4 Times and memory

The times and the peaks of the prover, and their comparison with upstream's, are on [the performance page](performance.md). Per `Commitment` on the heap, the tableau of `sha256` (213 rows of 256 elements of 16 bytes) takes 872 KB, that of `ecdsa2` (65 rows of 32 bytes) 532 KB, with 10 and 11 KB of heap and nonces.

## 6. What stays trusted, and the limits

- The operating system's generator, for the zero knowledge of the proofs `longfellow_prove` and `longfellow_prove_mdoc` make without `--seed` (register rows C1 and P4). A proof made with `--seed` is reproducible and predictable, by design, for tests.
- That `Simple_Rng` is upstream's test generator (register row R7), transcribed and confirmed by the byte identity, and that upstream's proofs are the ones its test asserts.
- The zero-knowledge and completeness theorems of the padded sumcheck and of Ligero (register row S1); the completeness of this prover is tested (register row V6).
- The termination of the rejection samplers (register row V4).
- The subfield projection beyond the tested elements (register row V8).
- The constant-time discipline, by review against the list of ADR 0051, in builds with assertions disabled (register row S4).
- Enough memory, and aggregate allocation in place (register rows P1 and P2): the supported scale is the available memory for one circuit, the wires, the tableau and the working set.
- The fixed statement hash of the reference (register row R6).
- The command-line program, outside SPARK (register row C2).
