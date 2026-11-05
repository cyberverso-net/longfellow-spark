# 0080 A memory milestone, before the certification block and M3

## Status

Proposed (2026-10-29, after milestone M2 of Phase D). Amended 2026-10-30 by [ADR 0082](0082-order-after-the-memory-milestone.md): the order after this milestone is the mDoc layer, the guide, the certification block, then M3.

## Date

2026-10-29

## Context

At the close of M2 ([ADR 0078](0078-milestone-m2-closed.md)) the peak heap was far above upstream's, by the same measure: the bytes allocated at the peak of each process.

- **The measure.** Ours is counted by a malloc interposer loaded with `LD_PRELOAD`, upstream's by the same interposer on one v2 proof or one verification of its bench's flow. Upstream's own tracking allocator gives figures within 7 % of it (104 and 45 MB).
- **The peaks, main at 88835f2:**

  | | this project | upstream (both circuits in one process) |
  |---|---|---|
  | prover | hash 645 MB, signature 78 MB | 107 MB |
  | verifier | hash 515 MB, signature 44 MB | 48 MB |

- **Where it goes** (the notes of 29 October, the large blocks live at the peak with their allocation stacks):
  - the hash circuit in memory: 236.7 MB in both programs, 7.76 million terms of 32 bytes. Upstream holds both circuits in about 3 MB;
  - in the verifier, two copies of the terms of the largest layer (114 MB each), one of them a function result passed to `Bind_Quad`;
  - in the prover, the wires of every layer (109 MB), a working copy of the layer and its vectors (155 MB);
  - in the command-line prover, a provisional list of 2^20 inputs (16 MB) never freed.
- **Why upstream's circuit is small.** The LFC2 file names each repeated block of a layer once: a dictionary of term deltas, segments of dictionary indices, and a sequence of segments. Upstream keeps that form in memory and rebuilds the terms on the fly. This project expands it.
- The prover runs on the holder's phone, so its memory is felt by users. Memory is not a trade of trust for speed: the work is Gold, like M2.

## Decision

**A memory milestone, in Gold, before the certification block and M3.**

- **The criterion:** the peak heap within twice upstream's, by the same measure, on the mDoc v7 circuits, for the prover and the verifier.
- **First step, without a format change** (this record):
  - the verifier passes a layer's terms to `Bind_Quad` as a slice of the circuit, by reference;
  - the command-line prover frees the provisional list of inputs, the inputs file and the decimal strings once converted.
- **Next, the circuit's representation**, each step with its own record:
  - B: the circuit held compressed, as the file holds it, and one layer expanded at a time into a term array proved equal to the layer of a ghost expansion. The kernels and their Gold references stay as they are;
  - C: in the expanded layer, the constant of a term as an index into the circuit's constants, if the criterion asks for it;
  - then the prover's wires.
- **Not taken:** the kernels reading the compressed form directly, as upstream does. That rewrites the proof of every kernel, for 15 to 20 MB more in the verifier.

## Alternatives considered

- **Leave memory to M3.** Rejected: changing the circuit's representation after M3 means two builds to adapt, and the certification documents would describe structures about to change.
- **A ceiling in absolute terms** (ADR 0055 set 1 GB, which every run keeps). Kept, but it says nothing about the gap with upstream.

## Consequences

- The first step, measured on the proving machine, main 88835f2 against 4940221, peak heap:

  | | before | after | change |
  |---|---|---|---|
  | hash prove | 645 MB | 621 MB | -24 MB |
  | hash verify | 515 MB | 401 MB | -114 MB (-22 %) |
  | signature prove | 78 MB | 60 MB | -17 MB |
  | signature verify | 44 MB | 36 MB | -8 MB |

  The proofs of the command line stay identical byte for byte. The memory still allocated at the end of the verifier falls from 116 MB to 1.4 MB: it was the copy of the layer.
- The performance page records the measure and the peaks. The tools stay with the notes: the interposer, the profiler, and the per-layer statistics of the circuit files.
- Block 1, the packed form:
  - `Packed_Circuits` and `Read_Packed` keep a circuit as its file keeps it, proved on the ghost expansion (chapter 6, Section 3.7);
  - on the mDoc hash circuit the form takes 4.2 MB (4,366,352 bytes), against 236.7 MB expanded. The estimate was about 3 MB: the deltas keep their three fields as 64-bit integers, 32 bytes a delta, where the estimate counted 4 bytes a field;
  - the peak heap is unchanged, since the consumers still expand the circuit;
  - `Read_Packed` bounds what it keeps over the whole circuit: deltas, segments, segment entries and kept tokens, each at most `Max_Terms` (2^28), with `Bound_Exceeded` beyond. `Read` bounds only the terms, upstream each layer, so a file of more than 256 MB with large unused segments loads with `Read` and not with `Read_Packed`. Chapter 6, Section 1.5, records it beside the bounds of ADR 0046.
- Block 2, the first step of a layer from the packed form (chapter 3, Section 3.5). This block departs from "Not taken" above in one bounded way: the first step of a layer, bind g and the merge of the runs, reads the packed form directly, as upstream's `bind_g`, because it is the step that decides the size of the working array; the rounds, `Bind_H`, keep their kernels and proofs.
  - `Packed_HQuad` walks a layer, binds each term with g and merges it into the run of its hands as it comes: `Layer_Runs`, `Bind_Merge`, `Bind_Quad_Packed`, `Eval_Bound_Quad_Packed`. The working array has one entry per run of equal hands: on the largest layer of the mDoc hash circuit 439,013 entries (14.0 MB) where the expanded layer holds 3,578,789 terms (114.5 MB); the largest working array, on the layer of 1,429,054 terms, holds 1,153,333 entries (36.9 MB against 45.7 MB). The time of the two paths is measured by `first_step_bench` in the release build (chapter 3, Section 3.5).
  - Every result is stated on the layer of the ghost expansion, as the kernels of `Sumcheck_HQuad` state theirs on an expanded layer, so the invariant of the rounds (with the eq2 table; without it `Bind_Merge`, like `Merge_Terms`, states the run count only) and the references `EBQT_Ref` and `EBQ_Ref` are reached unchanged.
  - The verifier and the prover still take the expanded circuit, so the peak heap is unchanged; block 3 makes them take the packed form and measures it.
  - `Bind_Step_Packed`, the rounds on the packed path, is a copy of `Bind_Step` with the ghost layer in its contract, kept until block 3 removes the expanded path.
- Block 3, first part (3a), the verifier on the packed form (chapter 3, Section 3.5; chapter 6, Section 3.7).
  - The sizes come from the shape of the circuit, `Shape` of `Sumcheck_Algebra` (the header and the layer table, with `Shape_Ok` as its predicate); the subprograms that read no term take it in place of the circuit, the ghost references keep the circuit and are stated on the expansion `Expand (P)` on the packed path.
  - `Zk_Verifier.Verify` takes the packed circuit: the shape once, the bound quads from the walk with the kernels of block 2 (`Bound_Quads`, Gold against `BQ_Ref` on the expansion), the core on the shape. `Verifier_Core` takes the shape; the fact that the bound quads it receives are those of the challenges lives in the postconditions of their producers and in `Proof_Only` assertions at its two calls. The command-line verifier loads with `Read_Packed`; `Read` stays as the prover's loader and the oracle of the tests. `Pack`, Gold, packs the hand-built circuits of the tests.
  - Peak heap on the proving machine, one session, the counter of the first step on both sides (upstream's `heap_v7` verification of the mDoc v7 flow, generic code, baseline CPU):

    | | before (main 7946d77) | after (3a) | upstream (both circuits) |
    |---|---|---|---|
    | hash verify | 401 MB | 79 MB | 48 MB |
    | signature verify | 36 MB | 11 MB | |

    The verifier is within the criterion of the milestone, 1.6 times upstream's peak for both circuits on the hash circuit alone (from 8.3 times). The proofs of the command line stay identical byte for byte. The prover's peak is unchanged until the second part of the block.
- Block 3, second part (3b), the prover on the packed form and the expanded path removed (chapter 7, Sections 2.1, 3.3 and 3.7; chapter 3, Section 3.5).
  - `Packed_Eval` evaluates the circuit from the walk, Gold on the expansion against the references of the expanded `Eval_Circuit`; `Sumcheck_Prover` is generic over `Packed_HQuad` and `Prove_Layer` fills its working array, one entry per run of equal hands, with `Bind_Merge`; `Zk_Prover.Prove` takes the packed circuit, and `longfellow_prove` loads with `Read_Packed` as the verifier does.
  - The expanded path leaves the executable code: `Bind_Quad` and `Bind_Step` of `Sumcheck_HQuad` and `Bound_Quads` of `Sumcheck_Verifier` are removed, `Bind_Step` of `Packed_HQuad` is the one left (ADR 0073 and ADR 0071, Status notes). `Read`, `Read_Pinned`, the expanded `Eval_Circuit`, `Bind_G_T`, `Merge_Runs`, `Merge_Terms` and `Eval_Bound_Quad` stay proved as the oracles of the harnesses. `first_step_bench --check` compares the packed first step with the exact `Eval_Bound_Quad` on every layer of the two mDoc version 7 circuits inside `make check`.
  - Peak heap on the proving machine, one session, three runs each, upstream's prover and verifier under the same counter in the same session: the prover on the mDoc hash circuit 621 MB to 226 MB, on the signature circuit 60 MB to 27 MB (upstream 107 MB for both circuits in one process; the hash proof 2.1 times upstream, from 5.8); the verifier unchanged at 79 MB and 11 MB (upstream 48 MB). The round trip does not move (hash proof 5.01 s, verification 2.43 s); the proofs are identical byte for byte. The largest object allocated for a layer is now the working array of the rounds, 36.9 MB on the hash circuit, freed with the layer; the prover's wires are the next item (#60, #61).
- Block 4, first part (4a), the prover's wires one heap segment per layer (chapter 7, Sections 2.1, 3.3 and 3.7; chapter 3, Section 2.2).
  - The profile of #60 (3 November, main against upstream at d5e6be7, one session): at the peak of the hash proof, layer 13, ours held the wires of every layer (55.2 MB, one buffer in the work record of `Zk_Prover`) where upstream holds those of the layers still to prove (28.6 MB, `prove_core` takes and drops each layer's vector); the five working vectors of the rounds 72.2 MB against upstream's 21.7; the merged terms 36.9 MB against 27.7; the two eq2 tables alive inside `Eq2_Table` 33.6 MB against none. The four items explain the 119 MB between the peaks (226 against 107).
  - `Packed_Eval.Eval_Circuit` fills one heap segment per layer (`Seg_Array` of `Sumcheck_Algebra`), `Sumcheck_Prover.Prove` frees the segment of a layer once the layer is proved, segment 0 first, and `Zk_Prover.Prove` allocates the array and releases what is left on every path. The working vectors of the rounds are the second part of the block; the eq2 table its own issue.
  - The declarations the block adds to `Sumcheck_Algebra` enter the context of every verification condition of the instances of `Sumcheck_HQuad`, a generic over the algebra: the proof of `Lemma_Bind_H_Step` on P-256, the hardest of the project at 83 % of the step budget (#92), no longer closed within it at the gate. With the maintainer's agreement its body was split, the sums unfolded one step at a time by the existing `Lemma_W_Step` in place of the whole definition of `W_Sum`; its contract, the prover settings and the budget are unchanged. The verification-approach page states the rule this taught.
- Block 4, second part (4b), the working vectors of the rounds in upstream's form (chapter 7, Sections 2.3 and 3.3; chapter 3, Section 3.4).
  - The two hands share the wire segment of the layer until the first binding separates them: hand 1 is the segment, bound in place; hand 0 is bound out of place at round 0 into a vector of half the width, then in place; one accumulator for the round polynomial. `Bind_In_Place`, the in-place form of `Bind`, is the one kernel added, Gold against the same reference. Five vectors of the layer's width beside the segment become one and a half.
  - Peak heap on the proving machine, one session, three runs each, upstream's prover under the same counter in the same session: the prover on the mDoc hash circuit 199 MB to 142 MB (the five vectors of layer 13, 72 MB, become the accumulator alone at the peak, 14 MB), 1.32 times upstream's 107 MB for both circuits in one process, from 1.86, and 66 % of the criterion of 214 MB; on the signature circuit 23 MB to 20 MB. The verifier unchanged at 79 MB and 11 MB. The hash proof 4.87 s from 4.96 s (no copy of the wires per hand), the verification 2.43 s; the proofs identical byte for byte. What remains above upstream at the peak is the two eq2 tables alive inside `Eq2_Table` (#105) and the 32-byte run entry of the merged terms.
- The eq2 table in one array (#105; chapter 3, Section 3.3).
  - `Eq2_Table` fills its table by upstream's recursion (`fill_recursive` of `eq.rs`): the table split at its high bit, the weights of the two challenges multiplied by the factor of that bit and carried down, a table of one entry the sum of the two weights. No second table. Upstream also stops at the number of wires of the layer where this project fills the whole power of two; that changes the contract of `Eq2_Table` and is left to the close of the milestone (#64), with the run entry of the merged terms (#110).
  - Peak heap on the proving machine, one session, three runs each, upstream's prover and verifier under the same counter in the same session: the prover on the mDoc hash circuit 142 MB to 125 MB, 1.17 times upstream's 107 MB, from 1.32, and 58 % of the criterion of 214 MB; the verifier on the hash circuit 79 MB to 62 MB, 1.30 times upstream's 48 MB, from 1.64; both fall by the second table of layer 13 (2^20 entries of 16 bytes, 16.8 MB). On the signature circuit the verifier 11 MB to 9.5 MB, the prover unchanged at 20 MB. Times unchanged (hash proof 4.56 s, verification 2.28 s); the proofs identical byte for byte.
  - Peak heap on the proving machine, one session, three runs each, upstream's prover under the same counter in the same session: the prover on the mDoc hash circuit 226 MB to 199 MB (the wires of layers 0 to 12, 26.7 MB, freed before layer 13), under the criterion of 214 MB; on the signature circuit 27 MB to 23 MB; upstream 107 MB for both circuits in one process, the hash proof 1.86 times it, from 2.11. The verifier unchanged at 79 MB and 11 MB. The round trip does not move (hash proof 5.02 s before and after, verification 2.45 s); the proofs are identical byte for byte.

## Verification impact

- No contract changes. The slice is the value `Layer_Terms` returned; the protocol partition is proved (6238 checks).
- The command-line prover is outside the proof perimeter (SPARK_Mode Off).
- Block 2: the ghost postconditions of `Lemma_Term_Of`, `Expand` and `Lemma_Walked_Step` in `Packed_Circuits` gain `Same` on the coefficient of each term, beside the equality they stated. An addition: on GF(2^128) the predefined equality of an element is pointwise and gives no congruence through the field operations, so the coefficient could not be carried from the walk to the model (chapter 3, Section 4.1). The `circuits` partition is proved again (3,436 checks, 3,374 at the close of block 1); the new partition `packed_hquad` holds 1,644 checks. Prover settings unchanged.
- Block 3, first part: `Verifier_Core` takes the shape of the circuit, and its `Proof_Only` precondition on the bound quads moves to the postconditions of `Zk_Verifier.Bound_Quads` and `Sumcheck_Prover.Prove` and to `Proof_Only` assertions at the two calls; its own postcondition, and those of `Zk_Verifier.Verify` and `Zk_Prover.Prove`, are unchanged. New Gold contracts: `Shape_Of (P)` with `Lemma_Shape_Of`, `Pack`, `Zk_Verifier.Bound_Quads`. `Zk_Verifier.Verify` asks of the circuit, at level `Proof_Only`, the loader's postcondition. No contract weakened, prover settings unchanged. The `circuits` partition holds 4,557 checks (3,436 at the close of block 2: `Pack` and its lemmas), the `verifier` partition 2,542 (1,945 at the close of Phase B), all proved.
- Block 3, second part: `Sumcheck_Prover.Prove` and `Zk_Prover.Prove` take the packed circuit; their postconditions are restated on the expansion `Exp (P)` and with `P.Ninput`, `P.Npublic`, at their current levels, and both ask of the circuit, at level `Proof_Only`, the loader's postcondition. New Gold contracts: `Packed_Eval.Eval_Layer` and `Eval_Circuit`. Removed, with the expanded path: `Bind_Quad`, `Bind_Step`, `Sumcheck_Verifier.Bound_Quads`. The lemmas of the expanded `Eval_Circuit` move from the body to the spec of `Sumcheck_Algebra`, and `Lemma_Chal_Off_Eq` from the body of `Zk_Verifier` to the spec of `Sumcheck_Verifier`, unchanged. One addition: `Shape_Of (P)` of `Packed_Eval`, `Sumcheck_Prover` and `Zk_Prover`, and the executable preconditions of `Eval_Circuit`, `Sumcheck_Prover.Prove` and `Zk_Prover.Prove`, state the part of the loader's postcondition that the command line checks where the circuit enters the program (ADR 0072): `Indices_Ok`, `Layers_Ok` and `Shape_Ok` of the shape. No contract weakened, prover settings unchanged. The `prover` partition holds 4,419 checks (4,160 at the close of the first part), the `packed_hquad` partition 2,458 at its last run on its own (1,644 at the close of block 2), the whole project 32,657 at the gate of the block (32,037 at the close of the first part), all proved.
- Block 4, first part: `Packed_Eval.Eval_Circuit` takes the array of segments in place of the single buffer; its postcondition is restated layer by layer on the segments (`Layer_Holds_Seg`, `Layer_Z_Seg`, the references of the expanded evaluation read at base 0), with `Segs_Shape` (every segment at its size) added, at its current level; nothing of the single-buffer form is lost, each fact has its per-segment twin. `Sumcheck_Prover.Prove` takes the segments (`Segs_Shape` in its precondition) and leaves every one null (`Segs_Null` in its postcondition); `Prove_Layer` asks for the segment it reads; the postconditions on the bound quads are unchanged. `Zk_Prover.Prove` is unchanged in its contract. New Gold contracts: `Allocate_Segs`, `Release_Segs`, `Lemma_Layer_Seg_Intro`. Removed with the buffer: `Lemma_Layer_Done` and `Lemma_Off_Eq` of `Packed_Eval`, `Lemma_Segment` of `Sumcheck_Prover`, `Lemma_Wires_Cover` of `Zk_Prover`. No contract weakened, prover settings unchanged. The `packed_hquad` partition holds 2,396 checks (2,458 at the close of block 3), the `prover` partition 4,449 (4,419), the `protocol` partition 5,901 with the proof of `Lemma_Bind_H_Step` split (its postcondition on P-256 from 499,341 steps by Z3 alone to 2,942 by Z3, 685 by CVC5 and 87,210 by Alt-Ergo, three provers where there was one), the whole project 32,774 at the gate of the block (32,657 at the close of block 3), all proved; most steps 463,202, unchanged.
- Block 4, second part: `Bind_In_Place` added to `Sumcheck_Algebra`, Gold against the reference of `Bind` on the vector as it came, with the frame of the entries beyond the bound prefix; `Segs_From`, the state of the array of segments relative to the shape (the segments below a layer null, the others at their size), executable, in the precondition and postcondition of `Prove_Layer`, which now takes the array `in out` and binds the segment of its layer in place; `Bind_Hand` removed; the postconditions on the bound quads unchanged. One kernel added, none changed: the one divergence from the proof obligations of #61 as written, agreed by the maintainer. No contract weakened, prover settings unchanged. The `sumcheck` partition holds 3,616 checks, the `prover` partition 4,428 (4,449 at the close of the first part), the whole project 32,861 at the gate of the block (32,774 at the close of the first part), all proved; most steps 463,202, unchanged.
- The eq2 table (#105): the contract of `Eq2_Table` is unchanged. Its body calls `Fill`, a recursive procedure of the body of `Sumcheck_Algebra` with a `Proof_Only` postcondition (each entry of its block is the weighted sum of the two references, the entries outside it untouched) and a `Subprogram_Variant` on L, which proves the recursion terminates; the lemmas that join the two halves (`Lemma_Peel`, `Lemma_Fill_Step`) are ghost, in the same body. The spec gains only a note in its header, so the context of every other unit is unchanged. No contract weakened, prover settings unchanged. The `sumcheck` partition holds 4,015 checks (3,616 at the close of block 4), all proved at the first attempt, most steps 120,845.

## References

- [ADR 0055](0055-phase-d-scope-mdoc-scale.md), [ADR 0067](0067-performance-milestones-by-trust.md), [ADR 0073](0073-verifier-binds-the-quad-as-upstream.md), [ADR 0078](0078-milestone-m2-closed.md).
- longfellow-zk/longfellow-zk at d5e6be7: `rust/core/proto/src/layer.rs` (`Layer`, `for_each_term`), `rust/core/proto/src/reader/lfc2.rs`.
- The notes of 29 October: `experiments/2026-10-29-heap`, `2026-10-29-heap-profile`, `2026-10-29-circuit-forms`, and the decision note on the circuit's representation.
