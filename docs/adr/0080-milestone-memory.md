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

## Verification impact

- No contract changes. The slice is the value `Layer_Terms` returned; the protocol partition is proved (6238 checks).
- The command-line prover is outside the proof perimeter (SPARK_Mode Off).

## References

- [ADR 0055](0055-phase-d-scope-mdoc-scale.md), [ADR 0067](0067-performance-milestones-by-trust.md), [ADR 0073](0073-verifier-binds-the-quad-as-upstream.md), [ADR 0078](0078-milestone-m2-closed.md).
- longfellow-zk/longfellow-zk at d5e6be7: `rust/core/proto/src/layer.rs` (`Layer`, `for_each_term`), `rust/core/proto/src/reader/lfc2.rs`.
- The notes of 29 October: `experiments/2026-10-29-heap`, `2026-10-29-heap-profile`, `2026-10-29-circuit-forms`, and the decision note on the circuit's representation.
