# 0055 Phase D scope: the mDoc scale and the proof of age

## Status

Proposed (2026-10-19, block 1 of Phase D). The performance target was replaced by milestones on 2026-10-21, at the close of block 4, with the author.

## Date

2026-10-19

## Context

Phase C closed with a prover that reproduces the two upstream proofs byte for byte ([ADR 0049](0049-phase-c-scope-the-prover.md)) on circuits of 7233 and 1527 witnesses with 256 Reed-Solomon columns. The circuits that a real mDoc verifier accepts are two to three orders of magnitude larger. The production artifacts of google/longfellow-zk at d5e6be7 (`rust/applications/mdoc_zk/artifacts/`) ship, for each supported version and number of attributes, one archive with two circuits: the hash circuit over GF(2^128) and the signature circuit over P-256. The version 7 archive with one attribute, the latest the artifacts ship (`runtime/src/zk_spec.rs` lists versions 5 to 7 in `ZK_SPECS` and a version 8 in `CURRENT_ZK_SPECS`, `CURRENT_VERSION = 8` in `circuits/src/lib.rs` line 26, whose circuits `5a893815...` are not among the archives of `artifacts/circuits/`, `all_circuit_hashes ()` of `artifacts/src/lib.rs` listing versions 5, 6 and 7 only), holds a hash circuit of 17 layers, 7 757 579 terms and 85 118 inputs (952 public), to be committed with rate 7, 132 queries and 4151 columns, and a signature circuit of 21 layers, 481 833 terms and 3739 inputs (900 public), rate 7, 132 queries, 4096 columns. The version 6 archive holds a hash circuit of 15 layers, 6 823 073 terms, 75 098 inputs, rate 4, 128 queries, 4096 columns, and the same signature circuit at rate 4, 128, 2945.

The original plan put the circuit compiler as Phase D. The author decided to prove the existing circuits first, at this scale, within a performance target, and to reach a complete mDoc proof; the compiler becomes Phase E.

Block 1 measured where the project stands. The loader accepts all four circuits within its bounds (`circuit_kat`, 82 cases, 36 seconds with assertions on, 278 MB). The command-line prover of Phase C, as it is, on the author's machine in the release build: on the hash circuit it overflowed the 8 MB main stack in `Eval_Circuit` of stage 3, whose per-layer value arrays are stack objects (a layer of 2^20 wires is 16 MB), and with a 64 MB stack it produced the proof (161 640 bytes) in 1434 seconds of CPU with a peak of 888 MB; on the signature circuit it produced the proof (199 020 bytes) in 1310 seconds with a peak of 216 MB (972 seconds and 170 MB under the version 6 configuration). The verifier accepts both proofs: the signature one in 62 seconds and 48 MB, the hash one in 166 seconds and 452 MB, and only with the 64 MB stack, since the input constraint of the stage 3 core overflows the default stack on 84 166 private inputs. The costs are in the places the handoff named and in one it did not: the Lagrange tables of the prover are built for every parity column with a product over the row length, k^2 (NCOL - k) multiplications, 3.4 thousand million on P-256 for the signature circuit's two tables, before any row is encoded; the stage 3 input constraint is an `Expression` quadratic in the private inputs (84 166 on the hash circuit); the wires of every layer are evaluated on the stack.

## Decision

- **Goal of the phase.** A complete mDoc proof for the age verification case (attribute `age_over_18` on the upstream test mDoc `age_over_18-website-mdoc[5].json` of `testcases/src/vectors.rs`), in the format of `applications/mdoc_zk` (`MdocProof::write`: six MACs, the hash proof, the signature proof), produced by this project and accepted by the upstream mDoc verifier (`run_mdoc_verifier`, run by the author with cargo), with time and memory measured and within the target below.
- **The two circuits of the phase** are those of the version 7 archive with one attribute (`8d079211...`), with the version 6 archive (`137e5a75...`) as the second configuration; both are copied with their witnesses and example proofs under `tests/vectors/upstream/mdoc/` and pinned by hash ([ADR 0059](0059-mdoc-vectors-and-measurement.md)).
- **Performance target, by milestones** (confirmed with the author on 2026-10-21, replacing the factors first proposed). The goal is a round trip under one second: the two proofs of the version 7 circuits and their two verifications, on the proving machine of [ADR 0060](0060-proving-machine-on-google-cloud.md), one core. Upstream shows it can be done: its own benchmark (`mdoc_zk_bench_v7` at d5e6be7) runs the whole flow on that machine in 0.85 seconds with the hardware carry-less multiplication (590 ms to prove, 256 ms to verify, circuits loaded each time), and in 4.0 seconds with its generic multiplication. At the close of block 4 this project takes about 600 seconds (425 to prove, 175 to verify). The milestones:

| Milestone | Content | Round trip | Trust |
|-----------|---------|------------|-------|
| M1, algorithmic parity | eq tables in `Eval_Bound_Quad` and in the input constraint; barycentric weights in the verifier's Lagrange tables; the sumcheck prover realigned with the reference's after a study of its costs; memory closer to the reference's 134 MB | at most 100 s | proved as today |
| M2, fast software multiplication | the carry-less product in constant time with integer multiplications (as BearSSL's ctmul64), Karatsuba, reduction; P-256 measured | at most 5 s | proved |
| M3, hardware multiplication | PCLMULQDQ on x86, PMULL on ARM | at most 1 s | the multiplication trusted and tested; a record of its own |
| M4, optional | parallelism (Ada tasks, Jorvik profile) | to be set | to be decided |

  The M1 target is the least certain: it depends on how many multiplications per term the reference's sumcheck makes, measured at the start of M1. Memory is already within target (599 and 74 MB at the peak, against 1 GB). At M3 the author intends to keep two variants: one with the stronger trust model of the proved multiplication, and a faster one with the hardware instruction and a justified compromise. That choice is discussed when M3 starts.
- **The three costs are addressed in order**, each with its own record: the input constraint made linear ([ADR 0056](0056-linear-input-constraint.md), block 2), the additive FFT on GF(2^128) in place of the Lagrange tables and encoder ([ADR 0057](0057-additive-fft.md), block 3), then P-256 measured and decided, and memory ([ADR 0057](0057-additive-fft.md), block 4). The additive FFT is done, without evaluating alternatives: it is the draft's own extension of Section 2.2.2, and it has the full didactic cycle (chapter 8).
- **A fourth cost is measured, not yet decided.** The sumcheck prover itself walks the 7.7 million terms of the hash circuit for about twenty rounds per layer and two hands, of the order of 300 million multiplications in GF(2^128) in software, 5 to 15 seconds on its own, and may dominate once the FFT is in place. Every measurement of the phase, from block 2 on, is therefore profiled by phase (circuit evaluation, validation, pads, Lagrange tables, encoding, Merkle, sumcheck prover, Ligero proof, writing), so that the target is apportioned and the dominant cost known at each step. Should the sumcheck dominate after the FFT, the lever is the multiplication in GF(2^128) under the constant-time discipline of [ADR 0006](0006-constant-time-discipline-and-scope.md): recorded here as measured, not decided. Since block 4 it is the dominant cost of both provers (about half of each proof in `Round_Evals`), and milestones M1 and M2 address it.
- **The stack is not the place for the wires.** `Eval_Circuit`'s per-layer arrays move to the heap under [ADR 0047](0047-heap-allocation-by-ownership.md) in block 2, with the linear constraint, so that no circuit in the bounds needs a stack above the default.
- **The mDoc layer comes last** ([ADR 0058](0058-mdoc-layer.md), blocks 5 and 6): the MACs, the public inputs, the transcript, the proof format, the witness.
- **The statuses and the command line.** `longfellow_prove` gains a binary inputs format for the upstream witness files (ADR 0059); the statuses of ADR 0049 stand.

## Alternatives considered

- **The circuit compiler first, as the original plan.** Deferred to Phase E: a compiler that produces circuits this project cannot prove in reasonable time would be measured by nothing.
- **A smaller target circuit.** Rejected: the version 7 one-attribute archive is what a production verifier accepts today; proving anything less does not reach the goal.
- **Keeping Lagrange and optimising its tables.** The tables are a one-off cost per configuration and could be cached, but the per-row encoding stays k times NCOL per row, and the draft defines the code through the additive FFT; the FFT is the decision, with the Lagrange encoder kept as the reference the harness compares against.

## Consequences

- Blocks 2 to 7 of the handoff, each with its record and its measurements; chapters 8 (the FFT) and 9 (the mDoc layer) with the full cycle.
- The trust model gains the mDoc layer's entries when it lands; the targets are stated in the README with the measured figures.
- Release 0.4.0 after block 4 if the author wants an intermediate tag; 0.5.0 at the close.

## Verification impact

- Provable: as the records of each block say; the Silver discipline on every new unit, structural Gold where the provers close it.
- Tested: the two upstream proof files remain the byte-for-byte anchors of the Phase C exit criterion, the codeword identity between the two encoders, the acceptance of the mDoc proof upstream.
- Trusted: unchanged, plus what ADR 0058 adds for the mDoc layer.
- Constant time: ADR 0051 extends to the FFT (butterflies on public indices) and ADR 0058 says what the witness generation can and cannot promise.

## References

- google/longfellow-zk at d5e6be7: `rust/applications/mdoc_zk/artifacts/` (`src/lib.rs`, `circuits/`, `proofs/`), `runtime/src/zk_spec.rs`, `runtime/src/prover.rs`, `runtime/src/proto.rs`, `runtime/src/mac.rs`, `rust/core/proto/src/archive/`, `rust/runtime/algebra/src/lch14_reed_solomon.rs`, `testcases/src/vectors.rs`.
- The handoff of 2026-10-19 and the session note `2026-10-19-phase-d-mdoc.md` with the measurements of block 1.
- [ADR 0011](0011-circuits-as-data.md), [ADR 0047](0047-heap-allocation-by-ownership.md), [ADR 0049](0049-phase-c-scope-the-prover.md), [ADR 0036](0036-lagrange-interpolation-instead-of-additive-fft.md).
