# 0084 The memory milestone closed: the peak heap at 1.17 and 1.30 times upstream's

## Status

Accepted (2026-11-07, at the merge of pull request #121; proposed 2026-11-07, close of the memory milestone of Phase D).

## Date

2026-11-07

## Context

[ADR 0080](0080-milestone-memory.md) opened a memory milestone after M2, in Gold like M2: the peak heap of the prover and the verifier on the mDoc version 7 circuits within twice upstream's, by the same measure, the bytes allocated at the peak of each process under one `LD_PRELOAD` counter on both sides. Upstream's peaks, both circuits in one process, are 107 MB for the prover and 48 MB for the verifier, so the criterion is 214 MB and 96 MB. At the close of M2 the prover's peak on the hash circuit was 645 MB and the verifier's 515 MB.

The milestone ran from 29 October to 7 November, through the steps recorded in ADR 0080 and [the performance page](../guide/performance.md):

- the first step, without a format change: the verifier binds the largest layer by reference, the command-line prover frees its provisional buffers;
- block 1 (#57): the circuit held in the packed form of the file, 4.2 MB for the hash circuit against 236.7 MB expanded, proved on a ghost expansion;
- block 2 (#58): the first step of a layer bound and merged from the packed form, one working entry per run of equal hands;
- block 3 (#100, #101): the verifier, then the prover, on the packed circuit, the expanded path removed from the executable code;
- block 4 (#106, #108): the prover's wires one heap segment per layer, freed as the layer is proved, and the working vectors of the rounds in upstream's form;
- the eq2 table filled in one array by upstream's recursion (#105).

The milestone review (#63, [ADR 0083](0083-claims-corrected-at-the-milestone-review.md)) corrected the claims the review found, and the round trip on the four production mDoc circuits entered the `cli` step of `make check` (#64).

## Decision

**The memory milestone is closed. The criterion is met, with two remaining items recorded as issues.**

The measurement, one session of the proving machine on 7 November, the release branch at a4a3836, three runs of each program on each circuit, the peaks identical from run to run, upstream's `heap_v7` (the version 7 flow on upstream's runtime at d5e6be7, generic arithmetic, baseline processor, both circuits in one process) under the same counter in the same session:

| Peak heap, mDoc v7 | close of M2 (88835f2) | at the close (a4a3836) | upstream, both circuits | ratio | share of the criterion |
|---|---|---|---|---|---|
| prover, hash | 645 MB | 125 MB | 107 MB | 1.17 | 58 % |
| prover, signature | 78 MB | 20 MB | | | |
| verifier, hash | 515 MB | 62 MB | 48 MB | 1.30 | 65 % |
| verifier, signature | 44 MB | 9.5 MB | | | |

The milestone traded no time for memory, as ADR 0080 asked (the work is Gold, like M2): in the same session the hash proof takes 4.69 s and its verification 2.34 s, the signature proof 0.46 s and its verification 0.28 s (at the close of M2, in its own session: 4.84 s, 2.52 s, 0.48 s, 0.29 s; sessions differ by up to 8 %). The proofs of the command line are identical byte for byte to those of every step of the milestone.

What remains above upstream at the prover's peak, layer 13 of the hash circuit, is recorded as issues rather than done here:

- **the run entry of the merged terms, 32 bytes against upstream's 24** (#110): 9.2 MB at the peak. It changes the working type of the merged terms and every contract that names it, at their levels, after a design shown to the maintainer: a block of several days for 9.2 MB on a criterion already met;
- **the eq2 table filled to the power of two above the layer's wire count** (#120): upstream stops at the number of wires. It changes the contract of `Eq2_Table` and every reader of the table has to show it reads below that count; the gain is unmeasured. It is a Task of M3a, the Gold optimisation step, where a change of contract for memory and time belongs by [ADR 0082](0082-order-after-the-memory-milestone.md).

## Alternatives considered

- **#110 in 0.4.0.** Rejected: about a week more before the release, for 9.2 MB on a criterion met with margin.
- **The truncation of the eq2 table in 0.4.0.** Rejected for the same reason, and its gain is not measured.
- **ADR 0080 amended with the close.** Rejected: its body is immutable (ADR 0042) and would carry a long note; a closing record in the form of [ADR 0078](0078-milestone-m2-closed.md) keeps the measurement and the decision in one place. ADR 0080 is Accepted with a note to this record.

## Consequences

- Release 0.4.0: Phase D, performance and memory, the first release after a review of the whole repository (ADR 0082). The tag names the reference state for the measurements that follow.
- The order of ADR 0082 follows: the mDoc layer, the guide for the evaluator, the certification block, then M3 opened by M3a.
- [The performance page](../guide/performance.md) records the milestone as closed, with the final table.
- The trusted base register keeps the final figures and its list of fragilities recomputed from the gate of a4a3836 (#92).
- ADR 0080 points here in its Status line.

## Verification impact

- None. Every step of the milestone kept its contracts proved: no `pragma Assume`, no weakened contract, no change of the prover settings. One proof was split with the maintainer's agreement (`Lemma_Bind_H_Step`, block 4a), its contract unchanged.
- The project at the close of the milestone, the gate of a4a3836: 33,276 checks, all proved; most steps 463,202, unchanged since block 4a.

## References

- [ADR 0067](0067-performance-milestones-by-trust.md), [ADR 0078](0078-milestone-m2-closed.md), [ADR 0080](0080-milestone-memory.md), [ADR 0082](0082-order-after-the-memory-milestone.md), [ADR 0083](0083-claims-corrected-at-the-milestone-review.md).
- Chapter 3 Sections 3.3 to 3.5, chapter 6 Section 3.7, chapter 7 Sections 2.1, 2.3, 3.3 and 3.7.
- The counter and upstream's driver: `scripts/measure/heapshim.c`, `scripts/measure/heap_v7.rs`.
- longfellow-zk/longfellow-zk at d5e6be7: `rust/core/proto/src/layer.rs`, `rust/runtime/sumcheck/src/eq.rs`.
