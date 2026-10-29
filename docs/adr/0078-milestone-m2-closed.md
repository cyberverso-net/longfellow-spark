# 0078 Milestone M2 closed: the Gold limit at 8.13 seconds

## Status

Proposed (2026-10-29, close of milestone M2 of Phase D).

## Date

2026-10-29

## Context

[ADR 0067](0067-performance-milestones-by-trust.md) made M2 the Gold limit: the code is optimised while every contract stays proved, and it is compared with upstream's generic code. M2 has no target figure. It closes when the profile shows that every remaining cost is either:

- work upstream's generic code also does, by the same algorithm; or
- a cost that only tested code removes.

M2 ran from 21 to 29 October, through ADR 0065 to 0077. The round trip went from about 126 s at the close of M1 to 8.13 s. The steps and their measurements are in [the performance page](../guide/performance.md).

## Decision

**M2 is closed. The stop criterion is met, with two remaining items recorded as code generation.**

The measurement, one session of the proving machine on 29 October, main at 8a037f8:

| | this project | upstream generic, baseline processor |
|---|---|---|
| prove | 5.32 s | 4.19 s |
| verify | 2.81 s | 1.64 s |
| round trip | 8.13 s | 5.83 s |

The gap of 2.3 s, item by item, from the profiles of both in the same session:

- **Removable only by tested code (M3):**
  - the verifier's Ligero encoding and tables, Lagrange here and FFT upstream: +0.59 s;
  - SHA-256 in software, against upstream's SHA instructions: +0.08 s.
- **Scope:** the two numbers do not measure the same thing.
  - Reading the circuit files, with their shape proved, in each process: +0.61 s.
  - The cold process and the first touch of memory, against upstream's warm iterations: +0.6 s.
  - The mDoc layer and the witness, which only upstream's figure includes: -0.31 s.
- **The same work, by the same algorithm:**
  - the verifier's bound quads: -0.05 s;
  - the Ligero prover: -0.40 s, faster here;
  - the GF(2^128) product: 34.3 against 37.8 ns at the same target.
- **The same algorithm, slower code:**
  - the GF(2^128) sumcheck prover, +0.44 s: 95.4 M products against 93.3 M, on scalar code that LLVM compiles better than GCC;
  - the P-256 arithmetic, +0.35 s: product 19.9 against 11.4 ns, sum 11.3 against 2.0 ns.

These two are recorded as code generation, not as cost of the proof. Their candidates are handled after M2, each with its own record:

- a scalar GF(2^128) product with fewer multiplications: five classes, 128-bit integer products, no bit reversal;
- the P-256 sum and difference in the prototype's form, which takes 5.7 ns against 11.3.

Memory is outside the criterion. The peak heap, the same measure on both sides, is about 7 times upstream's in the prover and 12 times in the verifier, most of it the circuit in memory (32 bytes a term) and the verifier's tables. It is recorded on the performance page and handled after M2.

**The comparison is at the same processor target on both sides.** Upstream's published generic row, 3.74 s (27 October), is built for the native processor. There LLVM vectorises the GF(2^128) product with AVX-512 and uses GFNI. It is given next to ours, with what it is.

## Alternatives considered

- **Another round on P-256 first.** Not taken: at most 0.1 to 0.15 s of the round trip, and the same algorithm as upstream already.
- **Close at the figure of ADR 0055 (5 s).** Not the criterion since ADR 0067. The Gold limit at equal algorithm is 8.13 s on this machine, with 1.8 s of it scope and M3 items.

## Consequences

- M3 starts: a tested variant chosen at build time, with the Gold build as the default and the reference. Its candidates are the hardware carry-less product, the verifier's encoding by FFT and the SHA instructions. The author's intent to keep both variants (ADR 0055) is discussed when M3 starts.
- [The performance page](../guide/performance.md) records the milestones, every step with its measurement, the comparison and the items after M2.
- ADR 0055 and ADR 0067 point here in their Status lines.

## Verification impact

- None. Every step of M2 kept its contracts proved: no `pragma Assume`, no weakened contract except the one agreed in ADR 0075 (the round evaluations under the claim of the round).
- The project at the close of M2: 26339 checks, all proved.

## References

- [ADR 0055](0055-phase-d-scope-mdoc-scale.md), [ADR 0063](0063-milestone-m1-algorithmic-parity.md), [ADR 0067](0067-performance-milestones-by-trust.md), ADR 0065 to [ADR 0077](0077-p256-montgomery-round-as-cios.md).
- The notes of 29 October: `measure-2026-10-29-m2-close`.
- google/longfellow-zk at d5e6be7: `rust/applications/mdoc_zk/runtime/benches/mdoc_zk_bench_v7.rs`.
