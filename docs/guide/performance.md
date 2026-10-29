# Performance

This page records how fast the project proves and verifies the production mDoc circuits, how it got there, and how it compares with upstream. The milestones are set by [ADR 0055](../adr/0055-phase-d-scope-mdoc-scale.md) and [ADR 0067](../adr/0067-performance-milestones-by-trust.md); M2 closes with [ADR 0078](../adr/0078-milestone-m2-closed.md).

## What is measured

- **The round trip:** the two proofs of the version 7 mDoc circuits (hash over GF(2^128), signature over P-256) and their two verifications.
- **The machine:** the proving machine of ADR 0060, a c4-standard-24 (Xeon Platinum 8581C), one core.
- **The build:** the proved build of the command line (ADR 0068), GCC 16.1, `-O3`, for the baseline x86-64 processor.
- **The protocol** (ADR 0067):
  - one series per comparison, all commits in the same session of the machine;
  - three runs of each commit, the median reported;
  - a 64 MB stack for all;
  - upstream's bench in the same session, generic for the baseline processor.
- **Sessions differ.** The same commit can be up to 8 % slower in one session than in another. Only figures from the same session are compared.
- **The scripts:** `scripts/measure-mdoc.sh` times the four runs, and with `MEASURE_PROFILE=1` profiles them with `perf`.

## The milestones

| Milestone | Content | Reference | Status |
|---|---|---|---|
| M1 | Algorithmic parity: the eq tables, the verifier's Lagrange weights, the sumcheck prover realigned | at most 100 s | closed at about 126 s |
| M2 | The Gold limit: as fast as the code goes while every contract stays proved | upstream generic | closed at 8.13 s (ADR 0078) |
| M3 | A tested variant chosen at build time: hardware carry-less product, the verifier's encoding by FFT | upstream hardware, 0.69 s | next |
| M4 | Parallelism | to be set | optional |

M2 has no target figure. It closes on a criterion (ADR 0067): every remaining cost is either work upstream's generic code also does, by the same algorithm, or a cost that only tested code removes.

## The path through M2

Round trip on the proving machine, proved build unless said otherwise. Each step is a record of its own. The figures before 22 October come from single runs; the later ones from the series of each record, each in its own session.

| Step | Record | Round trip |
|---|---|---|
| Close of M1 | ADR 0063 | about 126 s |
| Upstream's carry-less product, proved | ADR 0065 | about 85 s |
| The verifier's Lagrange tables by prefix and suffix | ADR 0066 | 27.8 s (the `-O2` build) |
| The release build without run-time checks in the proved units | ADR 0068 | 22.5 s |
| P-256 in Montgomery form | ADR 0069 | 19.0 s |
| The sumcheck and Ligero kernels in upstream's form | ADR 0070 | 16.7 s |
| The prover reuses its bound quad | ADR 0071 | 15.2 s |
| No second predicate check in the prover instances | ADR 0072 | 14.1 s |
| The verifier binds the quad as upstream | ADR 0073 | 14.1 s |
| The circuit identifier checked once | ADR 0074 | 9.0 s |
| The round evaluations from the claim | ADR 0075 | 8.7 s |
| The field operations without call and finalisation overhead | ADR 0076 | 8.15 s |
| The circuit predicate checked once at the entry | ADR 0072, amended | 7.99 s |
| The Montgomery round of P-256 as upstream's CIOS step | ADR 0077 | -0.13 s in its session |

The proofs of the command line have stayed identical byte for byte at every step.

## At the close of M2

Main at 8a037f8, one session of 29 October, median of three runs:

| | prove | verify |
|---|---|---|
| hash circuit | 4.84 s | 2.52 s |
| signature circuit | 0.48 s | 0.29 s |
| round trip | | **8.13 s** |

The same session, upstream's bench (`mdoc_zk_bench_v7` at d5e6be7, the `_v2` rows, which read the LFC2 format as this project does):

| | prove | verify | round trip |
|---|---|---|---|
| upstream, generic, baseline processor | 4.19 s | 1.64 s | 5.83 s |
| this project, proved build, baseline processor | 5.32 s | 2.81 s | 8.13 s |

Upstream's other rows, from the session of 27 October: hardware multiplication 0.48 s and 0.17 s; generic as published (`target-cpu=native`) 2.67 s and 1.07 s.

The fair comparison is the one above: the same processor target, the same algorithms. The two numbers still measure slightly different things:

- this project runs one process per circuit, cold, and reads and parses the LFC2 file each time;
- upstream's figure is the mean of warm iterations, both circuits in one process, including the mDoc layer and the witness generation;
- upstream is built with LTO; its generic variant also replaces the conditional moves of P-256 in assembly.

### Where the gap goes

Ours minus upstream, from the profiles of the same session (both at 999 samples a second):

| Item | Gap | Kind |
|---|---|---|
| The verifier's Ligero encoding and tables: Lagrange here, FFT upstream | +0.59 s | only tested code removes it: M3 |
| Reading the circuit files, with their shape proved, in each process | +0.61 s | scope |
| Cold process, first touch of memory | +0.6 s | scope |
| The GF(2^128) sumcheck prover: the same algorithm, 95.4 M products against 93.3 M | +0.44 s | code generation, GCC against LLVM |
| The P-256 arithmetic: the same algorithm, product 19.9 against 11.4 ns, sum 11.3 against 2.0 ns | +0.35 s | code generation |
| SHA-256 in software, against upstream's SHA instructions | +0.08 s | only tested code removes it: M3 |
| The verifier's bound quads | -0.05 s | the same |
| The Ligero prover | -0.40 s | faster here |
| The mDoc layer and the witness, measured by upstream only | -0.31 s | scope |

### The multiplication in GF(2^128)

The product is the same algorithm as upstream's generic code (ADR 0065), proved Gold. On the proving machine, in ns per product:

| | ours (GCC) | upstream (LLVM) |
|---|---|---|
| baseline x86-64 | 34.3 | 37.8 |
| with AVX-512 | 34.5 | 24.2 |
| native (AVX-512 and GFNI) | 34.3 | 23.4 |

- At the same target ours is faster.
- Upstream's published generic row is faster because LLVM vectorises its sixteen class products with AVX-512, and uses GFNI for the bit reversals. GCC keeps ours scalar at every target.
- Faster products need SIMD code or the hardware instruction: M3.

## After M2

Recorded here and handled after M2, each with its own record:

- **A scalar GF(2^128) product with fewer multiplications:** five classes and 128-bit integer products, no bit reversal; about 75 multiplications instead of 96. To be prototyped and measured first.
- **The P-256 sum and difference:** an unproved prototype without the generic loop of `Add_Words` takes 5.7 ns against 11.3; the product 16 against 20 ns.
- **The carry idiom** that GCC compiles to add with carry: proved, but slower in the loop form of `Add_Words` (ADR 0077); to be tried again with the prototype's form.

M3 then brings the hardware carry-less product, the verifier's encoding by FFT and the SHA instructions, as a tested build chosen at build time, with the Gold build as the default and the reference.
