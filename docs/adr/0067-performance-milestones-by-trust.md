# 0067 Performance milestones by trust: the Gold limit, then a tested variant

## Status

Proposed (2026-10-22, milestone M2 of Phase D). Amends the performance target of [ADR 0055](0055-phase-d-scope-mdoc-scale.md): milestones M2 and M3, and the upstream figures it quotes.

## Date

2026-10-22

## Context

ADR 0055 set a round trip under one second, by milestones: M2, fast software multiplication, at most 5 s, proved; M3, hardware multiplication, at most 1 s, trusted. The round trip is the two proofs of the version 7 circuits and their two verifications, on the proving machine, one core.

Where the project stands, measured on the proving machine:

- the first measurement of Phase D, block 2: 44 min 12 s;
- the close of block 4: about 600 s;
- the close of M1: about 126 s;
- after the multiplication of upstream ([ADR 0065](0065-carry-less-multiplication-in-gf2-128.md)): about 85 s;
- after the verifier's tables ([ADR 0066](0066-lagrange-tables-by-prefix-and-suffix.md)): 27.8 s (hash 12.1 s to prove, 6.5 s to verify; signature 6.4 s and 2.8 s).

These figures come from runs on different days, one run each; the series of the protocol below replaces them.

Everything on that path is Gold except what ADR 0057 already tests: the FFT of the prover equals the Lagrange encoding.

Two findings change the frame:

- **The upstream figures of ADR 0055 are the wrong rows.** They are the `_v1` rows of `mdoc_zk_bench_v7`, which read the LFC1 archive format. This project reads LFC2, the `_v2` rows. On the proving machine, the v2 rows are 0.69 s with the hardware multiplication (513 ms to prove, 175 ms to verify) and 3.84 s with the generic one (2.74 s and 1.10 s). The circuits are the same as ours: archive `8d079211...`, one attribute, same Ligero parameters.
- **The two numbers do not measure the same thing.**
  - Ours is one process per circuit, one cold run. It includes reading and parsing the LFC2 file and the SHA-256 of the circuit identifier, which upstream skips (`enforce_circuit_id = false`). It excludes the witness generation.
  - Upstream's is the mean of ten warm iterations, hash and signature in one process. It includes the decompression and the witness generation. It is built with `target-cpu=native` and LTO, where this project builds with `-O2` for the baseline CPU.
  - Upstream's generic variant (`force-generic-arch`) also replaces the conditional moves of P-256 in assembly, not only the multiplication in GF(2^128).
  - Both are single-threaded.

The author's intent (2026-10-22): first find how far the Gold code goes, and compare it with upstream's generic code; then build, in parallel, a variant that trades proof for tests where the gain is worth it, and compare it with upstream's hardware figures.

## Decision

- **M2 is the Gold limit.**
  - The code is optimised while keeping its Gold contracts. What is tested today stays tested, and nothing new moves from proved to tested.
  - The reference is upstream's generic variant, 3.84 s (v2 rows).
  - **The stop criterion.** M2 closes when the profile shows that every remaining cost is either work upstream's generic code also does, by the same algorithm, or a cost that only tested code removes (a processor instruction, an encoding by FFT in the verifier). The figure at that point is the cost of the proof at equal algorithm. It is recorded with the profile that justifies it.
- **M3 is the tested variant.**
  - It is a second form of the code, chosen at build time. The Gold form stays in the code as the default and the reference.
  - The candidates, each with its own record: the carry-less multiplication by PCLMULQDQ on x86 and PMULL on ARM; the verifier's encoding by the FFT of the prover, as upstream (kept in reserve by ADR 0066); others only if the profile at the close of M2 names them.
  - A differential harness runs both forms on every vector and on random inputs, and the proofs stay identical byte for byte.
  - The reference is upstream's hardware variant, 0.69 s (v2 rows). The trust model lists, for the tested build, each unit that the Gold build proves and the tested one does not.
- **M4 stays as in ADR 0055**, optional.
- **The measurement protocol** for every figure of a milestone:
  - the proving machine, its type, CPU and compiler version logged with each run;
  - one series per comparison, all commits in the same session of the machine;
  - three runs of each fast commit, the median reported;
  - a 64 MB stack for all, so that the early commits run too;
  - upstream's bench in three forms: hardware, generic as published, and generic built for the baseline CPU like this project;
  - the differences of scope above stated next to every comparison.

## Alternatives considered

- **Keep the targets of ADR 0055 (5 s proved, 1 s trusted).** The 5 s target asks for a number that the Gold code may or may not reach, and says nothing about what it costs to stay proved. A comparison at equal algorithm says it.
- **Move to the hardware multiplication now.** It would show the speed sooner, but the cost of the proof would never be measured on its own.
- **One code with build options scattered through it.** Rejected: the two forms are two sets of units, so the perimeter of the tested build can be read from the code.

## Consequences

- ADR 0055 keeps its other decisions. Its Status gains a note that points here.
- `docs/guide/performance.md` records the milestones, every optimisation step with its measurement, and the comparison tables with upstream, under the protocol above.
- The measurement scripts gain the logging of the machine and the series form.

## Verification impact

- None for M2: the decision keeps every proof.
- For M3: what moves from proved to tested is decided unit by unit, in the records of M3, and listed in the trust model of the tested build.

## References

- [ADR 0042](0042-status-amendments.md), [ADR 0055](0055-phase-d-scope-mdoc-scale.md), [ADR 0057](0057-additive-fft.md), [ADR 0060](0060-proving-machine-on-google-cloud.md), [ADR 0063](0063-milestone-m1-algorithmic-parity.md), [ADR 0065](0065-carry-less-multiplication-in-gf2-128.md), [ADR 0066](0066-lagrange-tables-by-prefix-and-suffix.md).
- google/longfellow-zk at d5e6be7: `rust/applications/mdoc_zk/runtime/benches/mdoc_zk_bench_v7.rs`, `rust/.cargo/config.toml`, `rust/core/proto/src/reader/lfc2.rs`.
