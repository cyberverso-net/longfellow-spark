# Architecture decision records

Format and lifecycle: see [0001](0001-record-architecture-decisions.md) and, for the amendment notes of a Status line, [0042](0042-status-amendments.md). Records 0002 to 0011 were written retroactively on 2026-10-09 from the package headers, the README, the git history and the project notes; their Date is the date the decision was taken (the first commit that records it), and they say where rationale was not recorded at the time.

| Number | Title | Status | Date |
|--------|-------|--------|------|
| [0001](0001-record-architecture-decisions.md) | Record architecture decisions | Accepted, amended by 0042 | 2026-10-09 |
| [0002](0002-pin-the-specification.md) | Pin the specification to draft-google-cfrg-libzk-03 | Accepted | 2026-10-06 |
| [0003](0003-proof-policy-and-trust-model.md) | Proof policy and trust model | Accepted, amended by 0020 | 2026-10-06 |
| [0004](0004-gf2-128-element-representation.md) | GF(2^128) element representation | Accepted | 2026-10-06 |
| [0005](0005-mul-ref-as-proof-target.md) | Ghost reference Mul_Ref as the proof target of Mul | Accepted | 2026-10-06 |
| [0006](0006-constant-time-discipline-and-scope.md) | Constant-time discipline and its scope | Accepted | 2026-10-06 |
| [0007](0007-square-as-wrapper-over-mul.md) | Square as a wrapper over Mul | Accepted | 2026-10-08 |
| [0008](0008-inv-fixed-chain-total-function.md) | Inv as a fixed Itoh-Tsujii chain, total on zero | Accepted | 2026-10-08 |
| [0009](0009-known-answer-vectors.md) | Known-answer vectors: notation, tiers, anchors | Accepted | 2026-10-08 |
| [0010](0010-assertion-enabled-test-project.md) | Test project compiling the library with assertions | Accepted, amended by 0044 | 2026-10-08 |
| [0011](0011-circuits-as-data.md) | Circuits are data | Accepted | 2026-10-06 |
| [0012](0012-p256-limb-representation.md) | P-256 base field: limb representation | Accepted | 2026-10-09 |
| [0013](0013-p256-reduction-strategy.md) | P-256 base field: reduction strategy | Accepted | 2026-10-09 |
| [0014](0014-p256-functional-specification-and-ghost-model.md) | P-256 base field: functional specification and ghost model | Accepted, amended by 0044 | 2026-10-09 |
| [0015](0015-p256-canonical-form-and-conditional-subtraction.md) | P-256 base field: canonical form and conditional subtraction | Accepted | 2026-10-09 |
| [0016](0016-p256-inversion.md) | P-256 base field: inversion | Accepted | 2026-10-09 |
| [0017](0017-p256-test-anchors.md) | P-256 base field: test anchors | Accepted | 2026-10-09 |
| [0018](0018-continuous-verification-gate.md) | Continuous verification gate | Accepted, amended by 0019 and 0020 | 2026-10-09 |
| [0019](0019-proof-off-the-hosted-gate.md) | Proof off the hosted gate | Accepted, amended by 0021, 0033 and 0041 | 2026-10-11 |
| [0020](0020-prover-configuration-step-budget.md) | Prover configuration by step budget | Accepted | 2026-10-11 |
| [0021](0021-proof-on-pull-requests.md) | Proof on pull requests to main | Accepted, amended by 0033, 0034 and 0041 | 2026-10-11 |
| [0022](0022-stage-3-scope-and-challenges-as-input.md) | Stage 3 scope: sumcheck algebra and symbolic verifier core, challenges as input | Accepted | 2026-10-12 |
| [0023](0023-gold-perimeter-for-protocol-code.md) | Gold perimeter for protocol code | Accepted | 2026-10-12 |
| [0024](0024-field-genericity-by-formal-package.md) | Field genericity by formal package | Accepted | 2026-10-12 |
| [0025](0025-polynomials-and-lagrange-constants.md) | Polynomials and Lagrange constants | Accepted | 2026-10-12 |
| [0026](0026-sparse-expression.md) | Sparse Expression | Accepted | 2026-10-12 |
| [0027](0027-sumcheck-vectors-and-upstream-instrumentation.md) | Sumcheck vectors and upstream instrumentation | Accepted | 2026-10-12 |
| [0028](0028-stage-4-scope-and-challenge-replay.md) | Stage 4 scope: Fiat-Shamir transcript and challenge replay | Accepted | 2026-10-13 |
| [0029](0029-sha256-and-aes256-in-spark.md) | SHA-256 and AES-256 in SPARK: Silver with NIST vectors, constant-time exemption | Accepted | 2026-10-13 |
| [0030](0030-literal-rejection-sampling.md) | Literal rejection sampling and declared non-termination | Accepted | 2026-10-13 |
| [0031](0031-transcript-gold-perimeter.md) | Transcript Gold perimeter | Accepted | 2026-10-13 |
| [0032](0032-transcript-vectors.md) | Transcript vectors: Appendix B.2, Appendix B.3 end to end, NIST | Accepted | 2026-10-13 |
| [0033](0033-parallel-proof-partitions.md) | Parallel proof partitions on the hosted runner | Accepted, amended by 0034 | 2026-10-15 |
| [0034](0034-proof-as-information-harnesses-in-parallel.md) | Proof on pull requests as information; harnesses in parallel | Accepted, amended by 0041 and 0045 | 2026-10-15 |
| [0035](0035-stage-5-scope-ligero-and-the-complete-verifier.md) | Stage 5 scope: Ligero and the complete verifier | Accepted | 2026-10-15 |
| [0036](0036-lagrange-interpolation-instead-of-additive-fft.md) | Reed-Solomon by Lagrange interpolation, not the additive FFT | Accepted | 2026-10-15 |
| [0037](0037-checked-inv-and-public-data-scope.md) | Checked_Inv, and the public-data scope of the Ligero units | Accepted | 2026-10-15 |
| [0038](0038-gold-perimeter-for-merkle-and-ligero.md) | Gold perimeter for Merkle and Ligero | Accepted | 2026-10-15 |
| [0039](0039-sizes-allocation-and-status.md) | Sizes, allocation and the status enumeration | Accepted, amended by 0043 | 2026-10-15 |
| [0040](0040-ligero-vectors-and-upstream-instrumentation.md) | Ligero vectors and upstream instrumentation | Accepted | 2026-10-15 |
| [0041](0041-verification-cadence.md) | Verification cadence: the proof by hand, the slow harness cases weekly | Accepted, amended by 0044 and 0045 | 2026-10-16 |
| [0042](0042-status-amendments.md) | Status amendments | Accepted | 2026-10-16 |
| [0043](0043-exhausted-status-and-streaming-slice.md) | Exhausted status and streaming slice | Accepted | 2026-10-16 |
| [0044](0044-field-contracts-at-proof-only-level.md) | Field contracts at proof-only level | Accepted | 2026-10-16 |
| [0045](0045-proof-gate-restored-through-partitions.md) | Proof gate restored through partitions | Accepted | 2026-10-16 |
| [0046](0046-phase-b-scope-lfc2-loader-and-interop.md) | Phase B scope: the LFC2 circuit loader and the interop exit criterion | Accepted | 2026-10-16 |
| [0047](0047-heap-allocation-by-ownership.md) | Heap allocation by ownership for the circuit and the working set | Accepted | 2026-10-16 |
| [0048](0048-circuit-vectors-and-interop-proofs.md) | Circuit vectors and the upstream interop proofs | Accepted | 2026-10-16 |
| [0049](0049-phase-c-scope-the-prover.md) | Phase C scope: the prover and its exit criterion | Proposed | 2026-10-17 |
| [0050](0050-randomness-as-a-byte-stream.md) | Randomness as a byte stream, and its sources | Proposed | 2026-10-17 |
| [0051](0051-constant-time-in-the-prover.md) | Constant time in the prover, unit by unit | Proposed | 2026-10-17 |
| [0052](0052-gold-perimeter-for-the-prover.md) | Gold perimeter for the prover | Proposed | 2026-10-17 |
| [0053](0053-prover-vectors-and-cross-verification.md) | Prover vectors and cross-verification | Proposed | 2026-10-17 |
