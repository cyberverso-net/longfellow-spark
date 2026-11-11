# 0090 The mDoc milestone closed: Phase D complete

## Status

Accepted (2026-11-11, at the merge of pull request #163; proposed 2026-11-11, close of the mDoc milestone of Phase D).

## Date

2026-11-11

## Context

[ADR 0055](0055-phase-d-scope-mdoc-scale.md) set the goal of Phase D: a complete mDoc proof of age for the attribute `age_over_18` of upstream's test document `age_over_18-website-mdoc[5].json`, in the format of upstream's `applications/mdoc_zk` (six MACs, the hash proof, the signature proof), produced by this project and accepted by upstream's mDoc verifier, with its time and memory measured against the milestones. [ADR 0082](0082-order-after-the-memory-milestone.md) split the phase into two releases: 0.4.0 at the close of the memory milestone ([ADR 0084](0084-memory-milestone-closed.md)), 0.5.0 at the close of the mDoc layer, Phase D complete by the criterion of ADR 0055.

The mDoc milestone ran from 7 to 11 November:

- the prover and the verifier in two phases over one transcript, as upstream's `commit` and `prove` ([ADR 0085](0085-prover-and-verifier-in-two-phases.md), #125);
- block 5, the mDoc layer from upstream's witness files: the MACs, the public inputs, the proof format, two programs ([ADR 0058](0058-mdoc-layer.md), #126, #65);
- block 6, the witness from the credential itself, in three parts: the ECDSA witness, the parse of the mDoc and the SHA-256 trace, the two witness builders ([ADR 0086](0086-mdoc-witness-bounds-and-constant-time.md), #134, #135, #136, #66);
- the cross-check with upstream's verifier at every gate ([ADR 0087](0087-cross-check-with-upstream-at-every-gate.md), #142) and the reuse of a proof whose inputs are unchanged ([ADR 0088](0088-proof-inputs-and-the-reuse-of-a-proof.md), #144);
- the 38 test documents of upstream at both versions in the gate (#150);
- the supported mDoc profile, its two rows and one entry point per role ([ADR 0089](0089-the-supported-mdoc-profile.md), #79).

The milestone review (#67) corrected the claims it found ahead of the code or the proofs (#155, #161) and made the gate start only from a clean checkout of the commit it reports (#162).

## Decision

**The mDoc milestone is closed, and with it Phase D. The criterion of ADR 0055 is met.**

- **The proof of age from the credential.** `longfellow_prove_mdoc --mdoc` proves `age_over_18` from upstream's document `age_over_18-website-mdoc[5].json` (the `TEST_DATA` case of upstream's runtime), in upstream's format; upstream's verifier at the pin accepts it at every gate (`scripts/cross-check-upstream.sh`), beside the proofs from the witness files and from the Mustermann document at both versions, and refuses an altered proof.
- **Every test document.** The 38 documents of upstream at both versions, with upstream's own requests, are proved and verified, or refused as upstream's tests expect, at every gate on the proving machine (`scripts/mdoc-cases.sh`).
- **Time and memory**, the final session (one session of the proving machine on 11 November, right after the full gate of the same commit, three runs of each program plain and three under the heap counter, upstream's `heap_v7` three times plain and once under the counter), the release commit 9f790cf, upstream at d5e6be7 in the same session, both circuits of the version 7 pair in one process, the same flow on both sides on the `TEST_DATA` document:

| mDoc v7, both circuits in one process, `TEST_DATA` | at the close (9f790cf) | upstream (d5e6be7) | ratio | share of the ADR 0080 criterion |
|---|---|---|---|---|
| proof, wall time, median of 3 | 4.55 s | 4.12 s | 1.10 | |
| proof, peak heap | 132 MB (131,514,792 B) | 107 MB (107,021,240 B) | 1.23 | 61 % of 214 MB |
| verification, wall time, median of 3 | 2.60 s | 1.65 s | 1.58 | |
| verification, peak heap | 64 MB (63,996,152 B) | 48 MB (48,162,672 B) | 1.33 | 67 % of 96 MB |

The round trip, one proof and one verification, is 7.15 s against upstream's 5.77 s, 1.24 times. The peaks are identical from run to run, the times within 0.02 s. The proofs are byte for byte those of the sessions of 8 and 10 November: from the Mustermann document and from its witness files under the same seed (SHA-256 `eb1fb46c…`), from `TEST_DATA` (`1d6cbca3…`); the two single-circuit proofs are those of release 0.4.0. The proof from the witness files takes 4.53 s, from the Mustermann document 4.55 s; the version 6 pair 3.95 s to prove and 2.39 s to verify. In the same session the hash circuit alone takes 4.64 s and 125 MB to prove, 2.31 s and 62 MB to verify, within 300 bytes of the peaks of release 0.4.0.

The criterion of the memory milestone, twice upstream's peak for the same flow (214 MB and 96 MB), holds for the complete proof of age. The remaining gap in time is the one M2 left in place ([ADR 0078](0078-milestone-m2-closed.md)): work upstream's generic code also does, or that only tested code removes; it sits in the verification more than in the proof.

What Phase D leaves open is recorded as issues:

- the pads of the MAC drawn inside the profile's prover entry point, beside the nonce, in Phase E (#156); until then they are the caller's obligation (ADR 0089);
- one conversion of the device authentication digest to e2 (#157) and a manifest of upstream's recordings (#158), in the certification block;
- the Lean correspondence reread at the merge of upstream's pull requests 225 and 215 (#122);
- the run entry of the merged terms (#110) and the eq2 table above the layer's wire count (#120), in M3a.

## Alternatives considered

- **ADR 0055 amended with the close.** Rejected, as for ADR 0084: ADR 0055 is still Proposed, but it carries four amendments in its Status line already, and a closing record keeps the measurement and the decision in one place. ADR 0055 is Accepted with a note to this record.

## Consequences

- Release 0.5.0: Phase D complete, the production mDoc circuits at full scale and the proof of age from the credential, accepted by upstream's verifier.
- The order of ADR 0082 follows: the guide for the evaluator, the certification block, then M3 opened by M3a. The circuit compiler stays Phase E.
- Upstream's Longfellow v2, under development on upstream's branch `v2` with new mDoc circuits, is followed in a milestone of its own, without implementation until upstream freezes its circuits. Version 1, which this project implements, stays upstream's deployed version.
- [The performance page](../guide/performance.md) records the milestone as closed, with the final table.
- The trusted base register keeps the final figures and its list of fragilities recomputed from the gate of 9f790cf (#92).
- ADR 0055 points here in its Status line.

## Verification impact

- None. Every block of the milestone kept its contracts proved: no `pragma Assume`, no weakened contract, no change of the prover settings.
- The project at the close of Phase D, the gate of 9f790cf: 39,177 checks, all proved; most steps 463,202, unchanged since block 4a of the memory milestone.

## References

- [ADR 0055](0055-phase-d-scope-mdoc-scale.md), [ADR 0058](0058-mdoc-layer.md), [ADR 0078](0078-milestone-m2-closed.md), [ADR 0082](0082-order-after-the-memory-milestone.md), [ADR 0084](0084-memory-milestone-closed.md), [ADR 0085](0085-prover-and-verifier-in-two-phases.md) to [ADR 0089](0089-the-supported-mdoc-profile.md).
- Chapter 9, the trust model, the trusted base register, the performance page.
- The counter and upstream's driver: `scripts/measure/heapshim.c`, `scripts/measure/heap_v7.rs`; the round trip `scripts/measure-mdoc.sh mdoc v7`.
- longfellow-zk/longfellow-zk at d5e6be7: `rust/applications/mdoc_zk/`.
