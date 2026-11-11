# 0085 The prover and the verifier in two phases: commit, then prove, on a transcript the caller opens

## Status

Accepted (2026-11-08, at the merge of #125, pull request #130; proposed 2026-11-07). The gate of the pull request held 33,709 checks, all proved, 449 of them added by the split, in 165 minutes; the mDoc layer of #126 drives the four phases as the Consequences foresee. Note of 2026-11-11 (#159): the link to ADR 0049 in the References names a file that does not exist; the record is [ADR 0049](0049-phase-c-scope-the-prover.md).

## Date

2026-11-07

## Context

`Zk_Prover.Prove` composed `ZkProver::commit` and `ZkProver::prove` of the reference in one procedure (ADR 0049): it validated the inputs, built the Ligero commitment, opened a transcript from its label, wrote the root and the statement, and proved. `Zk_Verifier.Verify` did the same on its side: it read the proof, then `Replay_Challenges` opened the transcript, wrote the root and the statement and replayed the challenges. One proof, one transcript, root and statement together.

The mDoc proof of `applications/mdoc_zk` (ADR 0058) is two proofs on one transcript. Upstream's prover opens the transcript from the session transcript bytes, commits the hash circuit (the root goes to the transcript), commits the signature circuit, draws from the transcript the value `av` that the MACs use, builds the public inputs of both circuits from `av`, the MACs, the attributes, the date and the keys, and only then proves the two circuits in turn, each proof writing its statement. The verifier mirrors it: both commitments received, `av` drawn, both verified.

Two things follow for this project's units. The commitment phase cannot evaluate the circuit: the public inputs do not exist yet, since `av` and the MACs are among them. And the root of each proof must reach the transcript before either statement, which one procedure that writes root and statement together cannot do.

## Decision

**Each of the two generic units gets the two phases of the reference, as separate procedures, and its original procedure becomes their composition on a fresh transcript.**

- `Zk_Prover.Commit (Sfb, Cfg, P, Priv, C, St)` takes the private inputs only. It checks their count (`Input_Length`) and the subfield (`Not_In_Subfield`), draws the pads, forms the witness vector, builds the Ligero commitment (`Config_Invalid` when a Lagrange denominator has no inverse) and writes the root to the transcript as it is. `Zk_Prover.Prove_Committed (Id, Sfb, Cfg, P, Pub, C, B, Len, St)` takes the public inputs: it checks their count and the first input (`Input_Length`, `Input_Not_One`), evaluates the circuit on the public and the private inputs together and checks the satisfiability (`Not_Satisfied`), writes the statement, runs the sumcheck, the core and the Ligero proof (`Exhausted`), and writes the bytes. Between the phases `Committed`, a private type, holds the commitment and the working set on the heap under the ownership rules of ADR 0047; `Prove_Committed` or `Release` frees it.
- `Zk_Verifier.Receive (B, Off, Cfg, P, R, St)` reads the proof at an offset of the buffer, returns the offset after it (`After`), and writes the root. `Committed` and `Received` carry the shape of the circuit they were made for, layer by layer, and `Fits` requires it of the circuit given to the second phase: the pads, the triples and the proof's layout are laid out by it. `Zk_Verifier.Verify_Received (Id, Cfg, P, Pub, R, St)` checks the public inputs, writes the statement, replays the challenges, computes the bound quads, runs the core and the Ligero verifier, and frees the record. `Read_Proof` gains the variant `Read_Proof_Prefix`, which does not require the proof to end at the end of the buffer.
- `Sumcheck_Transcript.Replay_From_Statement` is `Replay_Challenges` without the reset and the root; `Replay_Challenges` is the reset, the root, then it.
- `Zk_Prover.Prove` and `Zk_Verifier.Verify` keep their names and their contracts. `Prove` is the two checks on the input count and the first input, `Transcript.Reset` with the label, `Commit` on the private inputs, `Prove_Committed` on the public ones. `Verify` is the two checks on the public inputs, the reset, `Receive`, the check that the proof ends at the end of the buffer, `Verify_Received`.

**What changes for the single proof.** The bytes written and the proofs produced are the same: the transcript absorbs the label, the root and the statement in the same order, and the two upstream example proofs are still reproduced byte for byte under the upstream seeds (the regression test of the change). The statuses are the same. The checks that do not depend on the public inputs stay before the commitment: the count of the private inputs, the subfield check, and in `Prove` the count of the inputs and the first input. Only `Not_Satisfied` moves after the commitment, because in a bound pair the public inputs contain `av` and the MACs, which exist only after both commitments, and the circuit can be evaluated only with them. The cost falls on the error path only: on a false input the prover does the commitment's work for nothing and produces no output. The contracts are unchanged, and the structure is upstream's (`prove` evaluates the circuit after `commit`). Decided with the maintainer on 7 November, over two alternatives below.

**What does not change.** No existing contract is weakened or restated; the new procedures carry contracts of their own, in the same form (the statuses as equalities, the heap state as `Is_Null` and `Fits`). The assurance level of every unit and the prover settings are those of ADR 0020. The constant-time account of ADR 0051 is unchanged: the satisfiability check is the same fixed loop with one branch on its result, now in the proving phase.

## Alternatives considered

- **Validation first, then the composition.** `Prove` evaluates the circuit to validate, frees the wires, then runs the two phases, which evaluate again: one more walk of the circuit on the single-proof path (`longfellow_prove`, the harnesses), none on the mDoc path; ADR 0049 untouched. Rejected: the order of the checks was a convenience of the single-proof program, not a security property, and the composition is the form the chapter can state in one sentence.
- **No composition.** `Prove` keeps its body; `Commit` and `Prove_Committed` form a second path over the same helpers. No behaviour change, two paths to keep aligned. Rejected.
- **Keeping the wires between the phases** (the design of the block first proposed to measure it). Impossible: the wires need the public inputs, which the commitment phase does not have.
- **A transcript parameter instead of the package state.** The transcript is a package with state (ADR 0028, ADR 0031); the two phases drive it in sequence like everything else. Not changed here.

## Consequences

- The mDoc layer (#126) drives the four phases on one transcript: reset with the session transcript, two commits, the draw of `av`, two proofs; the verifier likewise.
- Chapter 7 Section 3.7 and chapter 4 Section 3.5 describe the phases; chapter 5 names the verifier's two.
- The peak heap of the mDoc flow (both circuits committed before either is proved) is measured in #126 with the real tools, against upstream's `heap_v7` in the same session (ADR 0067); the structure is upstream's, so no option is left to choose on this account.
- ADR 0049 carries a Status note to this record for the order of the checks.

## Verification impact

- The partitions `ligero-prover` (the prover instances), `verifier` and `protocol` (the glue) are proved again under unchanged settings. The new procedures are Silver with the ownership checks on `Committed` and `Received`; the contracts of the compositions are discharged from those of the phases. The counts are in the pull request.
- Tested: the byte identity of `sha256_proof.bin` and `ecdsa2_proof.bin` under the upstream seeds (the `cli` step); `prover_kat` on the statuses, including `not_satisfied` now found in the proving phase, and on the two phases themselves on every accepted case: two commitments, a draw, two proofs into one buffer, the two receipts at their offsets, the draw, the two verifications, then the second proof altered, the buffer cut short and the public inputs of the wrong count on both sides, each record freed; `writer_kat` through `Read_Proof`.

## References

- longfellow-zk/longfellow-zk at d5e6be7: `rust/runtime/zk/src/prover.rs` (`commit`, `prove`), `rust/runtime/zk/src/verifier.rs` (`recv_commitment`, `verify`), `rust/runtime/ligero/src/prover.rs` (`commit` writes the root), `rust/applications/mdoc_zk/runtime/src/prover.rs` (the order of the mDoc flow).
- [ADR 0028](0028-stage-4-scope-and-challenge-replay.md), [ADR 0047](0047-heap-allocation-by-ownership.md), [ADR 0049](0049-phase-c-scope-prover-and-exit-criterion.md), [ADR 0051](0051-constant-time-in-the-prover.md), [ADR 0058](0058-mdoc-layer.md).
- Chapter 4 Section 3.5, chapter 5 Section 3, chapter 7 Section 3.7.
