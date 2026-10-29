# 0064 The circuit premises of upstream's Lean proofs, checked and proved

## Status

Accepted (2026-10-21, with the pull request that realises it). Amended 2026-10-29 by [ADR 0079](0079-specification-migrated-to-draft-irtf-cfrg-longfellow-00.md): the Lean reference is 7bf8a6b, where the circuit premises are in `formal/lfzk-v1/LfzkV1/ConcreteCircuit.lean` (the path below should read `formal/lfzk/Lfzk/` at d9d8d6a).

## Date

2026-10-21

## Context

Upstream proves the soundness and zero knowledge of the protocol in Lean (`formal/` at d9d8d6a). The [correspondence page](../guide/lean-correspondence.md) lists what those theorems assume about the circuit and the statement. Three of these premises are simple decidable properties that this project did not check:

- **`OneWire`**: input wire 0 is the public constant 1. The Lean construction copies the inputs down through this wire, so the soundness theorems need it.
- **`Isolated`**: an assert-zero term (a term whose constant is 0) is the only term on its output wire.
- **`DeadEnd`**: no term reads an assert-zero wire of the layer below.

Lean needs `Isolated` and `DeadEnd` only to characterise the circuits the compiler emits (`unsat_iff`): with them, an unsatisfied circuit moves the verifier's claim with the layer's random `beta`. Upstream checks the two on its registered circuits with Rust tools outside Lean.

All the circuits this project uses satisfy the three, checked by a script on the files:

- the two upstream interop circuits (sha256, ecdsa2);
- the four mDoc circuits (hash and signature, two versions);
- the three synthetic circuits of the vectors.

On every public input list in the vectors, the first element is 1. The two interop circuits have no public input: their wire 0 is private, and Lean's `WellFormed` (which asks `0 < npub`) does not cover them.

## Decision

- **The reader checks `Isolated` and `DeadEnd`.** After `Well_Formed`, `Circuit_Reader.Read` refuses a circuit with an assert-zero term that shares its wire (new status `Not_Isolated`) or with a term that reads an assert-zero wire of the layer below (new status `Not_Dead_End`). The check is linear in the terms: per layer, one array records the assert-zero term of each wire.
- **The verifier and the prover check `OneWire`.** When the circuit has public inputs, `Zk_Verifier.Verify` refuses a statement whose first public input is not 1 (new status `Public_Input_Not_One`). `Zk_Prover.Prove` refuses the same inputs (new status `Input_Not_One`).
- **Circuits without public inputs are accepted as today.** Their wire 0 is private, so the verifier cannot check it. The correspondence page says that such a circuit lies outside the Lean model.
- **Proved.** The two predicates are ghost functions of the reader, at the `Proof_Only` level: quantified, quadratic, never executed. The postcondition of `Read` gives them on `Ok`. The postconditions of `Verify` and `Prove` tie each new status exactly to its cause.

## Alternatives considered

- **Refuse also when there is no public input.** It matches Lean's `WellFormed`, but it breaks the interop with the two upstream test circuits, which upstream accepts.
- **A separate predicate, reported by the command-line tools.** It leaves the verdict of `Verify` unchanged, but it leaves the premise with the caller, which is where it was.
- **Leave the premises open.** Upstream's own position. It costs nothing, but the evaluator then has to trust three properties that the code can check in linear time.

## Consequences

- `Circuit_Status`, `Verifier_Status` and `Prover_Status` each gain values. Every place that names a status gets them: the readers' vectors, the harnesses, the command-line tools and the guide.
- This project is stricter than upstream in three places. Each is listed where the status is described.
- The rows `OneWire`, `Isolated` and `DeadEnd` of the correspondence matrix move from "open" to "proved", with the exception for circuits without public inputs.

## Verification impact

Proved: on `Ok`, the loaded circuit satisfies `Isolated` and `DeadEnd`; `Verify` returns `Public_Input_Not_One` exactly when the circuit has public inputs, their count is right and the first is not 1; `Prove` likewise for `Input_Not_One`. Tested: one negative vector for each new status. Trusted: nothing new.

## References

- [Correspondence with upstream's Lean proofs](../guide/lean-correspondence.md).
- Upstream `formal/lfzk/LongfellowZk/ConcreteCircuit.lean` at d9d8d6a: `OneWire`, `Isolated`, `DeadEnd`, `unsat_iff`.
- [ADR 0046](0046-phase-b-scope-lfc2-loader-and-interop.md) (the loader and its statuses), [ADR 0039](0039-sizes-allocation-and-status.md) (the verifier's statuses), [ADR 0049](0049-phase-c-scope-the-prover.md) (the prover's).
