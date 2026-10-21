# Correspondence with upstream's Lean proofs

Upstream proves the security of the Longfellow protocol in Lean. This project proves, in SPARK, that its own code has no run-time error and that its kernels compute the specification's formulas. This page shows how the two fit together, piece by piece, and what still connects them only by reading.

It is written for an evaluator who has to judge a chain of evidence from a formal model of the protocol down to the code that runs. The reference is google/longfellow-zk at d9d8d6a (16 October 2026), directory `formal/`, in particular `formal/lfzk/README.md`. A copy of that README as it was read is kept with the project's notes.

## What upstream proves

Upstream's Lean development (Lean 4.31 with Mathlib) models the v7 mDoc protocol: the hash circuit over GF(2^128) and the signature circuit over the P-256 base field, on one Fiat-Shamir transcript, linked by a two-field MAC. Each circuit is a padded, layered sumcheck followed by Ligero V1 at rate 1/7 with 132 opened columns. This is the configuration this project implements.

| Property | Result in Lean | Theorem |
|----------|----------------|---------|
| Soundness of the pair of circuits, 1 to 4 attributes | at most (1 + tA + N) / 2^115, for tA Merkle queries and N transcript queries | `CompiledZkProfileRows.v7P256Sha{1,2,3,4}_zk_circuit_tsec_sepMac` |
| Soundness, signature circuit alone | 127 bits | `CompiledZkProfileRows.v7SigHahn_zk_circuit_tsec` |
| Soundness, hash circuit alone | 115 bits | `CompiledZkProfileRows.v7Hash{1,2,3,4}_zk_circuit_tsec` |
| Zero knowledge, 256-bit nonces | at most 2^-127 for the two fields, against 2^115 Merkle queries | `CompiledLongfellowZkV7Mac.v7mac_twofield_zk_q115` |
| Zero knowledge, 542-bit nonces | statistical, at most 2^-131 | `CompiledLongfellowZkV7Mac.v7mac_twofield_zk_stat542` |

The headline proofs use only Lean's standard axioms, plus `native_decide` for numeric facts. Upstream's audit script finds no `sorry`, `admit` or `axiom`.

## Where the Lean proofs stop

The theorems are about a verifier written in Lean, which transcribes upstream's C++ verifier `zk_common.h`. To carry them over to real code, one needs the one-way implication "whenever the code accepts, the Lean verifier accepts the same statement and proof, with the same challenge distribution". Upstream states this as an open premise: equivalence with the deployed verifier "is not proved from source or machine code". It names two ways to close it: a verified translation of the verifier, or a verifier generated from a verified executable definition.

The other premises upstream lists are:

- **The circuits.** `WellFormedP`, `Isolated` and `DeadEnd` hold on the registered circuits. Upstream checks them with Rust tools outside Lean, and the identification of the circuit files with Lean's `QuadCircuit` data is outside Lean too.
- **The challenge sampler.** Each transcript answer is an ideal uniform coin. The correspondence with SHA-256, the AES expansion and the rejection samplers is not proved.
- **The hash model.** A Merkle random oracle and an independent transcript oracle.
- **The commitments.** The byte encoding, the leaf as nonce and column, and the root as context are deployment obligations.
- **The MAC.** Each circuit asserts the MAC equation on its own private witness. This is a property of the circuits, assumed.

## The matrix

For each element of the Lean model, the unit of this project that implements it, and what connects the two. "Proved" means proved by GNATprove in this project; "by reading" means a reviewer compares the two definitions.

| Lean model | This project | Link |
|------------|--------------|------|
| `QuadCircuit`: layers of terms ⟨g, h0, h1, v⟩, `ninp`, `npub`; layer 0 is the output layer | `Sumcheck_Algebra.Circuit`, built by `Circuit_Reader.Read` from the LFC2 bytes | Proved: the reader returns, on `Ok`, a circuit of this shape with its identifier recomputed. Lean's own premise "the circuit is the artifact's bytes" is closed on our side by a proved parser; the agreement of the two shapes is by reading. |
| `WellFormed`: wire indices in range, `nv <= 2^logw`, `0 < npub <= ninp` | `Well_Formed`, the type predicate of `Circuit` | Proved, and stricter on the indices: each term reads only wires of its own layers. Not checked: `0 < npub`. |
| `OneWire`: input wire 0 is the public constant 1 | not checked | Open. Proposed: the verifier refuses a statement whose first public input is not `One`, with a proved postcondition. |
| `Isolated`: an assert-zero term is the only term on its output wire | not checked | Open. Proposed: a proved check in the loader. |
| `DeadEnd`: no term reads an assert-zero wire of the layer below | not checked | Open. Proposed: a proved check in the loader. |
| `Satisfied`: every assert-zero hand product is zero at the honest wires, every output is zero | `Eval_Circuit` (Gold): its status is "all Z assertions hold and every output is zero" | Proved against `Z_Ref` and `Layer_Holds`; the agreement with `Satisfied` is by reading. The factor order differs (we write w(h1) w(h0)), which is the same value. |
| Padded sumcheck rounds, p(1) := claim − p(0), no cleartext round check | `Sumcheck_Verifier.Symbolic_Round` (Gold by definition) and `Verify_Layer` | Proved that the code computes this formula; agreement with the model by reading. |
| `begin_circuit` puts both claim points at G | `Verifier_Core`: the first `Claims_State` has HC0 = HC1 = G | By reading. |
| The next points are the interleaved even and odd challenges | `Verify_Layer`: even rounds feed HC0, odd rounds HC1 | By reading. |
| The layer coefficient `bind_gh_all` at the layer's own `beta`, assert-zero terms replaced by `beta` (`prep_v`) | `Bound_K` and `Eval_Bound_Quad` (Gold), and since Phase D `Eval_Bound_Quad_T` (Gold against the bindeq form of Section 6.2) | Proved against the formulas; the agreement of the bindeq form with eq is tested. |
| Each layer emits its finalize row and quadratic triple | `Verify_Layer` and `Lqc_Triples`; the pad layout `Lemma_Pads_Below` | Proved: the layout of the triples and the bounds on every emitted term. |
| The input row: the `alpha_in` combination of the two points' eq vectors, the public part folded in | `Input_Constraint` (Gold against `In_Coef` and `Pub_Binding_Ref`) | Proved against the formula; agreement with the model by reading. |
| The only verdict is Ligero V1's, on the system the transcript built | `Zk_Verifier.Verify`: the status is Ligero's, after the reader and the core | Proved: the status is tied to its cause. Our verifier also refuses malformed input before Ligero, which only strengthens the one-way implication. |
| Ligero V1: the low-degree, linear and quadratic tests; rate 1/7, 132 openings | `Ligero_Verifier` (the three tests Gold against Sections 4.4 and 4.5) and `Ligero_Geometry` | Proved against the specification's formulas; the parameters come from the configuration. |
| The Merkle opening check | `Merkle.Verify` (Gold) | Proved against the node model. |
| The leaf codec: nonce ‖ column, 256-bit digests | `Ligero_Proof.Read`, the leaves of `Ligero_Verifier` and `Merkle` | Proved for the layout; SHA-256 itself is tested (FIPS vectors). |
| Fresh challenges, drawn in protocol order, never re-absorbed | `Transcript`, `Sumcheck_Transcript.Replay_Challenges` | The order is tested byte for byte against Appendix B.2 and the upstream proofs. The ideal sampler stays an assumption, here as upstream. |
| The two-field MAC, a private MAC witness per circuit | not implemented yet (Phase D, block 5) | To follow `mac.rs` exactly, as the Lean proof requires: the old shared-blind argument fails for separate blinds (`SoundnessAudit.separate_blinds_collision`). |

## What this means for the trust model

The soundness and zero-knowledge theorems are no longer only "trusted": upstream proves them in Lean, for a model of the verifier this project implements. They stay listed as trusted for this project, because the link between that model and this code is the matrix above, and most of its rows are "by reading". The [trust model](trust-model.md) says so.

## What would close the gap

In order of cost:

1. **Prove the circuit premises in SPARK.** `OneWire`, `Isolated` and `DeadEnd` are simple decidable properties. Checking them in the loader and the verifier, with proved postconditions, turns three rows from "open" into "proved".
2. **Keep this matrix current.** Each change to the verifier, here or upstream, is checked against it, and each row names the definitions on both sides.
3. **A machine-checked link.** Express the ghost references of this project, the formulas its Gold contracts are proved against, as Lean definitions, and prove in Lean that they agree with upstream's model. That is the "verified executable definition" route upstream names, and it is research: a phase of its own, after the current one.
