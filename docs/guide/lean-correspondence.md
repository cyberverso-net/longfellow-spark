# Correspondence with upstream's Lean proofs

Upstream proves the security of the Longfellow protocol in Lean. This project proves, in SPARK, that its own code has no run-time error and that its kernels compute the specification's formulas. This page shows how the two fit together, piece by piece, and what still connects them only by reading.

It is written for an evaluator who has to judge a chain of evidence from a formal model of the protocol down to the code that runs. The reference is longfellow-zk/longfellow-zk at 7bf8a6b (26 October 2026), directory `formal/`: in particular `formal/README.md`, `formal/AUDIT.md` and `formal/lfzk-v1/README.md`. Until 29 October this page followed d9d8d6a (16 October); the circuit premises below are the same at both commits, word for word.

## What upstream proves

Upstream's Lean development (Lean 4.31.0 with Mathlib) models the v7 mDoc protocol: the hash circuit over GF(2^128) and the signature circuit over the P-256 base field, on one Fiat-Shamir transcript, linked by a two-field MAC. Each circuit is a padded, layered sumcheck followed by Ligero V1 at rate 1/7 with 132 opened columns. This is the configuration this project implements, Longfellow V1. Upstream's V2 (projective sumcheck and Polygero) is a different protocol, not in any draft, and not implemented here.

| Property | Result in Lean | Theorem |
|----------|----------------|---------|
| Extraction and soundness of the pair of circuits, 1 to 4 attributes | 116-bit T-security: at most (1 + N + tA) / 2^116, for N transcript queries and tA Merkle queries | `LfzkV1.CompiledZk.v7Hash{1,2,3,4}_deployed_fs_extraction_116_circuit` and `..._false_statement_116`, all in the target `LfzkV1.FlatV7All` |
| Zero knowledge, 256-bit nonces | at most 2^-127 for the two fields, against 2^115 Merkle queries; the simulator receives the zero pattern of the six common message blocks | `CompiledLongfellowZkV7Mac.v7mac_twofield_zk_q115` |
| Zero knowledge, 542-bit nonces | statistical, at most 2^-131, with the same zero pattern | `CompiledLongfellowZkV7Mac.v7mac_twofield_zk_stat542` |
| Witness indistinguishability, 256-bit nonces | at most 2^-127 per side, 2^-126 for the two fields, for messages with equal zero patterns | `CompiledLongfellowZk.compiled_longfellow_wi`, `CompiledLongfellowZkV7Mac.twofield_wi_v7` |
| The ECDSA circuit | soundness and completeness of the signature circuit's verification | `ecdsa_circuit_soundness`, `ecdsa_circuit_completeness` (`formal/circuits/ECDSA/`) |

The earlier 115-bit results, per pair and per circuit, are still in the development: `CompiledZkProfileRows.v7P256Sha{1,2,3,4}_zk_circuit_tsec_sepMac`, `v7SigHahn_zk_circuit_tsec` (127 bits, the signature circuit alone) and `v7Hash{1,2,3,4}_zk_circuit_tsec` (115 bits, the hash circuit alone). The 116-bit endpoints supersede them as the headline.

The components behind the headline are proved too, among them: the sumcheck rounds and chains (`SumcheckV1.sumcheck_step_reduction`, `sumcheck_multi_reduction`, `sumcheck_multi_completeness`), the extraction of Ligero V1 (`Ligero.V1.scalarGap_extraction_failure`), the distance of the Reed-Solomon code (`ReedSolomon.evaluation_code_minimum_distance`) and the binding of Merkle prefixes (`Merkle.MH.PrefixBindingGame.bad_ratio_le`).

The proofs use only Lean's standard axioms, plus `native_decide` for the numerical rows of V1, as `formal/AUDIT.md` documents. Upstream's audit (`formal/scripts/Audit.lean` and `scripts/audit.rs`) finds no `sorry`, `admit` or `axiom`.

## Where the Lean proofs stop

The theorems are about a verifier written in Lean. To carry them over to real code, one needs the one-way implication "whenever the code accepts, the Lean verifier accepts the same statement and proof, with the same challenge distribution". Upstream keeps it as a premise: "Source-level equivalence to the Rust or C++ verifier is not proved." The premise `CircuitSide` holds what the code must agree on: the public-input maps, `CodeAgreesP`, the initial points, the message readers, the placement in the tableau, the domains and the size bounds.

The other premises upstream lists are:

- **The circuits.** `WellFormedP`, `Isolated` and `DeadEnd` hold on the registered circuits. Upstream checks them with Rust tools outside Lean, and the identification of the circuit files with Lean's `QuadCircuit` data is outside Lean too. This project checks `Isolated` and `DeadEnd` itself, when it loads a circuit.
- **The challenge sampler.** Each transcript answer is an ideal uniform coin, with exact balance for every decoder role. The correspondence with SHA-256, the AES expansion and the rejection samplers is not proved.
- **The hash model.** A Merkle random oracle and an independent transcript oracle.
- **The commitments and the transcript.** The byte encodings, the field arithmetic and the byte-level transcript are implementation obligations.
- **The MAC.** Each circuit enforces its own tag equation, tag = (av + share) · message, on the common value. This is a property of the circuits, assumed.

## The implementation obligations, and what this project proves of them

`formal/AUDIT.md` lists what the Lean theorems leave to the implementation. This is where this project's proofs meet upstream's.

| Obligation upstream leaves | Here |
|----------------------------|------|
| Limb arithmetic and overflow | Proved: both fields are Gold against reference models, and no run-time error occurs anywhere in the proved units (chapters 1 and 2). |
| Allocation bounds | Proved: the working sets are sized from the circuit and the geometry, and every index is in range (chapter 6). |
| Parser validation | Proved: the circuit reader, the proof reader and the Ligero reader return, on `Ok`, structures of the shape they promise (chapters 5 and 6). |
| Serialisation | Proved for the layout: the writers write exactly the proof's length, in the shape the readers accept (chapter 7). That they rewrite every proof identically is tested. |
| Domain and hash encodings | Proved for the layout of leaves and nodes, and for the frames of the transcript on a ghost sequence of the absorbed bytes (chapter 4); SHA-256 and AES-256 are tested against FIPS vectors. |
| The SHA and AES expansion and the rejection samplers | Tested byte for byte against Appendix B.2 and the upstream proofs; the ideal sampler stays an assumption, here as upstream. |
| Byte-level transcript equivalence | Tested: the replayed challenges match the upstream proofs byte for byte. |
| The registered circuit's semantics | Trusted, here as upstream: the circuit files are taken as to what they compute (ADR 0011). |

## The matrix

For each element of the Lean model, the unit of this project that implements it, and what connects the two. "Proved" means proved by GNATprove in this project; "by reading" means a reviewer compares the two definitions.

| Lean model | This project | Link |
|------------|--------------|------|
| `QuadCircuit`: layers of terms ⟨g, h0, h1, v⟩, `ninp`, `npub`; layer 0 is the output layer | `Sumcheck_Algebra.Circuit`, built by `Circuit_Reader.Read` from the LFC2 bytes | Proved: on `Ok`, the reader returns a well-formed circuit of this shape, with the premises `Isolated` and `Dead_End`, and its identifier recomputed from its terms (or, for a pinned file, the identifier of the list, ADR 0074). Tested, not proved: that the terms are the ones the bytes encode. The expansion of deltas, segments and tokens agrees with upstream on the vectors (ADR 0048), and the identifier relates the terms to a hash, not the bytes to the terms. Lean's premise "the circuit is the artifact's bytes" thus rests on a proved structure, a tested decoding, and an agreement of the two shapes checked by reading. |
| `WellFormed`: wire indices in range, `nv <= 2^logw`, `0 < npub <= ninp` | `Well_Formed`, the type predicate of `Circuit` | Proved, and stricter on the indices: each term reads only wires of its own layers. Not checked: `0 < npub` (see below). |
| `OneWire`: input wire 0 is the public constant 1 | `Zk_Verifier.Verify` (`Public_Input_Not_One`) and `Zk_Prover.Prove` (`Input_Not_One`) | Proved: each status is returned exactly when the circuit has public inputs and the first is not 1. A circuit without public inputs is accepted as upstream accepts it; its wire 0 is private, and such a circuit lies outside the Lean model. |
| `Isolated`: an assert-zero term is the only term on its output wire | `Circuit_Reader.Read` (`Not_Isolated`), against the ghost predicate `Isolated` | Proved: on `Ok` the circuit satisfies the predicate. The predicate transcribes Lean's definition; the agreement is by reading. |
| `DeadEnd`: no term reads an assert-zero wire of the layer below | `Circuit_Reader.Read` (`Not_Dead_End`), against the ghost predicate `Dead_End` | Proved, as for `Isolated`. |
| `Satisfied`: every assert-zero hand product is zero at the honest wires, every output is zero | `Eval_Circuit` (Gold): its status is "all Z assertions hold and every output is zero" | Proved against `Z_Ref` and `Layer_Holds`; the agreement with `Satisfied` is by reading. The factor order differs (we write w(h1) w(h0)), which is the same value. |
| Padded sumcheck rounds, p(1) := claim − p(0), no cleartext round check (`SumcheckV1.sumcheck_step_reduction`) | `Sumcheck_Verifier.Symbolic_Round` (Gold by definition) and `Verify_Layer` | Proved that the code computes this formula; agreement with the model by reading. |
| `begin_circuit` puts both claim points at G | `Verifier_Core`: the first `Claims_State` has HC0 = HC1 = G | By reading. |
| The next points are the interleaved even and odd challenges | `Verify_Layer`: even rounds feed HC0, odd rounds HC1 | By reading. |
| The layer coefficient `bind_gh_all` at the layer's own `beta`, assert-zero terms replaced by `beta` (`prep_v`) | `Bound_K` and `Eval_Bound_Quad` (Gold), and since Phase D `Eval_Bound_Quad_T` (Gold against the bindeq form of Section 6.2) and `Sumcheck_HQuad.Bind_Quad` (Gold against the same form, ADR 0073) | Proved against the formulas; the agreement of the bindeq form with eq is tested. |
| Each layer emits its finalize row and quadratic triple | `Verify_Layer` and `Lqc_Triples`; the pad layout `Lemma_Pads_Below` | Proved: the layout of the triples and the bounds on every emitted term. |
| The input row: the `alpha_in` combination of the two points' eq vectors, the public part folded in | `Input_Constraint` (Gold against `In_Coef` and `Pub_Binding_Ref`) | Proved against the formula; agreement with the model by reading. |
| The only verdict is Ligero V1's, on the system the transcript built | `Zk_Verifier.Verify`: the status is Ligero's, after the reader and the core | Proved: the status is tied to its cause. Our verifier also refuses malformed input before Ligero, which only strengthens the one-way implication. |
| Ligero V1: the low-degree, linear and quadratic tests; rate 1/7, 132 openings (`Ligero.V1.scalarGap_extraction_failure`) | `Ligero_Verifier` (the three tests Gold against Sections 4.4 and 4.5) and `Ligero_Geometry` | Proved against the specification's formulas; the parameters come from the configuration. |
| The Merkle opening check (`Merkle.MH.PrefixBindingGame`) | `Merkle.Verify` (Gold) | Proved against the node model. |
| The leaf codec: nonce ‖ column, 256-bit digests | `Ligero_Proof.Read`, the leaves of `Ligero_Verifier` and `Merkle` | Proved for the layout; SHA-256 itself is tested (FIPS vectors). |
| Fresh challenges, drawn in protocol order, never re-absorbed | `Transcript`, `Sumcheck_Transcript.Replay_Challenges` | The order is tested byte for byte against Appendix B.2 and the upstream proofs. The ideal sampler stays an assumption, here as upstream. |
| The two-field MAC, a private MAC witness per circuit, tag = (av + share) · message | not implemented yet: the mDoc layer of ADR 0058 | To follow upstream's `mac.rs` exactly (at d5e6be7 `rust/applications/mdoc_zk/runtime/src/mac.rs`, at 7bf8a6b `.../src/v1/mac.rs`), as the Lean proof requires: the old shared-blind argument fails for separate blinds (`SoundnessAudit.separate_blinds_collision`). |

## What this means for the trust model

The soundness and zero-knowledge theorems are no longer only "trusted": upstream proves them in Lean, for a model of the verifier this project implements. They stay listed as trusted for this project, because the link between that model and this code is the matrix above, and most of its rows are "by reading". The [trust model](trust-model.md) says so.

## What would close the gap

The three circuit premises `OneWire`, `Isolated` and `DeadEnd` are checked, with proved postconditions ([ADR 0064](../adr/0064-lean-circuit-premises.md)). What remains, in order of cost:

1. **Keep this matrix current.** Each change to the verifier, here or upstream, is checked against it, and each row names the definitions on both sides.
2. **A machine-checked link.** Express the ghost references of this project, the formulas its Gold contracts are proved against, as Lean definitions, and prove in Lean that they agree with upstream's model. That would discharge part of `CircuitSide` for this code, and it is research: a phase of its own.
