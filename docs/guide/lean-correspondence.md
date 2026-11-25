# Correspondence with upstream's Lean proofs

Upstream proves the security of the Longfellow protocol in Lean. This project proves, in SPARK, that its own code has no run-time error and that its kernels compute the specification's formulas. This page shows how the two fit together, piece by piece, and what still connects them only by reading.

It is written for an evaluator who has to judge a chain of evidence from a formal model of the protocol down to the code that runs. The reference is longfellow-zk/longfellow-zk at 7bf8a6b (26 October 2026), directory `formal/`: in particular `formal/README.md`, `formal/AUDIT.md` and `formal/lfzk-v1/README.md`. The circuit premises below are word for word those of the earlier commit d9d8d6a.

**Before reading:** the primer's account of how strong the guarantee is ([A11.4](00-primer-cryptography.md#a114-how-strong-is-the-guarantee)) and the register's rows S1 and S2 ([the trusted base register](trusted-base.md)).

## What upstream proves

Upstream's Lean development (Lean 4.31.0 with Mathlib) models the v7 mDoc protocol: the hash circuit over GF(2^128) and the signature circuit over the P-256 base field, on one Fiat-Shamir transcript, linked by a two-field MAC. Each circuit is a padded, layered sumcheck followed by Ligero V1 at rate 1/7 with 132 opened columns. This is the configuration this project implements, Longfellow V1. Upstream's V2 (projective sumcheck and Polygero) is a different protocol, not in any draft, and not implemented here.

The notions of the table, in the primer:

- **soundness and extraction**, and what a bound such as (1 + N + tA) / 2^116 means as bits of security: [A11.4](00-primer-cryptography.md#a114-how-strong-is-the-guarantee), with the cheating prover of [A12.1](00-primer-cryptography.md#a121-the-cheating-prover);
- **zero knowledge** and the zero pattern of the six message blocks: [A11.4](00-primer-cryptography.md#a114-how-strong-is-the-guarantee) and [A12.2](00-primer-cryptography.md#a122-the-curious-verifier);
- **witness indistinguishability**, a weaker property than zero knowledge: two proofs made from two witnesses with the same zero pattern cannot be told apart, though nothing says the proof could be imitated without a witness;
- **what a Lean theorem is**, what makes it trustworthy, and how its chain of evidence meets this project's SPARK proofs: [B8.1, B8.2 and B8.5](00-primer-spark.md#b8-lean-and-spark-two-kinds-of-proof), with the rule on `native_decide` in [B8.6](00-primer-spark.md#b86-the-rule-on-native_decide-and-upstreams-own-evidence).

| Property | Result in Lean | Theorem |
|----------|----------------|---------|
| Extraction and soundness of the pair of circuits, 1 to 4 attributes | 116-bit T-security: at most (1 + N + tA) / 2^116, for N transcript queries and tA Merkle queries | `LfzkV1.CompiledZk.FlatV7Headline.v7Hash1_deployed_fs_extraction_116_circuit` and `LfzkV1.CompiledZk.FlatV7Headline.v7Hash1_deployed_fs_false_statement_116` for one attribute, the same pair under `FlatV7Hash2Headline`, `FlatV7Hash3Headline` and `FlatV7Hash4Headline` (`v7Hash2` to `v7Hash4`) for two to four, all in the target `LfzkV1.FlatV7All` |
| Zero knowledge, 256-bit nonces | at most 2^-127 for the two fields, against 2^115 Merkle queries; the simulator receives the zero pattern of the six common message blocks | `CompiledLongfellowZkV7Mac.v7mac_twofield_zk_q115` |
| Zero knowledge, 542-bit nonces | statistical, at most 2^-131, with the same zero pattern | `CompiledLongfellowZkV7Mac.v7mac_twofield_zk_stat542` |
| Witness indistinguishability, 256-bit nonces | at most 2^-127 per side, 2^-126 for the two fields, against 2^115 Merkle queries, for messages with equal zero patterns | `CompiledLongfellowZk.compiled_longfellow_wi`, `CompiledLongfellowZkV7Mac.twofield_wi_v7` |
| The ECDSA circuit | stated: soundness and completeness of the signature circuit's verification; at 7bf8a6b the two theorems hold only vacuously on real keys (the note below) | `ecdsa_circuit_soundness`, `ecdsa_circuit_completeness` (`formal/circuits/ECDSA/`) |

**The ECDSA row, read with care.** At 7bf8a6b the specification `StandardEcdsaVerify` (`formal/circuits/ECDSA/EcdsaSpec.lean`) and the hypothesis `h_pk_order` of the soundness theorem compare `[order]·PK` with the point at infinity by structural equality, `(0, 1, 0)`, where the curve operations leave a projective point `(0, Y, 0)` with Y other than 1. For a real P-256 key the premise is therefore false and the two theorems hold vacuously (upstream's issue 224, 3 November 2026). Upstream's pull requests 225 and 215 replace the equality with the projective equivalence `ProjectiveEquiv`. Neither is merged at 7bf8a6b, nor at 1c06629, the head of upstream's main read on 14 November 2026, where `EcdsaSpec.lean` still compares with `infinityPoint`. So this row is no evidence: what covers the signature circuit is this project's Gold proof that a circuit is evaluated as its terms say, and the upstream proofs and vectors it reproduces; what the circuit computes stays trusted (register row R2, ADR 0011). The row is reread at their merge (issue #122).

The earlier 115-bit results, per pair and per circuit, are also in the development: `CompiledZkProfileRows.v7P256Sha{1,2,3,4}_zk_circuit_tsec_sepMac`, `v7SigHahn_zk_circuit_tsec` (127 bits, the signature circuit alone) and `v7Hash{1,2,3,4}_zk_circuit_tsec` (115 bits, the hash circuit alone). The 116-bit endpoints supersede them as the headline.

The components behind the headline are proved too, among them: the sumcheck rounds and chains (`SumcheckV1.sumcheck_step_reduction`, `sumcheck_multi_reduction`, `sumcheck_multi_completeness`), the extraction of Ligero V1 (`Ligero.V1.scalarGap_extraction_failure`), the distance of the Reed-Solomon code (`ReedSolomon.evaluation_code_minimum_distance`) and the binding of Merkle prefixes (`Merkle.MH.PrefixBindingGame.bad_ratio_le`).

The proofs use only Lean's standard axioms, plus `native_decide` for the numerical rows of V1, as `formal/AUDIT.md` documents. Upstream's audit (`formal/scripts/Audit.lean` and `scripts/audit.rs`) finds no `sorry`, `admit` or `axiom`.

## Where the Lean proofs stop

The theorems are about a verifier written in Lean. To carry them over to real code, one needs the one-way implication "whenever the code accepts, the Lean verifier accepts the same statement and proof, with the same challenge distribution". Upstream keeps it as a premise: "Source-level equivalence to the Rust or C++ verifier is not proved." The premise `CircuitSide` holds what the code must agree on: the public-input maps, `CodeAgreesP`, the initial points, the message readers, the placement in the tableau, the domains and the size bounds.

The other premises upstream lists are:

- **The circuits.** `WellFormedP`, `Isolated` and `DeadEnd` hold on the registered circuits. Upstream checks them with Rust tools outside Lean, and the identification of the circuit files with Lean's `QuadCircuit` data is outside Lean too. This project checks `Isolated` and `DeadEnd` itself, when it loads a circuit.
- **The challenge sampler.** Each transcript answer is an ideal uniform coin, with exact balance for every decoder role. The correspondence with SHA-256, the AES expansion and the rejection samplers is not proved (register row S2).
- **The hash model.** A Merkle random oracle and an independent transcript oracle (register row S2).
- **The commitments and the transcript.** The byte encodings, the field arithmetic and the byte-level transcript are implementation obligations.
- **The MAC.** Each circuit enforces its own tag equation, tag = (av + share) · message, on the common value. This is a property of the circuits, assumed (register row R2). The end-to-end statement adds a condition on the key: the MAC key share `av` supplied with the proof is the transcript oracle's answer at the two Merkle roots (the Lean reading notes `kmac`, `hmac`: the share is decoded from the answer at the key point, balanced over 2^128 values). In words: the key is drawn from the transcript after both commitments, so that neither circuit's prover can choose it after seeing the other. This is an obligation of the mDoc layer: the prover derives `av` from the transcript at the two roots as `mac.rs` does, and the verifier recomputes it there; the correspondence table carries it in the MAC row.

## The implementation obligations, and what this project proves of them

`formal/AUDIT.md` lists what the Lean theorems leave to the implementation. This is where this project's proofs meet upstream's.

| Obligation upstream leaves | Here |
|----------------------------|------|
| Limb arithmetic and overflow | Proved: both fields are Gold against reference models, and no run-time error occurs anywhere in the proved units (chapters 1 and 2). |
| Allocation bounds | Proved: the working sets are sized from the circuit and the geometry, and every index is in range (chapter 6). |
| Parser validation | Proved: the circuit reader, the proof reader and the Ligero reader return, on `Ok`, structures of the shape they promise (chapters 5 and 6). |
| Serialisation | Proved for the layout: the writers write exactly the proof's length, in the shape the readers accept (chapter 7). That they rewrite every proof identically is tested. |
| Domain and hash encodings | Proved for the layout of leaves and nodes, and for the frames of the transcript on a ghost sequence of the absorbed bytes (chapter 4); SHA-256 and AES-256 are tested against FIPS vectors (register row V1). |
| The SHA and AES expansion and the rejection samplers | Tested byte for byte against Appendix B.2 and the upstream proofs; the ideal sampler stays an assumption, here as upstream (register row S2). |
| Byte-level transcript equivalence | Tested: the replayed challenges match the upstream proofs byte for byte (register row S3). |
| The registered circuit's semantics | Trusted, here as upstream: the circuit files are taken as to what they compute (register row R2, ADR 0011). |

## The matrix

For each element of the Lean model, the unit of this project that implements it, and what connects the two. "Proved" means proved by GNATprove in this project; "by reading" means a reviewer compares the two definitions.

| Lean model | This project | Link |
|------------|--------------|------|
| `QuadCircuit`: layers of terms ⟨g, h0, h1, v⟩, `ninp`, `npub`; layer 0 is the output layer | `Sumcheck_Algebra.Circuit`. The verifier and the prover load the packed form, `Packed_Circuits.Packed_Circuit`, with `Circuit_Reader.Read_Packed` from the LFC2 bytes, and the circuit of the model is its ghost expansion `Expand (P)` (ADR 0080); `Circuit_Reader.Read`, the expanded circuit, is the oracle of the tests | Proved: on `Ok`, `Read_Packed` returns a valid packed form whose expansion is a well-formed circuit of this shape, with the premises `Isolated` and `Dead_End`, and its identifier recomputed from the walk of its terms (or, for a pinned file, the identifier of the list, ADR 0074); `Read` proves the same on the circuit it returns, and `Read_Packed` is tested against it term for term on every shipped circuit. Tested, not proved: that the terms are the ones the bytes encode. The expansion of deltas, segments and tokens agrees with upstream on the vectors (ADR 0048), and the identifier relates the terms to a hash, not the bytes to the terms. Lean's premise "the circuit is the artifact's bytes" thus rests on a proved structure, a tested decoding, and an agreement of the two shapes checked by reading. |
| `WellFormed`: wire indices in range, `nv <= 2^logw`, `0 < npub <= ninp` | `Well_Formed`, the type predicate of `Circuit`, stated on `Expand (P)` by the postcondition of `Read_Packed` and asked of it, at level `Proof_Only`, by `Zk_Verifier.Verify` and `Zk_Prover.Prove`; the sizes the two programs compute come from `Shape_Of (P)`, proved to satisfy `Shape_Ok`, the part of `Well_Formed` that names no term | Proved, and stricter on the indices: each term reads only wires of its own layers. Not checked: `0 < npub` (see below). |
| `OneWire`: input wire 0 is the public constant 1 | `Zk_Verifier.Verify` (`Public_Input_Not_One`) and `Zk_Prover.Prove` (`Input_Not_One`) | Proved: each status is returned exactly when the circuit has public inputs and the first is not 1. A circuit without public inputs is accepted as upstream accepts it; its wire 0 is private, and such a circuit lies outside the Lean model. |
| `Isolated`: an assert-zero term is the only term on its output wire | `Circuit_Reader.Read_Packed` and `Read` (`Not_Isolated`), against the ghost predicate `Isolated`, on `Expand (P)` for the packed form | Proved: on `Ok` the circuit, or the expansion, satisfies the predicate. The predicate transcribes Lean's definition; the agreement is by reading. |
| `DeadEnd`: no term reads an assert-zero wire of the layer below | `Circuit_Reader.Read_Packed` and `Read` (`Not_Dead_End`), against the ghost predicate `Dead_End` | Proved, as for `Isolated`. |
| `Satisfied`: every assert-zero hand product is zero at the honest wires, every output is zero | `Packed_Eval.Eval_Circuit` (Gold), the prover's evaluation of the packed circuit from the walk: its status is "all assertions hold and every output is zero", stated on `Expand (P)` (ADR 0080). The expanded `Eval_Circuit` of `Sumcheck_Algebra` (Gold against the same references) is the oracle `prover_kat` compares it with | Proved against `Z_Ref` and `Layer_Holds` on the expansion; the agreement with `Satisfied` is by reading. The factor order differs (we write w(h1) w(h0)), which is the same value. |
| Padded sumcheck rounds, p(1) := claim − p(0), no cleartext round check (`SumcheckV1.sumcheck_step_reduction`) | `Sumcheck_Verifier.Symbolic_Round` (Gold by definition) and `Verify_Layer` | Proved that the code computes this formula; agreement with the model by reading. |
| `begin_circuit` puts both claim points at G | `Verifier_Core`: the first `Claims_State` has HC0 = HC1 = G | By reading. |
| The next points are the interleaved even and odd challenges | `Verify_Layer`: even rounds feed HC0, odd rounds HC1 | By reading. |
| The layer coefficient `bind_gh_all` at the layer's own `beta`, assert-zero terms replaced by `beta` (`prep_v`) | `Bound_K` and `Eval_Bound_Quad` (Gold), and `Eval_Bound_Quad_T` (Gold against the bindeq form of Section 6.2). The verifier computes them from the packed form with `Zk_Verifier.Bound_Quads`, through `Packed_HQuad.Bind_Quad_Packed` and `Eval_Bound_Quad_Packed` (Gold against the same references on the layer of `Expand (P)`, ADR 0080, ADR 0073); the prover takes them from its own sumcheck, `Sumcheck_Prover.Prove` on the packed circuit, through `Bind_Merge` and the rounds (ADR 0071). Each result is proved equal to `BQ_Ref` on `Expand (P)` and asserted at the two calls of `Verifier_Core` | Proved against the formulas; the agreement of the bindeq form with eq is tested (register row V9), and the packed path is tested against `Eval_Bound_Quad` and `Eval_Bound_Quad_T` on the expanded layers in `sumcheck_kat`, `circuit_kat` and `first_step_bench --check`. |
| Each layer emits its finalize row and quadratic triple | `Verify_Layer` and `Lqc_Triples`; the pad layout `Lemma_Pads_Below` | Proved: the layout of the triples and the bounds on every emitted term. |
| The input row: the `alpha_in` combination of the two points' eq vectors, the public part folded in | `Input_Constraint` (Gold against `In_Coef` and `Pub_Binding_Ref`) | Proved against the formula; agreement with the model by reading. |
| The only verdict is Ligero V1's, on the system the transcript built | `Zk_Verifier.Verify`: the status is Ligero's, after the reader and the core | Proved: the status is tied to its cause. Our verifier also refuses malformed input before Ligero, which only strengthens the one-way implication. |
| Ligero V1: the low-degree, linear and quadratic tests; rate 1/7, 132 openings (`Ligero.V1.scalarGap_extraction_failure`) | `Ligero_Verifier` (the three tests Gold against Sections 4.4 and 4.5) and `Ligero_Geometry` | Proved against the specification's formulas; the parameters come from the configuration. |
| The Merkle opening check (`Merkle.MH.PrefixBindingGame`) | `Merkle.Verify` (Gold) | Proved against the node model. |
| The leaf codec: nonce ‖ column, 256-bit digests | `Ligero_Proof.Read`, the leaves of `Ligero_Verifier` and `Merkle` | Proved for the layout; SHA-256 itself is tested (FIPS vectors, register row V1). |
| Fresh challenges, drawn in protocol order, never re-absorbed | `Transcript`, `Sumcheck_Transcript.Replay_Challenges` | The order is tested byte for byte against Appendix B.2 and the upstream proofs. The ideal sampler stays an assumption, here as upstream (register row S2). |
| The two-field MAC, a private MAC witness per circuit, tag = (av + share) · message; the key share `av` is the transcript oracle's answer at the two Merkle roots (the conjunct of the end-to-end statement, `v7P256Sha{1,2,3,4}_zk_circuit_tsec_sepMac`) | `Mdoc_Mac.Legacy_Tags` (the six tags, upstream's `push_legacy_macs` of `mac.rs` at d5e6be7), `Mdoc_Prover` and `Mdoc_Verifier`: av drawn from the transcript after both roots, each circuit with its own copy of the pads in its witness (chapter 9 Section 1.3) | Proved: the six products of the tag equation (Gold). By reading and tested: the order of the two commitments before av in both roles (ADR 0085, Silver on the phases; no contract states the absorbed transcript). Tested: the proofs made here are accepted by upstream's verifier and upstream's example proofs by this one (the cross-check, chapter 9 Section 5.1). The correspondence with the model's MAC is by reading, as the rest of this page: upstream's audit records that the older shared-blind argument fails for separate blinds (`SoundnessAudit.separate_blinds_collision`), and the model's statement is the one with separate blinds. |

## This project's own Lean proofs

Besides upstream's development, `lean/` holds a small Lean development of this project's own (chapter 10 Section 2). It proves two facts of the gadgets of the hash circuit that the SPARK solvers cannot reach, because they are facts of the product of GF(2^128): an output of the plucker whose assertion holds is a bit (G1), and the assertion `assert_eqmod` of 1 to 7 words of bits holds exactly when their sum modulo 2^32 is the asserted word (G3). The second rests on the order of x in the field, 2^128 - 1, which the development proves by computation in Lean's kernel.

**A departure from the pin.** The order of x is proved with five declarations of upstream's `formal/lfzk-v2/LfzkV2/Current/GeneratorChecks.lean` and the helpers of `formal/circuits/ECDSA/PowMod.lean` they use, ported into `lean/Upstream/` with their statements unchanged and their provenance in each file. They are taken from upstream's commit 6ef3c750 (15 November 2026), on its main branch at 1424f50e, not from the pin 7bf8a6b, because they do not exist at the pin. The rest of this page keeps the pin.

The SPARK proof cites the two facts through bridges (register rows L3 and L4). A bridge is checked by reading: its contract must state the Lean theorem. To keep that reading short, the Lean theorems are stated over a model of the field over `Nat`, in the same bit-level terms as `GF2_128`, and the step from that model to the field `AdjoinRoot P` of Mathlib is proved in Lean (`LongfellowSpark.GF128.ev`, an injective homomorphism below 2^128). The tables below give the reading, one row per definition.

**The field.**

| SPARK (`src/gf2_128.ads`, `src/gadgets*.ads`) | Lean (`lean/LongfellowSpark/GF128.lean`, `Model.lean`) | The same because |
|---|---|---|
| An `Element`: two limbs of 64 bits, bit I of the 128 the coefficient of x^I | A number below 2^128, bit I the coefficient of x^I (`toPoly`) | The same bits in the same order: limb 0 is bits 0 to 63 |
| `GF2_128.Add`: the limb-wise xor | `^^^` | xor of the same bits |
| `GF2_128.Mul`, proved equal to `Mul_Ref`: the product of the two polynomials reduced by x^128 = x^7 + x^2 + x + 1 (MSB-first Horner, each step `Xtime`) | `GF128.mul`: the carry-less product (`clmulAux`), then two folds by 0x87 | Two definitions of the product of GF(2)[x] / (x^128 + x^7 + x^2 + x + 1); the vectors of `lean/scripts/Vectors.lean` (`tests/vectors/lean_gf2_128.txt`, regenerated and compared by the step `lean`) agree with `GF2_128.Mul` in `gadgets_kat` |
| `Zero`, `One`, `Gadgets.X` | `0`, `1`, `2` | The polynomials 0, 1 and x |

**G1, `Gadgets.Bits.Lemma_Output_Is_Bit` and `LongfellowSpark.Model.output_is_bit`.**

| SPARK | Lean |
|---|---|
| `Pre => Bit_Assertion (V) = Zero`, with `Bit_Assertion (V) = Add (V, Mul (V, V))` | `h : v ^^^ mul v v = 0` |
| `V : Element` | `hv : v < 2 ^ 128` |
| `Post => Is_Bit (V)`, `V = Zero or else V = One` | `v = 0 ∨ v = 1` |

**G3, `Gadgets.Words.Lemma_Assert_Eqmod` and `LongfellowSpark.Model.assert_eqmod`.**

| SPARK | Lean |
|---|---|
| `Alpha_2 (I)`: `X` squared I times (`Mul (P, P)`) | `alpha2 i`: `2` squared i times (`mul b b`) |
| `Shift (I)`: `Mul (Alpha_2 (32), Shift (I - 1))`, `One` for 0 | `shift i`: `mul (alpha2 32) (shift (i - 1))`, `1` for 0 |
| `Factor (I, B) = Add (One, Mul (B, Add (Alpha_2 (I), One)))` | `factor i b = 1 ^^^ mul b (alpha2 i ^^^ 1)` |
| `Encode (W)`: `Encode_Upto (W, 32)`, one factor at a time from `One` | `encode bits = prodN 32 (fun i => factor i (bits i))` |
| `Product_Upto (L, K)`: the K words' elements, one at a time | `prodN k (fun j => encode (words j))` |
| `Assertion (L, K, A)`: the product over I < K of `Add (Product_Upto (L, K), Mul (Shift (I), Encode (A)))` | `assertion k words abits = prodN k (fun i => prodN k (...) ^^^ mul (shift i) (encode abits))` |
| `Value (W)`: the sum of `Pow2 (I)` over the bits I equal to `One` | `value bits = ∑ i < 32, if bits i = 1 then 2 ^ i else 0` |
| `Sum_Upto (L, K)`: the sum of the K values | `sumN k words = ∑ j < k, value (words j)` |
| `K : Term_Count`, 1 to 7 | `hk : 0 < k`, `hk7 : k ≤ 7` |
| `Pre => All_Bits (L, K) and then All_Bits (A)` | `hw : ∀ j < k, ∀ i < 32, words j i = 0 ∨ words j i = 1`, `ha : ∀ i < 32, abits i = 0 ∨ abits i = 1` |
| `Post => (Assertion (L, K, A) = Zero) = (Sum_Upto (L, K) mod 2 ** 32 = Value (A))` | `assertion k words abits = 0 ↔ sumN k words % 2 ^ 32 = value abits` |

Word J of the list `L` is `words j`, bit I of a word is `bits i`; the words past K are not read on either side.

## What this means for the trust model

The soundness and zero-knowledge theorems are not only trusted: upstream proves them in Lean, for a model of the verifier this project implements. They stay listed as trusted for this project (register row S1), because the link between that model and this code is the matrix above, and most of its rows are "by reading". The [trust model](trust-model.md) says so.

## What would close the gap

The three circuit premises `OneWire`, `Isolated` and `DeadEnd` are checked, with proved postconditions ([ADR 0064](../adr/0064-lean-circuit-premises.md)). What remains, in order of cost:

1. **Keep this matrix current.** Each change to the verifier, here or upstream, is checked against it, and each row names the definitions on both sides.
2. **A machine-checked link.** Express the ghost references of this project, the formulas its Gold contracts are proved against, as Lean definitions, and prove in Lean that they agree with upstream's model. That would discharge part of `CircuitSide` for this code, and it is research: a phase of its own.
