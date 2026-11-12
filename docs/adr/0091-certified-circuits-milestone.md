# 0091 Certified circuits: a proved checker for the registered circuits, with two proof backends

## Status

Proposed (2026-11-12, with #89, from the feasibility study of #88). Amends [ADR 0082](0082-order-after-the-memory-milestone.md): the milestone comes after the guide for the evaluator and before the certification block.

## Date

2026-11-12

## Context

**The row that stays trusted.** The trust model lists the circuit files as trusted: this project proves that it evaluates a circuit as the specification says (`Eval_Circuit`, chapter 3), not what the registered circuit itself accepts. Upstream's Lean development says the same from the other side. `formal/AUDIT.md` (7bf8a6b) states that "the individual registered application's circuit semantics must also be related to the modeled trusted circuit". So an evaluator who accepts every proof of this project and every theorem of upstream still has to take on trust that the hash circuit checks a SHA-256 of a signed MSO, and the signature circuit an ECDSA signature.

**Why the circuit cannot simply be reread.** The registered files are the output of an optimising generator:

- common subexpressions are shared;
- constants are folded and factors absorbed;
- copies are inserted and the wires renumbered by the scheduler.

The boundaries of the gadgets do not survive in the terms. A check that reads ranges of terms as gadgets would be fragile; a check of what each wire means is not.

**What the feasibility study found (#88).**

- **The generator.** The version 7 pair was produced by upstream's C++ `circuit_maker` at 0d92f80c (12 January 2026, `lib/circuits/mdoc/`), not by the Rust compiler. It regenerates byte for byte at 0d92f80c and at d5e6be7, on arm64 and on x86-64.
- **The map of the wires.** An instrumented copy of the generator still writes the registered files byte for byte and maps every one of the 3,366,957 wires of the hash circuit to its gadget and call: 57.8 % one gadget node, 21.0 % shared, 6.0 % copies, 15.2 % rewritten, none without a source. The certificate can be extracted from the generator; a matcher that reconstructs the map from the terms is not needed.
- **The meanings.** A wire's meaning is a linear form with constant coefficients over declared wires. On the hash circuit the forms name at most 3 declared wires, and only on SHA-256. On the signature circuit they name at most 2, apart from the reconstruction of the two scalars from their 256 bits. The compiler absorbs at most 12 factors into one node of the hash circuit, and 512 in the signature circuit.
- **The local check.** Its lemma is proved in SPARK: if a certificate's map from the pairs of a product of two forms to a wire's terms passes an executable check, then the terms' sum is the product of the forms, for every assignment of the wires. Normalising a product of forms of length k costs k × k pairs.
- **The algebra of the gadgets.** What the gadgets compute are theorems of algebra over finite fields: words encoded in the multiplicative group, orders of elements, a Karatsuba product, the formulas of the curve. The SMT solvers behind GNATprove do not reach them. Lean 4 with Mathlib does: the lemma of `BitAdderAux` took 84 lines of code, with no `sorry` and no `native_decide`.
- **The signature circuit.** It needs gadget semantics beyond local identities. Upstream's `formal/circuits/ECDSA` models `verify_circuit.h` at the level of its gadgets, with a soundness theorem. At 7bf8a6b that theorem is vacuous (upstream issue 224); upstream's pull requests 225 and 215 fix it, and #122 tracks them.
- **The specification.** Chapter 9 Section 6, "Conditions for certifying the circuit", reads both circuits' assertions from the generator line by line. It states the conditions on the issuer, on the relying party and on the circuit under which the pair's guarantee holds.

## Decision

**A milestone, "Certified circuits": a proved checker that takes the registered circuit files as they are, with an untrusted certificate, and establishes what each circuit accepts.**

**The target.** The version 7 one-attribute pair `8d079211…`, the pair upstream's Lean certificates cover. The perimeter is the EU age-verification profile: one namespace, one attribute.

**The theorem.** If the checker accepts the circuit C with the certificate K, then for every public input x and witness w, `Eval_Circuit (C, x, w) = Ok` implies `Relation (x, w)`, the relation of the specification. A wrong or hostile certificate makes the checker refuse; it never accepts by mistake, because the implication is proved for every C and K. Completeness, that every valid credential is accepted, stays tested.

**The pieces.**

1. **The relation specification**, ghost SPARK, one per circuit, at the level of bytes, words and field elements, with the list of public inputs and their meaning. The table "Conditions for certifying the circuit" of chapter 9 Section 6 is part of it. Each condition on the issuer or on the relying party is a hypothesis of the theorem, stated as such. Each condition on the circuit is either established by the checker or stated as a hypothesis.
2. **The reference netlist**, SPARK, Gold: the relation in straight-line form at word and bit level, proved equal to the specification.
3. **The certificate**, data, untrusted, emitted by the instrumented generator.
4. **The checker**, SPARK: Silver on any bytes and any certificate, Gold on the theorem. It walks the circuit in layer order and checks one local identity per wire. Each identity uses the lemma of the gadget type the certificate names for that wire.
5. **The evidence**: a command-line tool that prints the verdict with the circuit's identifier, its run in the gate, the chapters for the evaluator, the trust model and the register.

**Two proof backends, with one rule.** SPARK proves the structure, and Lean proves the algebra:

- Lean proves algebra only, never structure.
- The SPARK checker is the only code that reads the registered bytes.
- Every Lean lemma is cited by name in the SPARK contract that relies on it, with a correspondence table that gives the one statement in its two syntaxes. The trusted base register lists each one as "proved in Lean, bridged by reading".
- No `native_decide` counts as evidence.
- Lean and Mathlib join the trusted base. They are there already through upstream's proofs.

**The certificate's format.** For every wire:

- its class: gadget node, shared, copy or rewritten;
- its meaning, a linear form with constant coefficients over declared wires (wire 0 is the constant one), as a list of entries (coefficient, wire);
- for a bit the gadgets fold, the triple (c0, c1, wire): the bit is c0 + c1 · wire;
- for a product node, its two forms and the map from the pairs of their expansion to the wire's terms;
- the gadget instance it belongs to, and the type of the catalogue that gives the instance its meaning.

A form over other forms is expanded by the emitter, never by the checker.

**Two limits in the checker's contract**, distinct, so that a later generator that exceeds either is refused with a status of its own:

| Circuit | Form length (declared wires a meaning names) | Absorbed factors (in the construction of one node) |
|---|---:|---:|
| hash, over GF(2^128) | 3 | 12 |
| signature, over the base field of P-256 | 2 | 512 |

The reconstruction of a scalar from its 256 bits (`verify_circuit.h` 181 to 182 at 0d92f80c) is not a form: it is a declared gadget with its own lemma.

**The catalogue of gadget semantics**: one Gold lemma per gadget type across the two circuits, distinct from the word-level netlist. The netlist says what a circuit should compute; the catalogue says what each gadget's wires mean; the checker joins the two. The gadget functions of the two circuits reduce to twelve types:

| | Type | Gadgets (circuit) | Backend |
|---|---|---|---|
| G1 | Bit unpacking | `BitPlucker` (both) | Lean (the outputs are bits) and SPARK (the bit as a linear form) |
| G2 | Powers | `Polynomial::powers_of_x` (both) | SPARK, the local check |
| G3 | Words in the multiplicative group | `BitAdderAux` (hash) | Lean |
| G4 | SHA-256 compression | `FlatSHA256Circuit` (hash) | SPARK, against `Sha256` |
| G5 | Byte comparison | `Memcmp::leq` (hash) | SPARK |
| G6 | CBOR head | `CborByteDecoder` (hash) | SPARK |
| G7 | Routing in the MSO | the shifts, muxes and checks of `MdocHash` (hash) | SPARK |
| G8 | MAC over GF(2^128) | `MACGF2` (hash) | SPARK, the local check |
| G9 | GF(2^128) product over P-256 | `MAC::assert_mac`, `unpack_msg` (signature) | Lean |
| G10 | Element selection | `EltMuxer` (signature) | SPARK |
| G11 | Curve arithmetic and ECDSA | `VerifyCircuit` (signature) | Lean, upstream's ECDSA model |
| G12 | Scalar reconstruction | in `verify_signature3` (signature) | SPARK |

G3 rests on the order of α in the circuit's field. The milestone proves it in Lean by `decide`: the factorisation of 2^128 − 1 into nine primes and one test per prime, on a computable model of the field. If `decide` does not close in time, the stated fallback is a declared vector in the trusted base: the nine values, checked by the test harness.

**G11 reuses upstream's ECDSA model, on two conditions.**

- **Correctness.** The reuse is conditional on the merge of upstream's pull requests 225 and 215. #122 is a prerequisite of block 6. If they are not merged when block 6 opens, the fix is applied locally in a declared copy, and the evidence says so.
- **Ownership.** The bridge from the certificate's wires to the model's witness is this project's work and evidence, not a reading.

**Seven blocks.** The figures are an estimate from the costs the feasibility study measured, not a commitment:

| Block | Content | Estimate, weeks of work |
|---|---|---:|
| 1 | The relation specification of the hash circuit and its public interface, from chapter 9 Section 6 | 1 |
| 2 | The SHA-256 netlist and G4, with G1 and G3 in Lean | 2 |
| 3 | The checker core: the walk, its invariant, the local check, the two limits | 2 |
| 4 | The certificate's emitter and the hash circuit end to end | 2 to 3 |
| 5 | The rest of the hash relation: G5 to G8, the lint for issuers, the count of second occurrences | 2 to 3 |
| 6 | The signature circuit: G9 to G12 and the bridge to upstream's ECDSA model | 3 to 4 |
| 7 | The evidence, and the author's final review of the specification with the conditions table | 1 to 2 |
| | Total | 13 to 17 |

- **Block 6 starts after block 3**, in parallel with blocks 4 and 5. The checker core of block 3 is their common interface, and block 6 does not change it without a review.
- **Block 5** replaces upstream's "at least 96 bits of static security" (`mdoc_hash.h` 500 to 506 at 0d92f80c) with this project's own count of second occurrences, and provides the lint for issuers the conditions table announces.

**The place in the order.** After the guide for the evaluator, whose primer the checker's chapters build on, and before the certification block (ADR 0082, amended).

**The exit criterion.** Both circuits of the version 7 one-attribute pair are accepted by the checker, in `verify` and on the proving machine. The theorems are Gold, and the chapters are written for the audience of [ADR 0081](0081-audience-certification-evaluators.md). The trust model row on the circuits' semantics then reads: proved, under the specification of the relation and its conditions.

## Alternatives considered

- **A verified compiler in SPARK.** Rejected: it would not reproduce the bytes of upstream's optimising generator, so it would certify other circuits, not the registered ones.
- **Gadget templates over ranges of terms.** Rejected: the generator shares wires, folds constants and absorbs factors across gadget boundaries (15.2 % of the hash circuit's wires are rewritten), so a template breaks with every pass.
- **Equivalence checking without a certificate.** Rejected: it searches what the generator already knows. The certificate keeps the checker's work linear in the terms and its proof independent of the circuit's size.
- **A matcher that reconstructs the map from the terms.** Not needed: the instrumented generator maps every wire.
- **Everything in SPARK.** Rejected: the solvers do not reach the algebra of the gadgets (orders of elements, Karatsuba, the curve formulas); the lemmas would be trusted, not proved.
- **Everything in Lean.** Rejected: the registered bytes would be read by code outside the SPARK evidence of this project, and the checker would not be the executable this project ships and proves free of run-time errors.
- **Leaving the row trusted.** Rejected: it is the one row an evaluator cannot otherwise get past, and the feasibility study shows it can be closed in a measured time.

## Consequences

- The milestone "Certified circuits" opens after the guide for the evaluator. Its seven blocks become issues of the form Block, written from this record.
- `Local_Check`, the lemma of the feasibility study, enters a pull request of block 3 with its review. Until then it stays on the task branch of #88.
- The Lean development becomes part of the evidence an evaluator re-runs. Block 2, which brings its first lemmas, fixes where it lives and how the gate builds it.
- At the milestone's close, the trust model, the register and the Lean correspondence page change their rows on the circuits' semantics. The conditions table of chapter 9 Section 6 becomes the hypotheses of a theorem rather than a reading.

## Verification impact

None from this record: no code and no contract change. The milestone adds partitions and the Lean build to the gate; each block records its own.

## References

- [ADR 0066](0066-lagrange-tables-by-prefix-and-suffix.md), [ADR 0070](0070-sumcheck-and-ligero-kernels-as-upstream.md): the associativity of the product with the logical equality `Same`, and the ring laws behind opaque wrappers, which the local check uses.
- [ADR 0081](0081-audience-certification-evaluators.md), [ADR 0082](0082-order-after-the-memory-milestone.md), [ADR 0089](0089-the-supported-mdoc-profile.md).
- Chapter 3 (`Eval_Circuit`), chapter 9 Section 6 ("Conditions for certifying the circuit"), the trust model, the Lean correspondence page.
- Upstream: `lib/circuits/mdoc/`, `lib/circuits/logic/bit_adder.h`, `lib/circuits/ecdsa/verify_circuit.h` at 0d92f80c; `formal/AUDIT.md` and `formal/circuits/ECDSA` at 7bf8a6b; upstream issue 224 and pull requests 225 and 215.
- #88 (the feasibility study), #89 (this record), #122.
