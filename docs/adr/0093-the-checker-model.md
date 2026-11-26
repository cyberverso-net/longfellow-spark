# 0093 The circuit checker's model: meanings, facts and the certificate as a hint

## Status

Accepted (2026-11-26, with #170, block 3 of the milestone Certified circuits, before its code; proposed the same day from the census of the registered circuits).

## Date

2026-11-26

## Context

ADR 0091 decides a proved checker that takes a registered circuit file as it is, with an untrusted certificate, and walks it in layer order, one local identity per wire. It gives a wire's meaning as "a linear form with constant coefficients over declared wires", and the meaning of a product node as two such forms with a map from the pairs of their expansion to the wire's terms. That shape was taken from the feasibility study, which examined part of the hash circuit: block 0, round 20.

**What a census of the whole circuits shows.**
- **The method.** A census of every wire of the registered version 7 pair (a script in Python reading the files by the rules of the circuit reader; `scripts/census.py` keeps its computation, without the test for a product) expanded each wire's terms with the meanings of the wires they read, from the inputs up. It then sorted the wires by the polynomial they compute over the declared variables, with an exact test for a product of two forms.
- **On the hash circuit,** 3,366,957 wires:
  - 15.8 % are linear, with at most three variables;
  - 43.9 % are a product of two forms;
  - **40.4 % are neither.**
- **What the neither are.** Polynomials of degree 2 that are not products:
  - the factors of the multiplicative word encoding, x · y + a · x + b · y + c with c ≠ a · b;
  - the plucker's polynomial, which reads the square of the packed element;
  - the bits of SHA-256's rounds read through the squares of packed elements;
  - the mux of `assert_hash` over 40 selectors (40 monomials over 80 variables, in one wire);
  - the MAC's product of two packed elements (256 monomials over 131 variables, when the packed elements are expanded; 128 slots once the kind rule below declares them).
- **Linear wires longer than three variables:** the 6 wires of `MACGF2::pack` are linear of length 128.
- **On the signature circuit,** 220,137 wires:
  - 29.8 % are linear, with at most two variables;
  - 59.7 % are a product;
  - 10.4 % are neither: the mux of `EltMuxer`, the curve formulas of `addE` and `doubleE`, and the MAC.
- **Linear wires longer than two variables on the signature circuit:** 67 (`EltMuxer`, `MAC::unpack_msg`).
- **The scalar reconstruction from 256 bits** does not appear as a wire of its own. It is folded into products of 512 monomials of degree 2 over 1,025 variables, 769 slots, on six wires of `verify_signature3`.

The model of a product of two forms therefore does not cover the registered circuits. The census also found that no layer of the registered files has its terms sorted by output wire.

## Decision

### Variables and meanings

- **A declared variable** is named by its home, one wire of the circuit, and its value is that wire's value in the evaluation.
  - The input wires are the first variables: input wire i is variable i, with no relation.
  - Variable 0 is input wire 0, the constant one.
  - Every other variable is a declared wire.
  - **The checker assigns the identifiers**, in the order of the walk: the inputs first, then each declared wire as the walk declares it. The certificate names no variable: a slot's monomial is that of the pairs the walk forms, so a certificate cannot name another variable.
- **A wire's meaning** is a linear form over the declared variables, with constant coefficients.

### The walk, wire by wire

The walk goes over the layers from the inputs to the outputs.

**Coverage is by construction.** The walk iterates over the circuit's terms and wires, not over the certificate's entries, so a certificate cannot leave out a term or a wire. `Accepts` is a conjunction over the circuit.

- **The expansion.** For each term k · w(h1) · w(h0) of a wire, with k ≠ 0, the meanings of h1 and h0 are multiplied out into pairs of entries.
- **The hint.** The certificate says, for every pair, which slot of the wire it falls into. A slot is a monomial of degree at most 2 over the declared variables, with variable 0 standing for one.
- **The checks:**
  - every pair goes to a slot of its own monomial;
  - the slots of a wire are distinct monomials.
- **Q.** The coefficient of a slot is what the expansion collects there. The polynomial Q of the wire is its slots with those coefficients, in normal form because the slots are distinct.

**The kind of a wire is a rule of the checker, not a field of the certificate.**
- **Linear:** Q has degree at most 1 and at most `Max_Form` variables besides the constant. Its meaning is Q.
- **Declared:** otherwise. The wire becomes the variable of which it is the home, its meaning is that variable, and its fact is d_g = Q.

Any such rule is sound. This one fixes the form of the facts: short meanings, and a declared variable wherever a product or a long sum appears.

**The other facts:**
- every assertion of the circuit (a term with k = 0): the product of the two meanings is zero;
- every output of layer 0: its meaning is zero.

**Why the distinctness of the slots is checked and proved.** It is not needed for soundness. It is what makes Q a normal form: a catalogue lemma compares Q with its gadget's polynomial coefficient by coefficient, and block 4 rests on that.

### The certificate is a hint

- **What it carries:**
  - for every wire, the number of its slots, which lays out the pool of section "The limits";
  - for every pair of every term's expansion, its slot, which spares the checker a search for the monomial;
  - for every wire, the gadget instance and the catalogue type it belongs to, for the catalogue's lemmas.
- **What it does not carry:** no coefficient, no meaning, no kind and no fact. Those are computed.
- **Its failure mode.** A wrong slot makes the walk refuse. It cannot make a false fact, because a fact is what the circuit's own terms collect.

### The theorem

The declarations below are generic over the field, as `Sumcheck_Algebra` is, and instantiated for GF(2^128) in block 3 and P-256 in block 6.

- **`Accepts (P, K)`**, ghost. The conjunction, over the layers and wires of the packed circuit P, of the per-wire check with certificate K. It is a function of P and K alone, defined by a functional model of the walk:
  - the slots' coefficients by a recursive ghost function over the terms of a layer, as `Acc_Ref` is over the terms of `Eval_Quad`;
  - the meanings and the variables by recursion over the layers.
- **`Walk (P, K, St)`**, executable. Silver on its statuses, with the postcondition `(St = Accepted) = Accepts (P, K)`. It holds no induction.
- **`Lemma_Accepts (P, K, W, Wires)`**, ghost.
  - Its precondition:
    - `Valid (P)`;
    - `Accepts (P, K)`;
    - `Evaluated_Ok (Expand (P), W, Wires)`, which is `Eval_Circuit`'s postcondition with OK = True: the inputs in place, `Layer_Holds` and `Layer_Z` for every layer, the outputs zero;
    - `Same (W (0), One)`.
  - Its postcondition: `Facts_Hold (P, K, Wires)`. At the values of the declared variables read from `Wires`, every declared wire's fact holds, every assertion's product is zero, and every output's meaning is zero.
- **The induction is in `Lemma_Accepts`**, a ghost loop over the layers and the wires, in the order of the walk. Its invariant: every wire before has the value of its meaning, and every fact before holds. Each step uses the regrouping lemma of `Local_Check` and `Layer_Holds` at that wire, so the proof does not depend on the number of wires.
- **The premise `Same (W (0), One)`.** Variable 0 is read as one in every meaning, since a copy multiplies by input wire 0. So "variable 0 is one" is a premise of the theorem, and the final theorem obtains it from the relation of block 1, whose precondition has `X (X_One) = One`.

**What block 4 and the final theorem cite:** `Accepts`, the postcondition of `Walk`, and `Lemma_Accepts`.

### The walk over the registered files

- **The terms in file order.** The terms of a wire are spread through its layer, so the walk accumulates each term's expansion into its wire's slots in file order, as `Eval_Quad` accumulates `Acc_Ref`. It checks each wire at the end of its layer.
- **The bridge to `Acc_Ref`.** This order gives the bridge by the structure of `Eval_Quad`'s proof: `Acc_Ref` multiplies (k · w(h1)) · w(h0) over the terms with k ≠ 0, in term order.
- **The circuit's form.** The walk reads the circuit through `Packed_Circuits`, the form the prover and the verifier hold, and the theorem is stated over `Expand (P)`.

### The limits

Every constant whose excess refuses a circuit is a constant of the checker's contract, per field instance, with a status of its own. The values are the census's, run under the kind rule (`scripts/census.py`) on the registered pair.

| Constant | What it bounds | GF(2^128): measured, bound | P-256: measured, bound | Status when exceeded |
| --- | --- | --- | --- | --- |
| `Max_Terms_Per_Wire` | terms (k ≠ 0) of one wire | 128, 128 | 769, 769 | `Too_Many_Terms` |
| `Max_Slots` | slots of one wire | 128, 128 | 769, 769 | `Too_Many_Slots` |
| `Max_Layer_Slots` | slots of all the wires of one layer, the pool | 3,578,718, 2^22 | 158,225, 2^18 | `Pool_Full` |
| `Max_Vars` | declared variables, inputs included | 2,921,144, 2^22 | 158,159, 2^18 | `Too_Many_Vars` |

- **Where the values come from.** They are measured by `scripts/census.py` with the checker's kind rule. That is why they differ from the first census of the Context: the six wires of `MACGF2::pack` are declared, so the MAC's product has 128 slots rather than 257, and there are six more declared variables.
- **The capacities are sized for the one-attribute pair**, the milestone's target. The circuits for 2 to 4 attributes are outside the milestone.
- **The per-wire bounds are the measured values**, as ADR 0091 asks: a later generator that exceeds them is refused, not accepted silently.
- **The pool and the variables are capacities**, the next power of two above the measured value. The pool holds the slots of one layer, laid out wire by wire from the counts the certificate gives. It is bounded on its own, since a table of `Max_Slots` entries for each wire of a layer would be 128 × 1.6 million entries on the hash circuit. Its size is `Max_Layer_Slots` × (two identifiers and one coefficient): about 100 MB for GF(2^128), 10 MB for P-256.
- **Two constants refuse nothing, since they hold by construction:**
  - `Max_Form`, 3 and 2: the kind rule declares a wire whose linear meaning would be longer, which covers `MACGF2::pack` and the scalar reconstruction of the signature circuit (G12) with no kind of their own;
  - the pairs of one term's expansion, (`Max_Form` + 1)², 16 and 9: a meaning has at most `Max_Form` + 1 entries.
- **`Max_Terms_Per_Wire` and `Max_Slots` replace ADR 0091's "absorbed factors"**, a count made inside the generator that the checker cannot see. ADR 0091's Status line records it.
- **The certificate's own refusals:** a slot index beyond the wire's count (`Bad_Hint`), a pair sent to a slot of another monomial (`Wrong_Monomial`), two slots of one monomial (`Duplicate_Slot`), a slot no pair reaches (`Empty_Slot`), so that the count of a wire's slots, which the certificate gives, is exact and a wire has one normal form whatever the certificate. `Accepts` states both the distinctness of the slots and that every slot is reached, and the reader's statuses on its bytes.

### The run on the registered circuits

The theorem is proved for every circuit and certificate. That the registered pair is accepted is one run of the proved checker on it, which the register lists as row T9:
- the digest of the circuit file;
- the digest of the certificate;
- the digest of the checker's sources at the commit;
- the command, `longfellow_check_circuit` in the release build, which anyone repeats.

### An independent check

`scripts/census.py` computes the same polynomials as the checker, in another language and through another reader (the Python reader of the vector generators). A test of the vectors step compares, on the registered circuits, the checker's facts with the census's: a digest of all the facts in the order of the walk, and the counts per kind and per shape. It is not proof; it is a second computation an evaluator can read. It takes 22 seconds on the hash circuit and 2 on the signature circuit, so it runs at every gate.

## Alternatives considered

- **Meanings over the wires of the layer below**, the design's first alternative. `Local_Check` would apply as it is, but each wire would be known one layer deep only. Every catalogue lemma would then compose across up to 17 layers of copies itself, while the gadgets do not follow the layers (6.0 % copies and 15.2 % rewritten wires, F1). Rejected.
- **A declared wire as a product A · B of two forms**, the model ADR 0091 sketched. It leaves 40.4 % of the hash circuit's wires out, the mux of `assert_hash` among them, and needs a third kind for long linear wires and for G12. Rejected. A · B stays possible as an optional factoring a gadget lemma may ask for, checked by `Local_Check` as it is.
- **Q given by the certificate**, with its coefficients, and compared. It is sound too, but it carries 24 bytes per slot (about 200 MB raw on the hash circuit, against about 15 MB for the hint) and adds a comparison to the proof. Nothing gained: the coefficients are what the terms collect. Rejected.
- **Normal forms computed without a hint**, the checker searching each pair's monomial among the wire's slots. Also sound, and the certificate would carry only the gadget instances. The search costs at most `Max_Slots` comparisons per pair, so the hint is a matter of time, not of trust. Kept as the fallback if the certificate turns out too large to commit (block 4 measures it).

## Consequences

- **The census, on the signature circuit:**
  - 220,137 wires: 65,685 short linear, 67 long linear, 131,403 products, 22,982 neither;
  - at most 769 terms and 769 slots on one wire;
  - no layer sorted by output wire;
  - every wire is of degree at most 2, so the model covers it, as it covers the hash circuit.
- **ADR 0091 gains a Status note** on its second limit: the count of absorbed factors becomes the two bounds the checker sees.
- **The certificate's size.**
  - On the hash circuit the hint is about 8 MB raw, and about 15 MB with the gadget instances.
  - Coded as LFC2 codes the circuit, it is probably a few MB.
  - If it stays under about 10 MB it is committed beside the circuit and pinned by its digest. Otherwise it is produced by the pinned instrumented generator and identified by its digest. Block 4 decides on the measured size.
- **The walk's time and memory.**
  - About 16 million field products on the hash circuit, about half a second.
  - The meanings of two adjacent layers in memory, at most 1.6 million wires, on the order of 100 MB beside the packed circuit.
  - Reading the certificate dominates, seconds to a minute. Block 4 measures it.
- **Which circuit the statement is about.** The checker reads the file through the same reader and the same packed form as the verifier (`Circuit_Reader`, `Packed_Circuits`). The theorem, stated over `Expand (P)`, is therefore about the circuit the verifier evaluates. No meaning of the file's bytes is trusted beyond what the register already lists: row R4 (upstream's production reader defines the LFC2 format) and row T8 (the contracts at `Proof_Only`, `Expand` and `Cursor_At` among them, are not compiled).
- **The interface of blocks 4 to 6** is `Accepts`, `Walk` and `Lemma_Accepts`, and the form of the facts. A change goes through a review, as ADR 0091 says.

## Verification impact

- **New units,** proved in new partitions (`checker` and `cert-reader`):
  - `Checker` (the walk and the theorem): Gold on the theorem, Silver on the statuses;
  - `Cert_Reader`: Silver on any bytes.
- **`Local_Check`** enters main, generic over the field, with its regrouping lemma extended to a sequence of terms each the product of two forms. Gold.
- No existing contract changes, and no prover setting.
- **The register gains T9** with block 4, which runs the checker on the registered circuit and fills in its digests.
- **The vectors step gains the comparison** with the census.

## References

- ADR 0091 (the milestone, the certificate, the limits), ADR 0024 (genericity over the field), ADR 0066 and ADR 0070 (the ring laws, `Same`, the opaque wrappers), ADR 0080 (the packed circuit).
- Chapter 3 (`Eval_Circuit`, `Acc_Ref`), chapter 10 Section 3.
- #170, #88 (the feasibility study).

---
