# 0094 The certificate without hints: the walk finds each pair's slot

## Status

Accepted (2026-11-28, with #171, block 4 of the milestone Certified circuits, before its code; decided by the maintainer on 28 November 2026 over the alternative below, on the census and the measurement of the search). Amends [ADR 0093](0093-the-checker-model.md): its hint is withdrawn, and its fallback "Normal forms computed without a hint" is the decision.

## Date

2026-11-28

## Context

ADR 0093 gives the certificate, for every pair of every term's expansion, the slot of the wire that the pair's monomial takes: the hint. The walk checks it:
- a slot beyond the wire's count is refused (`Bad_Hint`);
- a pair sent to a slot of another monomial is refused (`Wrong_Monomial`);
- a new slot whose monomial the wire already has is refused (`Duplicate_Slot`);
- hints left unused are refused (`Hints_Left`).

The record kept the alternative, the walk searching each pair's monomial among its wire's slots, as the fallback if the certificate turned out too large to commit, and left the measurement to block 4.

**What the measurement shows.** On the registered version 7 pair, with `scripts/census.py`:
- **The size.** The certificate of ADR 0093 for the hash circuit is 14,400,111 bytes raw, against the record's estimate of about 8 MB, so it is over the 10 MB the record set for committing it. It compresses to 89,804 bytes with gzip, 160 times smaller.
- **Why it compresses so well.** Of the hash circuit's 7,666,061 pairs, all but 32 open a new slot: the hint of all the others is "the next free slot". On the signature circuit, all but 94 of 480,133.
- **The cost of the search.** A walk without hints compares each pair's monomial with its wire's slots until it finds it or reaches the end. That is 11,476,606 comparisons on the hash circuit (1.5 per pair, at most 127 for one pair) and 2,342,741 on the signature circuit (at most 768). It is a few milliseconds of work.

**A compact hint was considered:** the exceptions only, every other pair taking the next free slot. To refuse a duplicate, that walk must check that the default slot's monomial is not already among the wire's slots: the same search as without hints, with a list to read besides.

## Decision

**The certificate carries no hint.** For each pair of a term's expansion, the walk takes the first slot of the wire whose monomial is the pair's. If there is none, it opens the next slot.

**What the certificate carries:**
- the circuit's identifier, compared by the driver as ADR 0093 states;
- for each layer, the number of its wires;
- for each wire, the number of its slots.

The gadget instances are added by the catalogue's block, in a section of their own.

**The slot counts stay, and they decide nothing.** The walk needs each wire's count before the layer's pairs are placed, to lay out the pool. Each count is checked:
- a new slot beyond the wire's count is refused;
- a count above the slots the pairs reach is refused (`Empty_Slot`).

So a wrong count makes the walk refuse, and the counts are the circuit's own.

**What changes in the model of `Circuit_Checker`:**
- **The slot of a pair,** `H`, is a ghost function of the circuit alone: the slot of the pair's monomial if the wire already has it, else the wire's used count. Two recursive functions over the pairs of the layer define it: `Present`, whether the wire has a monomial, and `Index_Of`, the slot it took. The used count, `Used`, grows by one for each pair whose monomial the wire does not have yet, and stops at `Max_Count + 1`, above every count a certificate can give. A lemma, `Lemma_Slots`, says what the search relies on: a monomial the wire has is at a used slot, and a used slot's monomial is one the wire has, at that slot.
- **The rest of the model keeps its text:** `Used`, `Slot_Mono`, `Slot_Coef` and `Pair_Ok` read `H` as before.
  - Two of the three conjuncts of `Pair_Ok` (the slot reached and its monomial) now hold by `Lemma_Slots`.
  - The third, the slot below the wire's count, is the one check left.
- **The theorem is unchanged.** `Lemma_Accepts` and its induction read `Pair_Ok` as before.
- **Removed:**
  - `Hint_At` and `Hint_Pos` and their lemmas;
  - the conjunct of `Layer_Ok` that every hint is used;
  - the certificate's array of hints and their spans.

**The statuses:**
- **removed:** `Wrong_Monomial`, `Duplicate_Slot` and `Hints_Left`, which only a hint could cause;
- **renamed:** `Bad_Hint` becomes `Count_Exceeded`, a new slot beyond the wire's count;
- **kept:** `Empty_Slot`.

**The hostile certificates.** The five on the hints leave the harness: one hint too many, one too few, a new slot not in the first free place, a pair sent to another monomial, a duplicate slot. The two on the counts stay: one below the true count (`Count_Exceeded`) and one above (`Empty_Slot`).

**The certificate of the registered hash circuit** is written by `scripts/census.py`, about 3.4 MB raw. It is committed beside the circuit in `tests/vectors/` and pinned by its digest. No generator is needed to write it.

## Alternatives considered

- **The hint of ADR 0093 as it is.** Rejected: 14.4 MB raw for 32 slots of information, over the record's own limit for committing it.
- **The exceptions only,** every other pair taking the next free slot. Sound, and about 3.4 MB with the counts. Rejected:
  - it makes the same search as this decision to refuse a duplicate;
  - it keeps a list sorted by pair position, with a cursor in the walk and its invariant;
  - it keeps three statuses and six hostile certificates of its own.
- **No counts either:** the walk would count each wire's slots in a first pass over the layer, by the same search. It would read no certificate at all. Rejected:
  - it proves the walk's most expensive invariant, that of the used slots, twice;
  - it doubles the time of the walk;
  - it gains nothing in what the theorem says, since the counts already decide nothing.

  A later block may take it if the walk is wanted independent of any certificate.
- **Compressing the certificate of ADR 0093.** Rejected: a decompressor in front of a proved reader is either outside the proof or a block of its own.

## Consequences

- **`Circuit_Certificates`** loses the hints, their spans and `Max_All_Hints`. The format's version becomes 2, and the reader refuses a certificate of version 1.
- **`Circuit_Checker`:**
  - `Check_Layer`'s check of a pair becomes a search loop with its invariant;
  - `Layer_Coefficients` places each pair by the same search;
  - both are re-proved, at their levels: `Walk` Gold against `Accepts`, `Lemma_Accepts` Gold, the reader Silver.
- **`scripts/census.py`** writes the new format. `tests/vectors/gen_checker_vectors.py` and `checker_kat` follow the new list of hostile certificates.
- **Chapter 10 Section 3** describes the search in place of the hint. The record of the certificate's instances is the catalogue's.
- **The time of the walk** gains the search, measured on the registered hash circuit with the walk's other figures.

## Verification impact

- **Contracts changed, with the maintainer's agreement:**
  - the model `Accepts` (through `H` and `Layer_Ok`) and the postcondition of `Walk`, which states it;
  - the certificate's type and `Spans_Ok`;
  - the reader's postcondition;
  - the statuses of `Status`.
- **The theorem `Lemma_Accepts` keeps its statement.**
- **New ghost code:** `Present`, `Index_Of` and `Lemma_Slots`, and the invariant of the search in `Check_Layer` and `Layer_Coefficients`.
- **`Layer_Coefficients` keeps its postcondition:** the model's slots for any certificate whose counts fit. It keeps each wire's used count up to the wire's count, and a pair whose slot falls at or beyond the count changes no slot of the pool, as in the model.
- **The partition `checker`** is proved again from the final sources, the block's VC log recording each unproved check.

## References

- [ADR 0093](0093-the-checker-model.md): the model, its fallback, its hostile certificates.
- [ADR 0091](0091-certified-circuits-milestone.md): piece 3, the certificate.
- `scripts/census.py`, and the registered pair `8d079211…` in `tests/vectors/upstream/mdoc/`.
- Chapter 10 Section 3.
