# 0051 Constant time in the prover, unit by unit

## Status

Accepted (2026-10-18, at the close of block 6 of Phase C; proposed 2026-10-17 and edited until then)

## Date

2026-10-17

## Context

[ADR 0006](0006-constant-time-discipline-and-scope.md) set the discipline for the field arithmetic: no branch and no memory access that depends on a secret, masks in place of conditionals, a guarantee scoped to builds with assertions disabled. [ADR 0029](0029-sha256-and-aes256-in-spark.md) and [ADR 0037](0037-checked-inv-and-public-data-scope.md) declared it not applicable to the transcript and to every unit of stage 5, which process the public content of a proof string, with the clause that a prover would not reuse them on secrets without a new decision. The prover is that decision: the witness (the private inputs, the wires of every layer, the pads) is secret, and so is everything computed from it until it is masked or committed.

Two places in the reference branch on values. `write_ligero_proof` decides the run-length structure of the queried columns by testing each element for membership in the subfield (`contains_subfield`), and the membership test solves a linear system with a pivot search (`solve_subfield`, `rref_solve` in `algebra/gf2_128.rs`), whose control flow depends on the element. The queried columns are public once the proof is written, but the test runs on every element of every committed column, and the pivot search is data-dependent code on secret-derived values.

## Decision

The discipline of ADR 0006 applies to every prover unit that touches the witness, with the same clause: the guarantee holds for builds with assertions disabled, since executable contracts branch on values. Unit by unit:

- **Constant time by construction.** `Sumcheck_Prover`: `eval_round_poly` loops over the terms of the layer (public structure) and branches on the parity of a wire index of the term (public), never on a wire value; `bind` is a fixed loop of multiply-adds. The Reed-Solomon encoding of a row: a linear combination of the row's values with the public Lagrange matrix, fixed loops. The tableau layout: copies at positions fixed by the geometry and the subfield boundary (public). `Merkle.Build` over the leaf digests and `Sha256` over nonce and column bytes: data-independent flow (ADR 0029). The sampling of pads, random rows and nonces: depends on the randomness, not on the witness, and the P-256 rejection loop reads fresh bytes each time. The Ligero proof: `y_ldt`, `y_dot`, `y_quad` are linear combinations with public challenges; `a_full` is built from the public constraints.
- **Written with care.** The subfield encoding of Section 7.4: the run-length structure is decided by position, not by value. A queried column element is the Reed-Solomon encoding of a row of the tableau at one column, and whether that row is a subfield row is public: on P-256 every row is one, since the field is its own subfield and the reference's membership test is the constant `true` (`contains_subfield` of `algebra/p256.rs`), so the reference writes an empty full-field run and then one subfield run of every element at the full width, which the shipped `ecdsa2` proof shows; on GF(2^128) a witness row is a subfield row when it lies wholly below the subfield boundary, `(i + 1) * WR <= subfield_boundary` in `layout_witness_rows` of `ligero/prover.rs`, and the shipped `sha256` proof has the three runs the rule predicts (48, 1360 and 2000 elements: the three random rows, the 85 witness rows below the boundary of 3000 with WR 35, the rest). The rule rests on two facts. A subfield row encodes into the subfield: its random prefix is sampled in the subfield (`subfield.sample`), its witnesses lie in it (the check `Not_In_Subfield` of [ADR 0049](0049-phase-c-scope-the-prover.md) enforces it), the Lagrange coefficients over nodes and points of the subfield lie in it, so every encoded element does, by closure. A full-field row encodes outside the subfield except with probability 2^-112 per element, because every such row carries NREQ random full-field elements: the LDT, linear and quadratic rows are random throughout, the witness rows above the boundary and the x, y, z rows of the quadratic constraints carry a random prefix of NREQ elements (`sample_random_prefix_row`). Without that prefix the argument would fail: a row of zeros and ones, as a Boolean circuit has above the boundary, would encode into the subfield and the reference writer, which decides on the value (`contains_subfield` in `write_ligero_proof`), would group it in a subfield run. The writer therefore takes the run boundaries from the row kinds and the boundary, merges adjacent runs of the same kind, and respects the rules of the reader (runs alternate starting with a full-field run; a zero-length run only as the very first and only once; `read_ligero_proof` and the `Well_Coded` of `Ligero_Proof`), so that the verifier accepts the proof in every case and the bytes equal upstream's in all but the 2^-112 event. The projection of a subfield element to its two bytes is a fixed linear map: sixteen masks, each coordinate the parity of the element and its mask, precomputed from the basis (a left inverse of the 128 by 16 basis matrix exists on the low seventeen bits, checked on all 65536 subfield elements in the spike of block 1) and checked in the repository by a vector against the basis or a lemma; no linear system is solved at run time.
- **Two branches on witness-derived values, declared.** The satisfiability check of [ADR 0049](0049-phase-c-scope-the-prover.md) compares the outputs of layer 0 with zero and the Z assertions, and the prover stops with `Not_Satisfied`; the subfield check projects every private input below the boundary with the fixed map, re-injects the coordinates on the basis and compares with the input, accumulating the differences in one mask over all the inputs concerned, and stops with `Not_In_Subfield`. Each comparison is a fixed loop with a mask; the one branch on each accumulated result is the prover's own decision whether to produce a proof, and what it reveals is that the inputs are inadmissible, which the absence of a proof reveals anyway.
- **Out of the perimeter, public data:** the transcript and the challenges it yields, the circuit, the public inputs, the identifier, the serialised proof once written, the Merkle path (the opened columns are public by construction).
- **No inversion on witness values.** The prover computes no inverse of a secret; the inverses it uses are those of the public Lagrange denominators (`Checked_Inv` on public points, ADR 0037). Should an inversion of a secret become necessary, it is a decision to take first.

## Alternatives considered

- **The reference's membership test, made branch-free.** Rejected: a constant-time rank computation over 128 rows per element is heavy, and the position rule gives the same structure without any test.
- **Declaring the prover out of the constant-time perimeter**, as the verifier is. Rejected: the witness is the one secret the system has, and the prover is where it lives.
- **Measuring constant time.** Not possible with this project's means (ADR 0006): the discipline is reviewed by reading, and the chapter says so.

## Consequences

- Each prover unit's header states its position in the list above, as the stage 5 headers state the opposite.
- The writer of Section 7.4 needs the row kinds, which the geometry gives, and the subfield boundary, which the prover has from the circuit header.
- The byte identity with upstream holds up to the 2^-112 event above; the harness would show it as a mismatch, and the chapter names it.

## Verification impact

- Provable: nothing about timing; the structure of the code (loops with fixed bounds, selections by mask) is a reading discipline, as in ADR 0006.
- Tested: the fixed projection against the basis (ADR 0053).
- Trusted: that the discipline is kept, by review; the compiler's preservation of it, as ADR 0006.
- Constant time: this record.

## References

- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/algebra/gf2_128.rs` (`solve_subfield`, `rref_solve`, `contains_subfield`, `to_subfield_bytes`), `ligero/proof.rs` (`write_ligero_proof`), `ligero/prover.rs` (`layout_witness_rows`: `subfield_only`), `sumcheck/prover.rs`.
- [ADR 0006](0006-constant-time-discipline-and-scope.md), [ADR 0029](0029-sha256-and-aes256-in-spark.md), [ADR 0037](0037-checked-inv-and-public-data-scope.md), [ADR 0049](0049-phase-c-scope-the-prover.md), [ADR 0050](0050-randomness-as-a-byte-stream.md).
