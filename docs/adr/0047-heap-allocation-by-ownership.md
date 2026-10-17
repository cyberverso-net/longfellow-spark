# 0047 Heap allocation by ownership for the circuit and the working set

## Status

Accepted (2026-10-17, at the close of block 3 of Phase B; proposed 2026-10-16 and edited until then)

## Date

2026-10-16

## Context

Every object of the verifier has lived on the stack: the circuit record of stage 3 (`Raw_Circuit`, with its discriminants `Last_Layer` and `NT`), the challenges, the padded proof, the constraint terms, the Ligero proof record and the tables ([ADR 0039](0039-sizes-allocation-and-status.md)). Chapter 3 found the first limit at 32768 private inputs, chapter 5 states the supported scale as a few tens of thousands of inputs on an 8 MiB stack. The two upstream circuits of [ADR 0046](0046-phase-b-scope-lfc2-loader-and-interop.md) fit (a few megabytes); an mDoc circuit, with millions of terms at 48 bytes each on P-256, does not, and the loader's own tables (deltas, segments, tokens, sized by counts the file declares) are of the same order.

SPARK supports pool-specific access types under its ownership rules (SPARK Reference Manual 3.10): one owner at a time, no aliasing, deallocation through `Ada.Unchecked_Deallocation`, absence of dangling and null dereferences proved. A spike on 2026-10-16 with GNAT 16 and GNATprove 16.1 established what the rules allow for a discriminated record with a large array component:

- An uninitialised allocator, `new Raw_Circuit (Last_Layer => L, NT => N)`, is rejected unless the type has full default initialisation ("uninitialized allocator without default initialization is not allowed in SPARK", E0019).
- An initialised allocator with an aggregate, `new Raw_Circuit'(..., Terms => [others => ...])`, is accepted and GNAT builds the object in place on the heap: 2^25 terms, one gigabyte, allocated and filled in 0.9 s with no growth of the stack.
- Giving every component a default value makes the uninitialised allocator legal too, at the price of default values on the element types of stages 1 and 2.
- The fill loop over the allocated array, a loop invariant establishing `Well_Formed` on `C.all`, a postcondition `C /= null and then Well_Formed (C.all)` and a `Free` with postcondition `C = null` are all proved at level 2.

## Decision

- **The circuit lives on the heap.** `Circuit_Reader` declares `type Circuit_Access is access Raw_Circuit` and allocates once, after the counting pass, with an aggregate allocator sized by the counted layers and terms; the second pass fills the object in place; the postcondition states `Well_Formed (C.all)` on `Ok`. `Free` deallocates. The element types keep no default values. Callers pass `C.all` to the verifier, which is unchanged: Ada passes a record of this size by reference, so no copy exists.
- **The working set of `Verify` lives on the heap, in one allocation per verifier.** `Zk_Verifier.Verify` allocates a record `Work`, discriminated by the sizes the circuit and the geometry fix (the padded sumcheck proof, the Ligero proof record with its columns and path, the challenges, the constraint terms, the constants and the quadratic triples), after its length checks, passes its components by reference to the reader, the replay, the core and the Ligero verifier, and frees it before returning, on every path. `Ligero_Verifier.Verify` does the same for its own working set (the Ligero challenges, the chosen columns, the two Lagrange tables, the evaluation vectors of the tests, the constraint vector of the linear test), after its length checks. Two allocations per verification, one per level, rather than one: merging them would need the complete verifier to name the Ligero verifier's working set, a dozen discriminants exposed in a spec for no gain in memory. The stage 3 expressions of the input constraint stay as they are: their memory is linear in the private inputs (about 120 bytes each on P-256, under a megabyte for the upstream circuits) and their time is quadratic, seconds for the upstream circuits; a circuit of a hundred thousand private inputs would take minutes, which is recorded as the limit of Phase B and revisited with the prover.
- **Allocation failure is outside the proofs,** as stack exhaustion was: `Storage_Error` on `new` is not a status, since no SPARK contract can speak of it (SPARK User's Guide, "Dealing with Storage_Error"); the supported scale becomes the available memory, and chapter 6 gives the bytes per term, per input and per column.
- The loader's own tables (deltas, segments, tokens) are allocated the same way, sized by the counts the file declares after the check that each count fits the bytes that remain (every entry is at least one byte), so that a hostile header cannot demand more than the file's own length.

## Alternatives considered

- **Default values on the element types**, to use the uninitialised allocator. Rejected: it changes the types of stages 1 and 2 (and the meaning of initialisation for every variable of those types in flow analysis) to save an aggregate the compiler builds in place anyway.
- **A larger stack** (`ulimit -s`, or a task with `Storage_Size`). Rejected: not portable, and tasking brings a run-time the library does not need; the stack was never the right place for an object sized by a file.
- **Keeping the working set local and moving only the circuit.** Viable for the two upstream circuits, whose working set is under a megabyte; rejected because the move is the same work either way and ADR 0039 had already decided one allocation sized by the geometry.
- **Library-level objects of maximum size.** Rejected: `Max_Terms` times 48 bytes is twelve gigabytes.

## Consequences

- `Circuit_Reader` and `Zk_Verifier` use access types; the proofs gain the ownership checks (no dangling, no null dereference, every path frees).
- The API of `Zk_Verifier.Verify` is unchanged for the circuit (`C : Circuit`); callers hold a `Circuit_Access` and pass `C.all`.
- The README trust model replaces "the supported scale of the verifier's working set on the stack" with "the available memory for one circuit and one working set".

## Verification impact

- Provable: absence of run-time errors including the access rules; the initialisation of the allocated objects in whole; `Well_Formed` of the loaded circuit; the deallocation on every path.
- Tested: the sizes on the two upstream circuits; the loader on a hostile header (counts beyond the bytes).
- Trusted: `Storage_Error` on allocation; GNAT's in-place construction of the aggregate allocator, observed in the spike, not a language guarantee (if a future compiler built the aggregate on the stack, the spike's run at 2^25 terms would show it).
- Constant time: not applicable, as ADR 0037.

## References

- SPARK Reference Manual 3.10 (access types, ownership); SPARK User's Guide, "Dealing with Storage_Error", "Pointer Support".
- The spike: a generic record with discriminants and a term array, aggregate allocator, fill loop with invariant, `Free`; 27 checks proved; runs at 2^22 and 2^25 terms (session note of 2026-10-16).
- [ADR 0011](0011-circuits-as-data.md), [ADR 0039](0039-sizes-allocation-and-status.md), [ADR 0046](0046-phase-b-scope-lfc2-loader-and-interop.md); chapter 3 Section 3.5, chapter 5 Section 3.5.
