# Chapter 6: the circuit loader, the heap and the interop proofs

Units `Uleb128`, `Circuit_Status`, `Circuit_Reader` (generic over the sumcheck algebra of a field, instantiated for GF(2^128) and for the P-256 base field), the working sets of `Zk_Verifier` and `Ligero_Verifier` on the heap, the release project `cli/` with the command-line verifier `longfellow_verify` and the interop harness `interop_kat`. Phase B, complete. Decisions: [ADR 0046](../adr/0046-phase-b-scope-lfc2-loader-and-interop.md) (scope and the format), [ADR 0047](../adr/0047-heap-allocation-by-ownership.md) (the heap), [ADR 0048](../adr/0048-circuit-vectors-and-interop-proofs.md) (vectors and interop), with [ADR 0011](../adr/0011-circuits-as-data.md) (circuits as data) as the frame.

Phase A ended with a verifier from the proof string to a verdict on circuits held in memory as the term lists of the draft's Appendix B.3. Phase B gives it the circuits the upstream compiler produces: a loader for the upstream file format that proves what the verifier needs of a circuit, memory that does not depend on the size of a stack, and the exit criterion of [ADR 0011](../adr/0011-circuits-as-data.md): proofs produced by the upstream prover on upstream circuits, accepted from their files.

## 1. The format

### 1.1 What the verifier needs of a circuit

Chapter 3 defined a circuit as data: layers, each a list of terms (g, h0, h1, k) with k an element, meaning Q[g, h0, h1] = k in the quad representation of draft Section 6.3.2 (k = 0 marks a Z assertion, Section 6.3.3), and the counts `noutput`, `ninput`, `npublic`. The verifier needs nothing else of a circuit's meaning, but it needs its shape to be right: `Well_Formed` of `Sumcheck_Algebra` (every term names an output wire below its layer's output width and input wires below its input width, `nw <= 2^logw`, the last layer reads exactly `ninput` wires, `npublic <= ninput`, the layers partition the term list in order) is a precondition of `Verifier_Core`, and the stage 3 proofs assume it. The loader's job is to establish it on arbitrary bytes.

### 1.2 LFC2

The pinned draft does not define a file format for circuits; the upstream implementation does, at d5e6be7, in `rust/core/proto/src/writer/lfc2.rs` and `reader/lfc2.rs` (the production reader, with its bounds and its error cases), with a simplified copy under `docs/specs/rust/src/circuit/lfc2.rs`. ADR 0046 takes the production reader as the definition of the format. A file is:

- the magic `LFC2`;
- seven ULEB128 integers: `field_id` (`FieldID` of `lib/proto/circuit_io.h`: 1 for P-256, 4 for GF(2^128)), `nv` (the output count), `ncopies` (always 1), `npublic_input`, `subfield_boundary` (a prover-side parameter, how many witnesses lie in the subfield), `ninput`, `nl` (the layer count);
- a table of constants: a count, then that many elements in the encoding of Section 7.2.1 (16 bytes little-endian on GF(2^128), 32 bytes little-endian below p on P-256);
- per layer: `logw`, `nw` (the layer's input width), a table of **deltas** (four ULEB128 each: g, h0, h1 zigzag-encoded, an index into the constants), a dictionary of **segments** (each a count then that many delta indices), and a sequence of **tokens** (segment indices);
- 32 bytes of identifier.

ULEB128 is the unsigned little-endian base-128 encoding, seven bits per byte with a continuation bit; the production reader takes at most four bytes, so a value is below 2^28, and a fourth byte with the continuation bit set is an error. Zigzag maps a signed delta d to 2d when d >= 0 and to -2d - 1 otherwise, so that small differences of either sign take one byte.

### 1.3 Expansion by prefix sums

The term list of a layer is the expansion of its tokens: for each token, for each delta index in the named segment, the delta is added to a running (g, h0, h1) that starts at (0, 0, 0) for the layer, and the term (g, h0, h1, constants[k]) is appended. Deltas and segments are dictionaries: the writer deduplicates the differences between consecutive terms and the sequences of them, which is what makes an mDoc circuit a megabyte where the earlier format took a hundred. Any valid encoding denotes the same list, so the reader must accept every one, not only the writer's: the generator writes each test circuit twice, deduplicated as upstream does and plainly, one delta per term in one segment.

### 1.4 The identifier

The last 32 bytes are `compute_id` of `rust/core/proto/src/circuit.rs`: the SHA-256 of a canonical form of the circuit, independent of the encoding chosen. The hash takes, as eight little-endian bytes each: a field tag (2 and the bit width for a binary field; 1 and the encoding of -1 for a prime field), `noutput`, `logv` = ceil(log2 `noutput`), 1 (`ncopies`), 0 (`logc`), `nl`, `ninput`, `npublic`, `subfield_boundary`; then per layer `nw`, `logw` and the term count; then per term g, h0, h1 and the constant's bytes. The identifier is what the transcript binds (`Write_Sumcheck_Statement`, chapter 4), so a verifier that accepted a file whose identifier does not match its content would verify a proof against a statement about another circuit. The loader always recomputes it (upstream makes the check optional, for files that predate the identifier).

### 1.5 Where this project is stricter

The production reader accepts what its allocator can hold: 5 000 000 wires, 20 000 000 terms, 10 000 layers. This project's bounds are those of the stage 3 proofs: `Max_Wires` 2^24, `Max_Terms` 2^28, `Max_Layers` 64, `Max_Logw` 40 (as upstream). And the production reader does not check what `Well_Formed` demands: a term may name a wire beyond its layer's width, a width may exceed 2^logw. A circuit that upstream would load and then misuse is refused here, with `Bound_Exceeded` or `Not_Well_Formed`. "Accepts everything upstream accepts" is therefore not a property of this loader, and chapter 6 says so where ADR 0046 decided it; the two upstream circuits, and every circuit a correct compiler produces, lie inside both sets of rules.

## 2. The algorithms

### 2.1 Reading an integer

`Uleb128.Read` takes the bytes and a position; it reads up to four bytes, accumulating the seven-bit payload of byte i times 128^i, and stops at the first byte without the continuation bit. It fails in two ways, which the loader distinguishes: the bytes end first (`Truncated`), or the fourth byte continues (`Bad_Integer`). `Zigzag` is the decoding of Section 1.2.

### 2.2 Two passes

The loader cannot allocate the circuit before it knows the layer and term counts, and it cannot trust the counts the header declares without reading the layers. So it walks the file twice. The first walk validates and counts: every integer well formed, every count within the bytes that remain (a count of n entries that each take at least one byte must satisfy n <= remaining bytes, so a hostile header cannot demand an allocation larger than the file), every constant an element, every index in range at the point it is read, `logw` and `nw` within the bounds, the term count accumulated with the bound checked before each addition, the identifier present, nothing after it. The second walk allocates the circuit once, with the counts of the first, and fills it: the constants into a table, each layer's deltas into a table, each layer's segments as positions in the file, and the expansion of the tokens into the term array, with the running (g, h0, h1) kept within the wire range at every step.

The two walks are one procedure, `Walk`, with the circuit as a parameter that is null in the first pass. Every write into the circuit in the second pass is guarded by a bound check against the circuit's own discriminants, with the status `Bad_Index` on failure: the guards are unreachable, since the two walks read the same bytes, but they let the proof of the second pass stand on its own, and the two walks' counts are compared at the end.

### 2.3 After the walks

The loaded circuit is checked against `Well_Formed`, at run time, in one linear pass (`Not_Well_Formed`); then its identifier is recomputed and compared with the stored one (`Id_Mismatch`). Only then is the circuit returned.

## 3. The Ada/SPARK implementation

### 3.1 Access types under ownership

Everything until this chapter lived on the stack, and chapter 3 and chapter 5 recorded the limit: a few tens of thousands of inputs on a default 8 MiB stack. A circuit of a hundred thousand terms is a few megabytes; an mDoc circuit is hundreds. The loader allocates the circuit on the heap.

An *access type* in Ada is a pointer type: `type Circuit_Access is access Raw_Circuit;` and a value of it designates an object created by an *allocator*, `new Raw_Circuit'(...)`. SPARK admits pointers under *ownership* rules (SPARK Reference Manual 3.10): at any time one path owns a designated object, assigning an access value moves the ownership, passing it as a parameter lends it for the call, and a procedure that returns with an owning local still non-null is reported as a possible memory leak. The provers then establish what pointers usually prevent them from establishing: no null dereference, no dangling reference, no aliasing between what one procedure writes and what another reads. Deallocation is `Ada.Unchecked_Deallocation`, instantiated for the type; after a call the access value is null, which the instance's postcondition states.

Two rules shaped the code, found by the spike of ADR 0047 before any of it was written. SPARK rejects an allocator without an initial value unless the type is fully default-initialised (`new Raw_Circuit (Last_Layer => L, NT => N)` is an error, E0019), and the element types of stages 1 and 2 have no defaults; so every allocation is an *aggregate allocator*, `new Raw_Circuit'(Last_Layer => ..., Terms => [others => ...], ...)`, which names every component. GNAT builds such an aggregate in place on the heap: the spike allocated 2^25 terms, a gigabyte, in 0.9 seconds with no growth of the stack. That construction is observed, not a language guarantee, and the trust model says so.

### 3.2 Circuit_Reader

The generic takes the sumcheck algebra of a field (hence its `Raw_Circuit`, its element and its `From_Bytes`), the field identifier and whether the field is binary. `Read (B, C, H, St)` returns the circuit as a `Circuit_Access`, a `Header` (the field identifier, the subfield boundary, the identifier) and a `Circuit_Status.Status`, one of twelve values, one per cause (`Ok, Bad_Magic, Field_Mismatch, Unsupported_Copies, Bad_Integer, Bound_Exceeded, Bad_Element, Bad_Index, Truncated, Trailing_Bytes, Id_Mismatch, Not_Well_Formed`); nothing raises. Its postcondition is the shape of the result: `St = Ok` exactly when `C /= null`, and then `Well_Formed (C.all)` and `H.Id = Compute_Id (C.all, H.Subfield_Boundary)`; on any other status `C` is null and the header is `Null_Header`.

The temporaries of a walk (the constants, each layer's deltas and segments) are heap arrays too, sized by the counts after the check that they fit the bytes, allocated in the pass that needs them and freed on every exit of the procedure. The deallocation calls go through the `Unchecked_Deallocation` instances directly: a wrapper procedure that freed two at once drew the flow warning "statement has no effect" on every exit, since its outputs are dead after the return, while the direct calls are recognised.

`Compute_Id` transcribes `compute_id` over `Sha256` of chapter 4, with `Ceil_Lg2` as the reference's `ceil_lg2`; the field tag is a constant chosen by the generic formal `Is_Binary` (an `if` statement on a formal known statically drew a flow warning, an if-expression in a constant does not).

### 3.3 Establishing Well_Formed

`Well_Formed` is the type predicate of `Circuit`, the subtype of `Raw_Circuit` that the verifier takes. The loader does not prove it from the walk; it checks it, once, on the finished object, and the postcondition follows from the check. The alternative, a functional specification of the expansion from which the predicate would follow, would prove that the loader expands as the walk defines and would still leave the agreement with upstream to the vectors, which is where it belongs: the Gold of the loader is `Well_Formed` of what it returns and the equality of the identifier, and the expansion is tested (Section 5).

Three lessons of the proof. `128 ** I` with a variable exponent is opaque to the provers, so `Pow128` is a function by cases over 0 .. 4 and the arithmetic becomes linear. A sum `Pos + N` with `Pos` as large as a byte count overflows `Natural` in the provers' eyes even when it cannot at run time, so bounds are written as differences (`B'Length - Pos <= I`). And a record component declared `Integer` carries nothing of the postcondition of the function that filled it: the deltas' components are a subtype `Signed_Delta` of the range `Zigzag` gives, so that the running sums have bounds.

### 3.4 The working sets of Verify on the heap

`Zk_Verifier.Verify` used to declare its proof record, challenges, constraint terms and triples as locals; `Ligero_Verifier.Verify` its challenges, chosen columns, two Lagrange tables, evaluation vectors and constraint vector. Each now allocates one record `Work`, discriminated by the sizes the circuit and the geometry fix, with an aggregate allocator after its length checks, passes the components by reference to the readers and the tests, and frees it on every path. Two allocations per verification, one per level (ADR 0047): merging them would have the complete verifier name the Ligero verifier's working set through a dozen discriminants exposed in a spec, for no gain in memory. Ada's rule that a component constraint be static or a bare discriminant (RM 3.8(12)) is why `Work` has a discriminant `B_Last` rather than `Last_Layer + 1`; and a discriminant that bounds an array indexed by `Index` must itself be of type `Index`, or the range check on the component cannot be proved (the one verification condition of this block that failed, `ligero_verifier.adb:654`, before three discriminants went from `Natural` to `Index`).

### 3.5 Memory, and the supported scale

Bytes per object, on GF(2^128) and on P-256 (an element is 16 or 32 bytes; a `Natural` 4; a digest 32):

| object | GF(2^128) | P-256 | where |
|--------|-----------|-------|-------|
| a term of the circuit | 32 | 48 | heap, the circuit |
| a term of the constraint matrix A (`Ligero_Terms`: coefficient, constraint, witness) | 24 | 40 | heap, `Zk_Verifier.Work`; about 165 per layer plus one per private input |
| a private input in the stage 3 input constraint (three expressions) | about 70 | about 120 | stack, chapter 3 Section 3.5 |
| a witness slot in the constraint vector of the linear test | 16 | 32 | heap, `Ligero_Verifier.Work` |
| a queried column: NROW column elements, BLOCK + DBLOCK table entries, two evaluations, one nonce | 16 (NROW + BLOCK + DBLOCK + 2) + 32 | 32 (NROW + BLOCK + DBLOCK + 2) + 32 | heap, both records |
| the Merkle path, 2 NCOL digests | 64 NCOL | 64 NCOL | heap, `Zk_Verifier.Work` |

For the two upstream circuits (`sha256`: 12 layers, 98 993 terms, 6657 inputs, 7233 witnesses, rate 3, NREQ 16, NCOL 256, hence BLOCK 51, DBLOCK 101, WR 35, NWROW 207, NROW 213; `ecdsa2`: 11 layers, 48 256 terms, 1042 inputs, 1527 witnesses, rate 4, hence BLOCK 42, DBLOCK 83, WR 26, NWROW 59, NROW 65) the circuit records are 3.2 and 2.3 MB, the two working sets about 0.5 and 0.3 MB together, the input constraint under 0.5 MB on the stack. The supported scale is now the available memory for one circuit and two working sets, with one exception kept from chapter 3: the input constraint of stage 3 still lives on the stack, at about 120 bytes per private input on P-256, so a circuit of some fifty thousand private inputs would need a larger stack; its time is quadratic in the private inputs (seconds here), and both are recorded as the limit to revisit with the prover. A failed allocation is `Storage_Error`, which no SPARK contract can speak of: like stack exhaustion before it, it is outside the proofs (SPARK User's Guide, "Dealing with Storage_Error").

### 3.6 The release project and the command-line verifier

`cli/longfellow_verify.gpr` compiles the library without assertions and with optimisation: run-time checks stay on (the proofs establish they cannot fail), executable contracts do not run. `longfellow_verify` takes the field, the circuit file, the proof file, the label, the Ligero configuration and the public inputs, loads the circuit, verifies the proof under the circuit's identifier and prints the status; exit status 0 on `Ok`, 1 on any other status, 2 on a usage or file error. It is `SPARK_Mode (Off)`: it reads files and writes to the terminal, and everything it calls is the SPARK library. `interop_kat` lives in the same project for the reason of Section 5.3.

## 4. What the proofs guarantee

### 4.1 For all inputs

- No run-time error in the loader on any byte string, including the ownership checks: no null or dangling dereference, every allocation freed on every path that does not return it, no aliasing.
- On `Ok`, the returned circuit satisfies `Well_Formed`, so the verifier's precondition holds, and its identifier is the one the file stored.
- `Uleb128.Read` returns the value of the bytes it consumed, one to four of them, and fails exactly when no terminating byte lies within four bytes; `Zigzag` is its definition.
- The two verifiers with their working sets on the heap: the same contracts as chapter 5, plus the ownership checks.

What the proofs do not say: that the expansion of deltas, segments and tokens is upstream's, or that `Compute_Id` is upstream's `compute_id`. Both are tested.

### 4.2 The verification condition table

GNATprove 16.1 with the project's prover configuration ([ADR 0020](../adr/0020-prover-configuration-step-budget.md)), the whole project at the close of Phase B: 11 967 checks, all proved, no justification, no `pragma Assume`; maximum steps 429 702, unchanged since stage 2. Proved checks by partition, from the per-unit lines of the report:

| partition | checks | units |
|-----------|--------|-------|
| `p256` | 3492 | `P256_Field` 3487, `Field_P256` 5 |
| `primitives` | 513 | `GF2_128` 58, `Field_GF2_128` 8, `Bytes` 49, `Sha256` 12, `Aes256` 33, `Transcript` 89, `Fisher_Yates` 58, `Merkle` 206 |
| `sumcheck` | 1971 | the algebra 574 and 604, the expressions 362 and 431 |
| `protocol` | 1462 | the verifier cores 482 and 537, the transcript glue 208 and 235 |
| `ligero` | 725 | geometry 49, Lagrange 111 and 123, the proof readers 216 and 226 |
| `verifier` | 1945 | the Ligero verifiers 741 and 807, the complete verifiers 190 and 207 |
| `circuits` | 584 | `Uleb128` 44, the loaders 267 and 273 |

The `circuits` partition proves in about seven minutes locally with ten provers; with sixteen open verification conditions, before their fixes, the same run took thirty-five, since an unproved check costs each of the three provers its full timeout. Reproduce with `make prove`; the summary is in `obj/development/gnatprove/gnatprove.out`.

## 5. What is only tested

### 5.1 Tier 1: the upstream files

`tests/vectors/upstream/circuits/` holds the two circuits upstream ships with inputs and proofs, copied unchanged and pinned by SHA-256 in the README there. `gen_circuit_vectors.py` parses them with its own LFC2 reader, written from the production code, and writes their layer counts, widths, term counts and identifiers to `circuit_summary.txt`, which `circuit_kat` compares with what `Circuit_Reader` loads. The generator computes `compute_id` independently and aborts unless it equals the identifier each upstream file stores: that is what anchors both transcriptions of the hash on upstream.

### 5.2 Tier 2: an independent reader and writer

The same generator writes the Appendix B.3 circuits and the Z-assertion circuit of chapter 3 in LFC2, in the two encodings of Section 1.3, with their identifiers; `circuit_kat` loads them and compares every term with the term lists the stage 3 vectors were generated from. Then 28 malformed files, each built from the B.3.3 circuit with one defect and the status it must give (a wrong magic, a wrong field, `ncopies` 2, each bound exceeded, a five-byte integer, a constant index, a delta index and a token out of range, a non-canonical P-256 constant, truncations at each section, a trailing byte, a wrong identifier, a wire outside its layer, a width above 2^logw, a last layer not reading `ninput`, `npublic` above `ninput`, a negative prefix sum); the Python reader returns the same status enumeration and the generator aborts if it disagrees with the intended status. 121 cases, in the assertion-enabled test build, about a second.

### 5.3 Tier 3: the two upstream proofs end to end

`interop_kat` loads each upstream circuit from its file, reads the proof file, and runs `Zk_Verifier.Verify` under the circuit's identifier, the label and the configuration of the upstream reference test (`sha256_spec_test`, rate 3, 16 queries, 256 columns; `ecdsa2_spec_test`, rate 4, 16 queries, 256 columns), with no public inputs, since neither circuit has any. Both proofs are accepted: `sha256` on GF(2^128) in 1.3 seconds (the circuit loads in 0.04), `ecdsa2` on P-256 in 1.0 second. Then three copies of each proof with one byte altered, in the root, in the sumcheck part and in the Ligero part: all six are refused with `Merkle_Failed`, because every byte of the proof is absorbed by the transcript before the columns are chosen, so an altered byte moves the chosen columns and the Merkle check fails first; the statuses are recorded in `interop.txt` and checked, so that a regression that changes a status while still refusing is seen. The command-line verifier accepts the same two proofs and refuses them under a wrong label (`merkle_failed`, exit status 1).

`interop_kat` runs in the release project, not in the assertion-enabled test build, and this is a limit of coverage to state plainly. With assertions on, the postconditions of stage 3 quantify over the positions of the stored pairs and the `Expression` of the input constraint is quadratic in the private inputs; one run on the 6657 inputs of `sha256` was stopped after thirty-five minutes. The contracts of stage 3 are proved for all inputs, and their execution is exercised on the Appendix B.3 circuits in `sumcheck_kat`; on real data what is tested is the verdict, on the binary code the project delivers. Moving those postconditions to the proof-only level, as ADR 0044 did for the fields, would have lost exactly that execution on B.3, and was not taken (ADR 0048).

## 6. What stays trusted, and the limits

- `Storage_Error`: a failed allocation raises, and no contract says so; the supported scale is the available memory.
- GNAT's in-place construction of an aggregate allocator, observed in the spike at 2^25 terms, not a language guarantee; a compiler that built the aggregate on the stack would show it there.
- The LFC2 files as to meaning, until Phase D reimplements the compiler: the loader proves their shape and checks their identifier, not what they compute.
- The production reader as the definition of the format, and the two upstream files as what d5e6be7 ships (pinned by hash).
- That the upstream prover's proofs are valid, which its own tests assert; this project confirms that it accepts them.
- The stage 3 input constraint on the stack and quadratic in time, the one piece of the verifier not yet sized by the heap (update, Phase D: moved to the heap and made linear by [ADR 0056](../adr/0056-linear-input-constraint.md), after the mDoc hash circuit overflowed the default stack in it), adequate for the upstream circuits and recorded for the prover's phase.

What Phase B leaves for later: the prover (Phase C), the additive FFT of the draft in place of Lagrange interpolation when the prover needs the full code, and the scale of an mDoc circuit, which the heap now admits and no vector yet exercises.
