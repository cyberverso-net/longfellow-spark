# 0046 Phase B scope: the LFC2 circuit loader and the interop exit criterion

## Status

Accepted (2026-10-17, at the close of block 3 of Phase B; proposed 2026-10-16 and edited until then)

## Date

2026-10-16

## Context

Phase A ends with a verifier from the proof string to a verdict on the explicit circuits of the draft ([ADR 0035](0035-stage-5-scope-ligero-and-the-complete-verifier.md)). Of the four items the project plan gave Phase B, three are done: the evaluator with its semantics is Gold since stage 3, the Ligero verifier and the proof reader with the top-level `Verify` since stage 5. What remains is the first item, the circuit loader ([ADR 0011](0011-circuits-as-data.md): parse the upstream format, validate well-formedness, absence of run-time errors on arbitrary bytes), the memory redesign that real circuits force ([ADR 0039](0039-sizes-allocation-and-status.md), chapter 3 Section 3.5), and the exit criterion: proofs produced by the upstream prover on upstream circuits, accepted byte for byte.

The circuit format is not in the pinned draft, which defines the quad representation (Section 6.3) and the serialisation of proofs (Section 7) only. Upstream defines **LFC2** at d5e6be7 in `rust/core/proto/src/writer/lfc2.rs` and `rust/core/proto/src/reader/lfc2.rs` (the production reader, with its bounds and its error cases) and in a simplified copy, `docs/specs/rust/src/circuit/lfc2.rs`, which asserts instead of reporting. The layout: the magic `LFC2`; ULEB128 integers of at most four bytes, hence below 2^28 (`field_id`, `nv`, `ncopies`, which must be 1, `npublic_input`, `subfield_boundary`, `ninput`, `nl`); a table of constants, each an element of Section 7.2.1; per layer `logw`, `nw`, a table of deltas (g, h0, h1 zigzag-encoded, an index into the constants), a dictionary of segments (sequences of delta indices) and a sequence of tokens (segment indices) whose expansion by prefix sums over the deltas is the layer's term list; then 32 bytes of identifier, the SHA-256 of the canonical form (`compute_id`). Field identifiers come from `lib/proto/circuit_io.h`: P-256 is 1, GF(2^128) is 4.

Upstream ships two circuits with inputs and proofs under `docs/specs/rust/tests/testdata/`, produced by its prover and accepted by its verifier (`test_reference.rs`):

| circuit | field | layers, max logw | terms | inputs (public) | configuration | proof |
|---------|-------|------------------|-------|-----------------|---------------|-------|
| `sha256` | GF(2^128), subfield boundary 3000 | 12, 15 | 98 993 | 6657 (0) | rate 3, NREQ 16, NCOL 256 | 49 936 bytes, label `sha256_spec_test` |
| `ecdsa2` | P-256 | 11, 13 | 48 256 | 1042 (0) | rate 4, NREQ 16, NCOL 256 | 56 268 bytes, label `ecdsa2_spec_test` |

Both lie within the bounds of stage 3 and 5 (`Max_Wires` 2^24, `Max_Layers` 64, `Max_Logw` 40, `Max_Terms` 2^28, `Max_Witnesses` 2^25). The circuit records are a few megabytes; an mDoc circuit (about one megabyte of compressed LFC2 upstream) has millions of terms and does not fit a default stack.

## Decision

- **Phase B is the loader, the heap and the interop.** Blocks: 1, this record with [ADR 0047](0047-heap-allocation-by-ownership.md) and [ADR 0048](0048-circuit-vectors-and-interop-proofs.md) and the allocation spike; 2, the loader with the identifier and the tier 2 vectors; 3, the working set of `Verify` on the heap, the two upstream proofs end to end and the command-line verifier; 4, chapter 6, the README and the partitions.
- **LFC2 is the interface, as the production reader at d5e6be7 defines it.** The acceptance rules of `reader/lfc2.rs` are transcribed: the magic, the ULEB128 limit of four bytes, `ncopies` equal to 1, the field identifier of the instance, every index in range at the point it is read (constant index, delta index, token), the identifier recomputed and compared. Where this project is stricter it says so: the bounds are the project's (`Max_Layers` 64 against 10 000, `Max_Wires` 2^24 against 5 000 000, `Max_Terms` 2^28 against 20 000 000, `Max_Logw` 40 as upstream), and the loaded circuit must satisfy `Well_Formed` of stage 3, which upstream does not check (every wire index below its layer's width, `nw <= 2^logw`, the last layer's width equal to `ninput`); a circuit that upstream would load and then misuse is refused here with a status.
- **The loader** is a generic `Circuit_Reader` over an instance of `Sumcheck_Algebra`, with the field identifier and the binary flag as formals, instantiated for both fields. `Read (B, C, Header, St)` takes the bytes, makes two passes (the first validates and counts the terms, the second allocates once and fills), and returns the circuit on the heap (ADR 0047), a header record (`Field_Id`, `Subfield_Boundary`, kept for Phase C, `Id`) and a status. Silver on arbitrary bytes; postcondition: on `Ok` the circuit satisfies `Well_Formed` and `Id` is its identifier. `Logv` is not stored: the core derives it from `Noutput` as it does today. The identifier is always recomputed (`Compute_Id`, SHA-256 of the canonical form, through `Sha256`) and a mismatch is a status: the cost is one hash over a few megabytes, and a file whose identifier does not match is a file to refuse, since the identifier is what the transcript binds (`Write_Sumcheck_Statement`).
- **Errors are the enumeration** `Circuit_Status`: `Ok, Bad_Magic, Field_Mismatch, Unsupported_Copies, Bad_Integer, Bound_Exceeded, Bad_Element, Bad_Index, Truncated, Trailing_Bytes, Id_Mismatch, Not_Well_Formed`, one value per cause the code can produce (`Bad_Integer` is a ULEB128 of more than four bytes, which the production reader also refuses), no exceptions, as [ADR 0039](0039-sizes-allocation-and-status.md) does for the verifier.
- **A command-line verifier**, `longfellow_verify`, outside the proof perimeter (`SPARK_Mode (Off)`, file input and output), in its own project under `cli/`: it takes the field, the circuit file, the proof file, the public inputs, the label and the configuration, loads the circuit, runs `Zk_Verifier.Verify` under the circuit's identifier and prints the status; exit status 0 on `Ok`, 1 on any other status, 2 on a usage error. It is the deliverable of the exit criterion and is exercised by `scripts/check.sh` on the two upstream proofs.
- **Exit criterion:** the two upstream proofs accepted from their files on both fields through the loaded circuits, and refused when a byte is altered.

Out of scope: LFC1 (the C++ format, which upstream reads for compatibility: about a hundred megabytes for an mDoc circuit, superseded by LFC2 in the Rust code); the subfield boundary beyond carrying it (the prover's concern, Phase C); the time of the input constraint of stage 3, quadratic in the private inputs (seconds on these circuits, ADR 0047 states the limit).

## Alternatives considered

- **Supporting LFC1 as well.** Rejected: a second parser for a format upstream is leaving, with a hundredfold larger files.
- **Converting circuits to a text form in Python and loading that.** Rejected: ADR 0011 makes the loader on arbitrary bytes the Silver target; a converter would move the parsing out of the proofs.
- **Following the production reader exactly, bounds included.** Rejected: its bounds suit its allocator; this project's bounds are what the stage 3 proofs assume, and `Well_Formed` is a precondition of the core, so the loader must establish it.
- **Checking the identifier only on request** (upstream's `enforce_circuit_id`). Rejected: the flag exists upstream for files produced before the identifier was fixed; every file this project accepts is checked.
- **Making the identifier the Gold target of the loader** (proving `Compute_Id` equal to a ghost transcription of `compute_id`). Not taken: the identifier is a hash of the structure, and its agreement with upstream is a vector question; the Gold of the loader is `Well_Formed` of the result.

## Consequences

- Real circuits reach the verifier: the README trust model keeps "upstream-generated circuit files" trusted as to what they compute, with their well-formedness proved on load and their identifier checked.
- A new unit family (`Circuit_Reader`, its instances, `Circuit_Status`) and a new proof partition; a new harness `circuit_kat` and the interop cases (ADR 0048); the `cli/` project.
- The two field instances gain nothing; the loader is generic over the algebra, as the verifier is.

## Verification impact

- Provable: absence of run-time errors on arbitrary bytes; on `Ok`, `Well_Formed` of the loaded circuit and the identifier equality; every status tied to its cause where the structure allows.
- Tested: the expansion of deltas, segments and tokens against an independent reference and against the upstream files; the identifier against the one upstream stored; the two upstream proofs end to end (ADR 0048).
- Trusted: the LFC2 files as to meaning, until Phase D; the production reader as the definition of the format; `Storage_Error` on allocation (ADR 0047).
- Constant time: not applicable, as ADR 0037: circuits and proofs are public data.

## References

- google/longfellow-zk at d5e6be7: `rust/core/proto/src/reader/lfc2.rs`, `rust/core/proto/src/reader/mod.rs` (the bounds), `rust/core/proto/src/writer/lfc2.rs`, `rust/core/proto/src/uleb.rs`, `rust/core/proto/src/circuit.rs` (`compute_id`), `docs/specs/rust/src/circuit/lfc2.rs`, `docs/specs/rust/tests/test_reference.rs`, `docs/specs/rust/tests/testdata/`, `lib/proto/circuit_io.h` (`FieldID`).
- draft-google-cfrg-libzk-03, Sections 6.3, 7.2.1.
- [ADR 0011](0011-circuits-as-data.md), [ADR 0022](0022-stage-3-scope-and-challenges-as-input.md), [ADR 0035](0035-stage-5-scope-ligero-and-the-complete-verifier.md), [ADR 0039](0039-sizes-allocation-and-status.md), [ADR 0047](0047-heap-allocation-by-ownership.md), [ADR 0048](0048-circuit-vectors-and-interop-proofs.md).
