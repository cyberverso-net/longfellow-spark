# 0074 The command line checks the identifier of a known circuit once, not on every load

## Status

Proposed (2026-10-27, milestone M2 of Phase D). Amends [ADR 0046](0046-phase-b-scope-lfc2-loader-and-interop.md) for the command line: `Read` still recomputes the identifier; the command line loads the circuits of a fixed list without recomputing it.

## Date

2026-10-27

## Context

`Circuit_Reader.Read` recomputes the identifier of every circuit it loads and refuses a file that stores another (ADR 0046). The identifier is the SHA-256 of a canonical form that writes every integer as eight bytes.

- The mDoc hash circuit has 7.76 M terms. Its identifier hashes 310 MB, for a file of 1.18 MB.
- On the proving machine this costs about 2.2 s in each hash proof and each hash verification. After ADR 0073 it is the largest single item of the hash verification, 4.90 s in all.
- Upstream does not check it in the mDoc application, in the prover or in the verifier (`lib/circuits/mdoc/mdoc_zk.cc`, `enforce_circuit_id_in_prover` and `enforce_circuit_id_in_verifier` are false; the Rust runtime passes `false` to `from_bytes`). Its comment states the model: the application holds a list of supported circuits, checks the identifier once after downloading or compiling a circuit, and then keeps the checked circuit in trusted storage.
- So the upstream rows that M2 compares with do not include this cost.

## Decision

**A second loader, `Read_Pinned`, and a fixed list of checked circuit files in the command line.**

- `Read_Pinned (B, Id, C, H, St)` does everything `Read` does except recompute the identifier. On `Ok` the stored identifier equals `Id`; a file that stores another is refused with `Id_Mismatch`. Its postcondition states `H.Id = Id` where `Read` states `H.Id = Compute_Id (C.all, H.Subfield_Boundary)`; the rest is the same. `Read` and its contract are unchanged.
- `Pinned_Circuits`, in `cli/src/`, lists the circuit files whose identifier was checked: for each, the SHA-256 of the file bytes and the identifier a full `Read` recomputed. Today the three mDoc circuits of the two v7 archives at d5e6be7 (the two archives share their signature circuit).
- `longfellow_prove` and `longfellow_verify` hash the file bytes. A file in the list is loaded by `Read_Pinned` under its listed identifier; any other by `Read`. `--check-circuit-id` makes both use `Read`.
- `interop_kat` checks every entry: the file has the listed digest, a full `Read` recomputes the listed identifier, `Read_Pinned` gives the same circuit and header, and `Read_Pinned` under another identifier refuses the file.

The key of the list is the digest of the whole file, not the identifier the file stores: a file that differs in any byte from the one checked goes through `Read`. Upstream trusts the stored identifier.

## Alternatives considered

- **Keep the check on every load, and declare the difference of scope.** Rejected: it leaves the largest item of the hash verification in place, for a property of a file that does not change between runs.
- **Make the check optional inside `Read`, as upstream's flag.** Rejected: the same gain with a conditional, weaker postcondition on the main loader, and a file that is not known would be trusted too.
- **A digest file next to each circuit.** Not taken: a second file to keep with each circuit, and to trust. Upstream keeps its list of circuits in the code (`ZK_SPECS` of the Rust runtime).
- **Make the identifier cheaper.** Feeding `Compute_Id` through a buffer instead of eight bytes at a time takes about a quarter off its time on the development machine. Kept in reserve: independent of this decision, and the check would still run on every load.

## Consequences

- Measured on the development machine, the hash verification: 2.21 s with the pinned circuit, 6.24 s with `--check-circuit-id`. Times on the proving machine to be recorded here.
- The proofs of the CLI stay identical byte for byte.
- A file in the list that has been altered goes through `Read`. Altering its stored identifier gives `id_mismatch`, as before.
- A new circuit gets the fast path only when it is added to the list, with its digest and its identifier, and `interop_kat` checks the new entry against its file.
- Guide chapter 6, the trust model, the CHANGELOG and ADR 0046 are updated.

## Verification impact

- `Read_Pinned` and `Read` share one body, `Load`, whose postcondition is conditional on which check it makes. `Read` keeps its postcondition.
- `Read_Pinned` proves the same absence of run-time errors, `Well_Formed`, `Isolated` and `Dead_End` as `Read`. It does not prove that the identifier is the circuit's: that is the check of the list, made by `Read` in `interop_kat`.
- Trusted, newly: the list of `Pinned_Circuits` and the code in `cli/src/` that chooses the loader. Both are outside the proofs, like the rest of `cli/src/`.
- No `pragma Assume`, no contract weakened.

## References

- [ADR 0046](0046-phase-b-scope-lfc2-loader-and-interop.md), [ADR 0073](0073-verifier-binds-the-quad-as-upstream.md).
- google/longfellow-zk at d5e6be7: `lib/circuits/mdoc/mdoc_zk.cc` (the flags and their comment), `rust/applications/mdoc_zk/runtime/src/proto.rs`, `rust/applications/mdoc_zk/runtime/src/zk_spec.rs` (`ZK_SPECS`; `combined_hash` is the SHA-256 of the two circuit identifiers), `rust/core/proto/src/reader/lfc2.rs` (`enforce_circuit_id`).
