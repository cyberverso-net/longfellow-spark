# 0050 Randomness as a byte stream, and its sources

## Status

Proposed (2026-10-17, block 1 of Phase C)

## Date

2026-10-17

## Context

The prover needs randomness for the one-time pads of the sumcheck proof, the random rows of the tableau and the Merkle nonces; the verifier needed none. The reference takes it through one trait with one method, `Rng::bytes(len)` (`algebra/random.rs`), and every sampling is built on it: a GF(2^128) element is 16 bytes read by `from_bytes` (`sample_gf2_128`), a P-256 element is 32 bytes read little-endian and rejected when not below p (`sample_p256`, a loop), a subfield element is 2 bytes mapped on the basis (`BinarySubfield::sample`), a Merkle nonce is 32 bytes (`commit_merkle_heap`). The order of consumption is fixed by the code: in `ZkProver::commit`, the pads layer by layer (per round the two pads of hand 0 then the two of hand 1, then the two claim pads, `LayerPad::sample`), then the tableau rows (`layout_tableau`: BLOCK elements for the LDT row, DBLOCK for the linear row, DBLOCK for the quadratic row, NREQ per witness row, in the subfield for the rows wholly below the subfield boundary, then per quadratic row NREQ for x, NREQ for y, NREQ for z), then one 32-byte nonce per committed column (NCOL minus DBLOCK of them, all before any leaf is hashed). The proving step consumes none: it reads the transcript.

The reference test seeds a linear congruential generator, `SimpleRng` of `tests/test_reference.rs` (state times 6364136223846793005 plus 1442695040888963407, one byte per step from bits 32 to 39), and the shipped proofs are its output; byte identity with them is reachable only by consuming the same bytes in the same order.

## Decision

- **The prover takes its randomness as a byte stream**, through a generic formal: `with procedure Fill (B : out Byte_Array);`, which fills any array it is given with fresh bytes. `Sampling` is generic over it (together with the field), and the prover units are generic over an instance of `Sampling`, so that every proof about them holds for any source; nothing in the proofs depends on the bytes being random.
- **Every sampling is built on that stream exactly as the reference builds it**, in a package `Sampling` generic over the field: 16 bytes for a GF(2^128) element, 32 bytes with rejection below p for a P-256 element (the loop is literal, as in [ADR 0030](0030-literal-rejection-sampling.md), declared possibly non-terminating), 2 bytes for a subfield element through `GF2_128.Inject`, 32 bytes for a nonce; in the order of the Context.
- **Sources.** The generator of the upstream test, `Simple_Rng`, is implemented once as a SPARK library package in `src/` (a package with one abstract state, `Seed` and `Fill`), used by the test project and by the command-line prover behind the explicit option `--seed N`, documented as a test option and never the default: it makes the output reproducible, and it makes it predictable. It lives in `src/` and not in `tests/` because the instances of the prover units are library-level units (one per field, as every other instance of the repository) and must name their source at instantiation; a second source would mean a second set of instances. The package is proved like the rest of the library, which costs nothing and settles its absence of run-time errors. The default source of the command-line prover is the operating system's cryptographically secure generator, read by code outside SPARK (`SPARK_Mode (Off)`, in `cli/`) and listed as trusted; `/dev/urandom` is its realisation on macOS and Linux at this date, and the decision does not depend on the path.
- **Chapter 7 states the consequence of a weak source:** the pads and the random rows are what makes the proof zero-knowledge; a predictable source lets a verifier recover the witness from the proof, and does not let a prover make the verifier accept a false statement, whose soundness rests on the transcript's challenges, not on the prover's randomness.

## Alternatives considered

- **A generic formal `Random_Source` type with a state.** Rejected: the procedure formal is the smallest interface that matches the reference's trait, and a source with state is one instance of it.
- **Sampling inside the fields** (`Sample` as a formal of `Field_Signature`). Rejected: the signature stays what the verifier needs; the prover's sampling is one generic package over it.
- **A SPARK generator for production** (a DRBG in SPARK over `Aes256` or `Sha256`). Not now: it would need seeding from the operating system anyway, and the trusted item would move, not vanish; it is the route if the trust on the operating system's generator is to be reduced.
- **Consuming randomness in a simpler order.** Rejected, as in ADR 0049.

## Consequences

- One more generic formal on the prover units, and a `Sampling` package proved once per field and per source (`Sampling_GF2_128`, `Sampling_P256` over `Simple_Rng`).
- `src/` holds `Simple_Rng` and the instances of the prover units over it, which the test project uses; `cli/` holds the operating system source `Os_Random` (`/dev/urandom`), outside SPARK, and one chain of instances over `Cli_Random.Fill`, a procedure that reads `Os_Random` unless `--seed` was given and then reads `Simple_Rng`: one source procedure, hence one chain of instances in the command-line prover, chosen at run time (block 5; the generic instantiation of the prover chain inside the command-line program's generic body was refused by the compiler on the identity of the formal packages, and a run-time switch in the source is simpler than two chains).
- The README trust model lists the operating system's generator as trusted for the zero-knowledge property of proofs made by `longfellow_prove`.

## Verification impact

- Provable: absence of run-time errors for any byte stream; the counts of bytes consumed per sample (the postconditions state how many bytes each sampling takes); the rejection loop as ADR 0030.
- Tested: byte identity with the upstream proofs under `Simple_Rng`, which exercises the order and the counts.
- Trusted: the operating system's generator; that `Simple_Rng` is the upstream test's generator (transcribed, and confirmed by the byte identity).
- Constant time: sampling depends on the randomness, not on the witness (ADR 0051).

## References

- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/algebra/random.rs`, `algebra/gf2_128.rs` (`sample_gf2_128`, `BinarySubfield::sample`), `algebra/p256.rs` (`sample_p256`), `sumcheck/pad.rs`, `ligero/prover.rs` (`layout_tableau`), `merkle.rs` (`commit_merkle_heap`); `docs/specs/rust/tests/test_reference.rs` (`SimpleRng`).
- [ADR 0030](0030-literal-rejection-sampling.md), [ADR 0049](0049-phase-c-scope-the-prover.md), [ADR 0051](0051-constant-time-in-the-prover.md).
