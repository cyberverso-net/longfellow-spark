# longfellow-spark

Naming: the repository is `longfellow-spark`; the Alire crate and the GPR project are `longfellow_spark`, because Alire crate names and Ada project identifiers do not allow hyphens.

A formally verified Ada/SPARK reimplementation of [Longfellow ZK](https://github.com/google/longfellow-zk) (libzk), built progressively: verified field arithmetic first, then a complete verifier consuming upstream-generated circuits as validated data, then the prover, and finally the circuit compiler.

## Status

Phase A, stage 1 (GF(2^128)) complete: `Add`, `Xtime`, `Mul` and `Square` proved Gold at level 2 (Mul and Square proved equal to the ghost Horner reference `Mul_Ref`); `Inv` implemented as a fixed Fermat chain, Silver, total with `Inv (Zero) = Zero`; 41 verification conditions discharged; 209 known-answer cases anchored on upstream constants.

Phase A, stage 2 (P-256 base field) complete: `Add`, `Sub`, `Neg`, `Mul`, `Square`, `From_Bytes`, `To_Bytes` proved Gold at level 2 against a ghost big-integer model (`To_Int (Mul (A, B)) = To_Int (A) * To_Int (B) mod p`, for all inputs); canonical form enforced by a type predicate; `Inv` a fixed Fermat chain, Silver, total; 467 known-answer cases anchored on the P-256 base point. Verification condition counts are in `docs/guide/02-p256-field.md`. Next: stage 3, the sumcheck verifier. Field polynomial verified against the pinned spec (Q(x) = x^128 + x^7 + x^2 + x + 1, Section 2.2.2).

Pinned spec: **IETF draft-google-cfrg-libzk-03 (23 September 2026)**; field definition in Section 2.2.2. Divergences in later draft versions are handled as explicit migrations (ADR 0002).

## Documentation

The repository is didactic: every stage has a chapter under `docs/guide/` (the mathematics, the algorithm, the Ada/SPARK implementation explained for a reader new to SPARK, and an honest account of what is proved, tested and trusted, with the verification condition table and the commands to reproduce it), and every non-trivial decision has a record under `docs/adr/`. Start with [docs/guide/README.md](docs/guide/README.md) and [docs/guide/verification-approach.md](docs/guide/verification-approach.md); the decision index is [docs/adr/README.md](docs/adr/README.md). Package headers cite the records and chapters they implement.

## Trust model

Maintained from day one; every entry is one of proved, tested, or trusted (ADR 0003). The reasoning behind the split is in [docs/guide/verification-approach.md](docs/guide/verification-approach.md).

- **Proved (by GNATprove):** absence of runtime errors on all SPARK code for all inputs (Silver, project-wide invariant); functional contracts where declared Gold in package headers (currently: `GF2_128.Add`, `GF2_128.Xtime`, `GF2_128.Mul` and `GF2_128.Square`, the latter two proved equal to the ghost reference `Mul_Ref`; that `Mul_Ref` matches the pinned spec's convention is a tested property, not a proved one; `P256_Field.Add`, `Sub`, `Neg`, `Mul`, `Square`, `Is_Canonical`, `From_Bytes`, `To_Bytes`, proved against the ghost integer model `To_Int` and the ghost prime `P`, where `P` is defined from the limbs of p and the proofs establish that it equals 2^256 - 2^224 + 2^192 + 2^96 - 1 as a polynomial identity in 2^32).
- **Tested (known-answer and interop vectors in `tests/vectors/`):** that `GF2_128.Mul_Ref`, hence `Mul`, matches the pinned spec's convention (bit i of the element is the coefficient of x^i, reduction by Q(x)): `tests/vectors/gf2_128_mul.txt` and `gf2_128_square.txt`, checked by the harness `tests/src/gf2_128_kat.adb`. That `GF2_128.Inv` computes the multiplicative inverse (`Inv (x) = x^-1`, `Inv (beta_i) = g^(65535 - i)`, `E * Inv (E) = 1` on random elements, `Inv (Zero) = Zero`): `gf2_128_inv.txt`, every expected value computed by two independent Python references (Fermat exponentiation and extended Euclid on GF(2)[x]) that must agree, and the harness re-checks `E * Inv (E) = One` at run time. For P-256: that the limbs of `P_Limbs` are the prime of Table 1 and that the encoding is the one of Section 7.2.1 (`p256_add.txt`, `p256_mul.txt`, `p256_bytes.txt`, anchored on b, Gx, Gy of RFC 5903 Section 3.1 through the curve equation Gy^2 = Gx^3 - 3 Gx + b); that `P256_Field.Inv` is the inverse (`p256_inv.txt`, Fermat and extended Euclid references agreeing, `E * Inv (E) = One` re-checked at run time); the Solinas reduction table and the inversion chain are additionally verified by the generator `gen_p256_vectors.py`. The file carries three tiers: anchors recomputed and verified against the subfield basis constants of the upstream reference implementation (google/longfellow-zk, commit d5e6be7, `docs/specs/rust/src/algebra/gf2_128.rs` and `lib/gf2k/gf2_128_test.cc`), structural cases from the field definition, and seeded random cases from an independent Python reference (`tests/vectors/gen_gf2_128_vectors.py`, schoolbook product then long division, a different structure from `Mul_Ref`).
- **Trusted (declared, to be reduced over time):** the GNAT compiler and GNATprove toolchain, including GNATprove's model of `Ada.Numerics.Big_Numbers.Big_Integers` used by the P-256 ghost model; the SMT solvers (CVC5, Z3, alt-ergo); Fermat's little theorem for both `Inv`; the 64-bit target assumption behind `Unsigned_128` (ADR 0012); upstream-generated circuit files (until Phase D); the SHA-256 implementation once introduced (until proved or replaced); the pinned specification itself.
- **Out of scope for proofs, compensated:** protocol-level soundness and zero-knowledge (fidelity to spec, cited per step); Fiat-Shamir transcript completeness (spec-derived absorption checklist); constant-time execution (coding discipline, documented per package; the guarantee is scoped to builds with assertions disabled, because enabled contracts and ghost code execute secret-dependent branches at run time, see the gf2_128.ads header and ADR 0006).

Platinum (full functional correctness of the whole system) is explicitly not a goal.

## Building and proving

Requires [Alire](https://alire.ada.dev) with a GNAT toolchain selected (`alr toolchain --select`).

```bash
alr build
alr exec -- gnatprove -P longfellow_spark.gpr --level=2 --report=all
```

The default proof level is 2; any use of a higher level is recorded in the commit message with its rationale.

## Testing

The test harness lives under `tests/` and is test code outside the proof perimeter (`SPARK_Mode (Off)`). Its project file compiles the library sources directly with `-gnata`, so every contract, loop invariant and ghost function executes at run time: a contract violation surfaces as a test failure. This is therefore not the constant-time build (see the trust model above and the `gf2_128.ads` header); never measure or deploy binaries built from `tests/`.

```bash
alr exec -- gprbuild -P tests/longfellow_spark_tests.gpr -p
tests/bin/gf2_128_kat        # default: the gf2_128_*.txt files under tests/vectors/
tests/bin/p256_kat           # default: the p256_*.txt files (about three minutes with assertions on)
```

Each harness takes vector file paths as arguments, prints pass and fail counts and exits with a non-zero status on any failure or if no case ran. Vector files are rebuilt with `python3 -I tests/vectors/gen_gf2_128_vectors.py` and `python3 -I tests/vectors/gen_p256_vectors.py`; the generators abort if their recomputed anchors disagree with the external constants they embed, and the P-256 generator also re-derives the Solinas reduction table and the inversion chain used by the implementation.

Definition of done, for every commit: `make check` passes. It runs, in order, `alr build`, the full proof at level 2 with unproved checks treated as errors, both harnesses, the vector generators with a comparison against the committed files, and a lint over tracked files; `scripts/check.sh` is the single definition of these steps and `make build`, `make prove`, `make test`, `make vectors` and `make lint` run them one at a time. The GitHub Actions workflow runs the same script, step by step, on every push and pull request to `main`.

## Continuous integration

[![verify](https://github.com/cyberverso-net/longfellow-spark/actions/workflows/verify.yml/badge.svg)](https://github.com/cyberverso-net/longfellow-spark/actions/workflows/verify.yml)

The workflow `verify` (ADR 0018) runs on every push and pull request with the same Alire-provisioned toolchain as the local environment (`gnat_native 16.1.0`, `gprbuild 26.0.1`, `gnatprove 16.1.0`, pinned in `alire.toml` and in the workflow's toolchain string): build, the full proof at level 2 with unproved checks treated as errors, both harnesses, the vector generators compared with the committed files, and the lint, one step each. Ubuntu runs for every change; macOS runs for `main` and manual dispatch. The GNATprove report is uploaded as an artifact of every run. A green badge certifies exactly what `make check` certifies locally, on the pinned toolchain; it says nothing about constant time or about specification fidelity beyond the vectors (see the trust model).

To reproduce locally: `make check`.

Branch model: work happens on a branch per stage or block; changes reach `main` through a pull request, merged only with the `verify` checks green; direct pushes to `main` are not used.

## Licence

Apache-2.0.
