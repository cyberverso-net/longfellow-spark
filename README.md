# longfellow-spark

Naming: the repository is `longfellow-spark`; the Alire crate and the GPR project are `longfellow_spark`, because Alire crate names and Ada project identifiers do not allow hyphens.

A formally verified Ada/SPARK reimplementation of [Longfellow ZK](https://github.com/google/longfellow-zk) (libzk), built progressively: verified field arithmetic first, then a complete verifier consuming upstream-generated circuits as validated data, then the prover, and finally the circuit compiler.

## Status

Phase A, stage 1 (GF(2^128)) complete. `Add`, `Xtime`, `Mul` and `Square` proved Gold at level 2 (Mul and Square proved equal to the ghost Horner reference `Mul_Ref`); `Inv` implemented as a fixed Fermat chain, Silver, total with `Inv (Zero) = Zero`. All 41 verification conditions discharged. Known-answer test harness in place (`tests/`); Mul, Square and Inv checked against upstream-anchored vectors (209 cases). Next: stage 2, the P-256 prime field. Field polynomial verified against the pinned spec (Q(x) = x^128 + x^7 + x^2 + x + 1, Section 2.2.2).

Pinned spec: **IETF draft-google-cfrg-libzk-03 (23 September 2026)**; field definition in Section 2.2.2. Divergences in later draft versions are handled as explicit migrations.

## Trust model

Maintained from day one; every entry is one of proved, tested, or trusted.

- **Proved (by GNATprove):** absence of runtime errors on all SPARK code for all inputs (Silver, project-wide invariant); functional contracts where declared Gold in package headers (currently: `GF2_128.Add`, `GF2_128.Xtime`, `GF2_128.Mul` and `GF2_128.Square`, the latter two proved equal to the ghost reference `Mul_Ref`; that `Mul_Ref` matches the pinned spec's convention is a tested property, not a proved one).
- **Tested (known-answer and interop vectors in `tests/vectors/`):** that `GF2_128.Mul_Ref`, hence `Mul`, matches the pinned spec's convention (bit i of the element is the coefficient of x^i, reduction by Q(x)): `tests/vectors/gf2_128_mul.txt` and `gf2_128_square.txt`, checked by the harness `tests/src/gf2_128_kat.adb`. That `GF2_128.Inv` computes the multiplicative inverse (`Inv (x) = x^-1`, `Inv (beta_i) = g^(65535 - i)`, `E * Inv (E) = 1` on random elements, `Inv (Zero) = Zero`): `gf2_128_inv.txt`, every expected value computed by two independent Python references (Fermat exponentiation and extended Euclid on GF(2)[x]) that must agree, and the harness re-checks `E * Inv (E) = One` at run time. The file carries three tiers: anchors recomputed and verified against the subfield basis constants of the upstream reference implementation (google/longfellow-zk, commit d5e6be7, `docs/specs/rust/src/algebra/gf2_128.rs` and `lib/gf2k/gf2_128_test.cc`), structural cases from the field definition, and seeded random cases from an independent Python reference (`tests/vectors/gen_gf2_128_vectors.py`, schoolbook product then long division, a different structure from `Mul_Ref`).
- **Trusted (declared, to be reduced over time):** the GNAT compiler and GNATprove toolchain; the SMT solvers (CVC5, Z3, alt-ergo); upstream-generated circuit files (until Phase D); the SHA-256 implementation once introduced (until proved or replaced); the pinned specification itself.
- **Out of scope for proofs, compensated:** protocol-level soundness and zero-knowledge (fidelity to spec, cited per step); Fiat-Shamir transcript completeness (spec-derived absorption checklist); constant-time execution (coding discipline, documented per package; the guarantee is scoped to builds with assertions disabled, because enabled contracts and ghost code execute secret-dependent branches at run time, see the gf2_128.ads header).

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
tests/bin/gf2_128_kat                      # default: every vector file under tests/vectors/
```

The harness takes vector file paths as arguments, prints pass and fail counts and exits with a non-zero status on any failure or if no case ran. Vector files are regenerated with `python3 -I tests/vectors/gen_gf2_128_vectors.py`; the generator aborts if its recomputed anchors disagree with the upstream constants it embeds.

## Licence

Apache-2.0.
