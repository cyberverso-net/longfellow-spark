# longfellow-spark

Naming: the repository is `longfellow-spark`; the Alire crate and the GPR project are `longfellow_spark`, because Alire crate names and Ada project identifiers do not allow hyphens.

A formally verified Ada/SPARK reimplementation of [Longfellow ZK](https://github.com/google/longfellow-zk) (libzk), built progressively: verified field arithmetic first, then a complete verifier consuming upstream-generated circuits as validated data, then the prover, and finally the circuit compiler.

## Status

Phase A, stage 1 (GF(2^128)) in progress. `Add`, `Xtime`, `Mul` implemented and proved (Gold, all VCs discharged at level 2; Mul proved equal to the ghost Horner reference Mul_Ref). `Square`, `Inv` and the known-answer test harness pending. Field polynomial verified against the pinned spec (Q(x) = x^128 + x^7 + x^2 + x + 1, Section 2.2.2).

Pinned spec: **IETF draft-google-cfrg-libzk-03 (23 September 2026)**; field definition in Section 2.2.2. Divergences in later draft versions are handled as explicit migrations.

## Trust model

Maintained from day one; every entry is one of proved, tested, or trusted.

- **Proved (by GNATprove):** absence of runtime errors on all SPARK code for all inputs (Silver, project-wide invariant); functional contracts where declared Gold in package headers (currently: `GF2_128.Add`, `GF2_128.Xtime`, `GF2_128.Mul`, the latter proved equal to the ghost reference `Mul_Ref`; that `Mul_Ref` matches the pinned spec's convention is a tested property, not a proved one).
- **Tested (known-answer and interop vectors in `tests/vectors/`):** nothing yet.
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

## Licence

Apache-2.0.
