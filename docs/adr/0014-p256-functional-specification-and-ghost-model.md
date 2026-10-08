# 0014 P-256 base field: functional specification and ghost model

## Status

Accepted (2026-10-09, after review)

## Date

2026-10-09

## Context

Stage 1 specified multiplication by a ghost reference with the same algebraic structure (Horner). For a prime field the natural specification is the integer value: `To_Int (Mul (A, B)) = (To_Int (A) * To_Int (B)) mod P`. Ada 2022 provides `Ada.Numerics.Big_Numbers.Big_Integers`, which GNATprove supports in ghost code (the SPARK library's `SPARK.Big_Integers` is a renaming of it, GNATprove 16.1). SPARKNaCl, the closest published SPARK precedent, does not state a value-level specification; it proves type safety and limb bounds. So the feasibility of the value-level statement at level 2 had to be established, not assumed.

A feasibility experiment on 2026-10-09 (GNATprove 16.1, level 2) analysed a four-limb model:

- `Conv (X)` = `To_Big_Integer (X)` from an instance of `Unsigned_Conversions (Unsigned_64)`; `Two_64` defined as `Conv (Unsigned_64'Last) + 1` (defining it as `2 ** 64` left `Conv'Result < Two_64` unproved);
- `Weight (I)` = 2^(64 I) and `Partial (L, N)` = value of limbs 0 .. N - 1, both recursive ghost expression functions with `Subprogram_Variant`;
- `Add_Limbs` with carry, postcondition `To_Int (R) + Carry * 2^256 = To_Int (A) + To_Int (B)`, loop invariant on `Partial`.

Result: the postcondition and invariant were proved once a lemma `Conv128 (X) = Conv (Lo (X)) + Conv (Hi (X)) * Two_64` was available, and that lemma was itself proved from `X / 2^64`, `X mod 2^64` and their equality with the shift and mask forms, with no axiom and no `pragma Assume`. Without the lemma, the per-limb carry step was not proved at level 2 and not at level 4 either: the gap is the connection between modular word arithmetic and the big-integer value, which must be supplied as a lemma. All 94 checks of the final experiment were discharged at level 2.

## Decision

- The model is `To_Int : Element -> Big_Integer`, a ghost expression function over the four limbs, with `P : constant Big_Integer` as the ghost prime. All functional contracts are stated as equalities of `To_Int` values modulo `P`, plus canonical form ([0015](0015-p256-canonical-form-and-conditional-subtraction.md)).
- Gold targets: `Add`, `Sub`, `Neg`, `Mul`, `Square` (as `Mul (E, E)` by composition, as in [0007](0007-square-as-wrapper-over-mul.md)), `From_Bytes` (value and canonical check), `To_Bytes` (round trip). `Inv` is Silver plus vectors ([0016](0016-p256-inversion.md)).
- Lemmas are ghost procedures whose bodies prove their postconditions by assertions, as the split lemma did. A lemma with a null body is an axiom and is not accepted; `pragma Assume` is not used. Where the standard SPARK lemma library (`SPARK.Lemmas.Arithmetic`, `SPARK.Lemmas.Mod_Arithmetic`) has what is needed, it is used and listed as trusted (it is proved by AdaCore, some lemmas at higher levels).
- Level stays at 2. If a step of `Mul` does not discharge at level 2, the fallback is staged, in this order: split the step further with intermediate assertions; add a lemma; only then request a higher level for that unit with a recorded rationale; and as a last resort declare that step Silver plus vectors in the header and the README.
- Expected lemma inventory for `Mul`: the split lemma; a column-accumulation lemma (sum of up to four 128-bit products plus a carry fits a stated bound and equals the model sum); the fold identity 2^256 = 2^224 - 2^192 - 2^96 + 1 mod p as a `Big_Integer` equality; the conditional subtraction lemma. The exact list is recorded in the chapter when the proofs are done.

## Alternatives considered

- **A ghost reference implementation, as in stage 1** (for example schoolbook over limbs in ghost code). Rejected: it would only prove `Mul` equal to another limb algorithm and leave the value-level statement to tests; the value model is what makes the P-256 proofs worth their cost.
- **Bounded types instead of a model** (SPARKNaCl style). Rejected as the specification; retained as a technique for bounding intermediate words.
- **Mathematical integers through `Big_Integer` in executable code.** Not applicable: `Big_Integer` is ghost-only here and would not be constant time.

## Consequences

- Ghost code grows (model, lemmas); none of it is in the executable with assertions disabled.
- The test build ([0010](0010-assertion-enabled-test-project.md)) executes `Big_Integer` arithmetic in every postcondition; expect it to be slow and keep vector counts moderate.
- A reader can check the specification by reading `To_Int` and `P` only.

## Verification impact

- Provable: value-level correctness of the Gold list for all inputs, modulo the lemmas, which are themselves proved.
- Tested: everything in the Gold list is also run against vectors (belt and braces), `Inv` by vectors only.
- Trusted: `Ada.Numerics.Big_Numbers.Big_Integers` semantics as modelled by GNATprove; any lemma taken from the SPARK lemma library.
- Constant time: ghost only; scope as [0006](0006-constant-time-discipline-and-scope.md).

## References

- GNATprove 16.1 distribution: `include/spark/full/spark-big_integers.ads`, `include/spark/spark-lemmas-arithmetic.ads`, `include/spark/spark-lemmas-mod_arithmetic.ads`.
- SPARK User's Guide, "Ghost code", "Manual proof using ghost code (lemmas)".
- SPARKNaCl README and `src/sparknacl-utils.ads` (no value-level contracts), read 2026-10-09.
