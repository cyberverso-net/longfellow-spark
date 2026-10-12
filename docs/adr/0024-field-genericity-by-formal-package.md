# 0024 Field genericity by formal package

## Status

Accepted (2026-10-12, after block 2 of stage 3)

## Date

2026-10-12

## Context

The sumcheck algebra and the symbolic core are the same code over GF(2^128) and over the P-256 base field; only the element type, the operations and three constants differ (Section 6.4: P2 = inj(2) on GF(2^128), P2 = 2 on fields of odd characteristic). The two field packages have different representations (two 64-bit limbs; four limbs under a canonical-form predicate) and different contracts (`Mul_Ref`; the `To_Int` model). Writing the protocol code twice would double the proof surface and let the two copies drift.

Ada generics are the SPARK way to write code once over several types. GNATprove does not analyse a generic unit itself; it analyses each instance, with the actual types and the contracts of the actual subprograms visible, so a proof is obtained per instance and is as strong as the actuals allow. A *formal package* parameter (`generic with package F is new Field_Signature (<>);`) lets a generic take a whole bundle of type, constants and operations as one parameter, instead of listing a dozen formal subprograms at every instantiation; the bundle is itself a generic package with formal parameters only, a *signature package*, whose instances carry no code.

## Decision

- A signature package `Field_Signature`, generic with formal parameters: `type Element is private;` `Zero, One, P2 : Element;` the functions `"+"`, `"-"`, `"*" : (Element, Element) return Element;` `Neg : Element return Element;` the three constants `L0_Den_Inv, L1_Den_Inv, L2_Den_Inv : Element`, the inverses of the Lagrange denominators of [ADR 0025](0025-polynomials-and-lagrange-constants.md); and a ghost function `Same (A, B : Element) return Boolean`, the logical equality of the type ([ADR 0023](0023-gold-perimeter-for-protocol-code.md)). The predefined `"="` of the formal private type is used for the semantic tests of the code.
- Two thin wrapper packages, `Field_GF2_128` and `Field_P256`, each holding the constants, the `Same` function (annotated `Logical_Equal`, body outside SPARK returning the predefined `=`) and a single inner instance `Sig` of `Field_Signature` naming the operations of the concrete package.
- The protocol packages, `Sumcheck_Algebra` first and the symbolic core after it, are generic over `with package F is new Field_Signature (<>)` and are instantiated once per field in the library: `Sumcheck_Algebra_GF2_128` and `Sumcheck_Algebra_P256`. Both instances are library units of `longfellow_spark.gpr`, so `make prove` proves both and the verification condition table counts both.
- Inside the generic the formal operations are reached through wrappers without postconditions ([ADR 0023](0023-gold-perimeter-for-protocol-code.md)); the generic code never names a concrete field, never calls `Inv`, and never relies on an identity that the formal operations do not give it.
- Prerequisites in GF2_128: a function `Neg (A : Element) return Element` with `Post => Neg'Result = A` (negation is the identity in characteristic 2, Gold trivially), and `Sub` as a declared function with `Post => Sub'Result = Add (A, B)` in place of the former expression function. P256_Field already has `Sub` and `Neg` with value-level postconditions.

## Alternatives considered

- **Two copies of the protocol code, one per field.** Rejected: twice the proof and test surface, and drift between the copies would be invisible to the proofs.
- **Individual formal subprograms on each generic (`with function "+" ...` and so on).** Rejected: eight to ten parameters repeated at every instantiation, no single place where "a field, as this project sees it" is written down; the signature package is that place.
- **Tagged types with an abstract field interface and dispatching.** Rejected: dynamic dispatch brings nothing here (the field is fixed at compile time), and dispatching calls are harder to prove than instantiated ones (class-wide contracts, Liskov conditions).
- **A single field type with a discriminant selecting the arithmetic at run time.** Rejected: every element would carry the tag and every operation a branch; the proofs would have to carry the discriminant through every contract.

## Consequences

- Every proof of the protocol code is done twice, once per instance, with different actual contracts; a kernel may prove on one instance and need an extra assertion on the other. Both must prove for `make check` to pass.
- The signature package is the project's definition of a field for protocol purposes. Adding a field (GF(2^16) for the subfield, p384) is one instantiation package and one instance, plus its vectors.
- Reading the generic requires knowing formal packages; chapter 3 of the guide explains the construct on first use.
- The vector generator and the harness are organised per field as well ([ADR 0027](0027-sumcheck-vectors-and-upstream-instrumentation.md)).

## Verification impact

- Provable: the generic's contracts, per instance; the structural Gold of [ADR 0023](0023-gold-perimeter-for-protocol-code.md) needs only that the actuals are functions (`Global => null`) and that `Same` is their logical equality; the actual contracts of `Add`, `Sub`, `Mul`, `Neg` are not used (they are hidden by the wrappers).
- Tested: that the instantiation packages name the right operations and constants (a swapped `"+"` and `"-"` on P-256 would prove and fail the vectors); the constants of ADR 0025.
- Trusted: that `Same` of each wrapper is the equality of its element type (body outside SPARK, ADR 0023); the field packages keep their own trust entries.
- Constant time: no requirement ([ADR 0022](0022-stage-3-scope-and-challenges-as-input.md)); the generic code has no branch on element values except the test `k = Zero` on circuit constants, which are public.

## References

- Ada 2022 Reference Manual, 12.7 "Formal Packages"; SPARK User's Guide, "Generic units" (instances are analysed, generics are not).
- draft-google-cfrg-libzk-03, Section 6.4 (P2 per field), Section 2.2.2 (inj).
- google/longfellow-zk at d5e6be7: `docs/specs/rust/src/algebra/mod.rs` (the `Field` trait, `sumcheck_eval_points`, `mone`), `algebra/gf2_128.rs` (`SUBFIELD_BASIS[1]`), `algebra/p256.rs`.
- `src/gf2_128.ads`, `src/p256_field.ads`.
