# 0089 The supported mDoc profile: its invariants, its two rows, the claim of each row and one entry point per role

## Status

Accepted (2026-11-11, at the merge of pull request #153; proposed 2026-11-10 with #79). Completes [ADR 0058](0058-mdoc-layer.md), whose specification table becomes the rows of the profile, and [ADR 0086](0086-mdoc-witness-bounds-and-constant-time.md), whose bounds become part of its invariants.

## Date

2026-11-10

## Context

The mDoc layer proves an age attribute of a credential with two circuits of upstream's table of specifications (`runtime/src/zk_spec.rs` at d5e6be7). Since block 5 the programs select a row of that table by its combined identifier and check that the circuit files are the row's (`Mdoc_Spec`, ADR 0058); since block 6 they prove from the credential itself (ADR 0086). Issue #79 asks for more: one identified application profile that binds everything a supported proof of age depends on, enforced by the application's entry point, with each security claim naming its theorem, its assumptions and its trusted entries.

Two facts make the question concrete. First, the configuration predicate of `Ligero_Geometry` checks geometry and sizes only: a rate inverse of 7, one query and 64 columns satisfy it, and nothing in the structure of a configuration establishes a security level. The 116-bit result of upstream's Lean development (`LfzkV1.CompiledZk.v7Hash{1,2,3,4}_deployed_fs_extraction_116_circuit` at 7bf8a6b, the [Lean correspondence](../guide/lean-correspondence.md)) is a theorem about the version 7 geometry, rate 1/7 with 132 opened columns, not about any structurally valid configuration. Second, the library's units accept more than the two rows: any version 5 to 7 in the type, any valid configuration, up to four attributes in the public inputs. Only the two rows are pinned and tested.

The facts were set out for the maintainer in a decision note of 10 November (the profile's guarantees and limits, condition by condition), and the six questions it raised were answered by the author the same day; this record writes the answers down.

## Decision

**The profile is a record of invariants plus two rows.** What does not vary is stated once, here and in chapter 9 Section 6; a row holds only what varies.

The invariants, facts of the code for every row:

- the protocol: upstream's `applications/mdoc_zk` at d5e6be7 in its legacy form (versions 6 and 7), two Longfellow proofs over one Fiat-Shamir transcript opened with the session transcript's bytes, the hash circuit over GF(2^128) and the signature circuit over the base field of P-256, Ligero V1 over a padded, layered sumcheck (chapters 3 to 7);
- the binding: the six legacy tags over the digest the issuer signed and the two coordinates of the device key, one-time pads drawn by the prover, the challenge av drawn from the transcript after both commitments (`Mdoc_Mac`, chapter 9 Section 1.3);
- the public inputs: upstream's legacy layouts of both circuits (`Mdoc_Inputs`), e2 over upstream's fixed headers (`Device_Auth`);
- the proof format: the six tags, the hash proof, the signature proof, nothing after (`Mdoc_Proof`);
- the witness: upstream's builders over the parse of the credential (`Mdoc_Parse`, `Mdoc_Witness`), with the bounds of ADR 0086 and, at version 6, the order constraint of the issuer-signed item (#150);
- the circuit files: those of the pinned list of the command line (`cli/src/pinned_circuits.adb`, ADR 0074), each held by its SHA-256 and its identifier.

The rows, what varies (`Mdoc_Spec`, one record each): the version, the number of attributes, the combined identifier (the profile's name), the identifiers of the two circuits, and the two Ligero configurations.

| Name (combined identifier) | Version | Attributes | Hash circuit: rate inverse, queries, columns | Signature circuit: rate inverse, queries, columns |
|---|---|---|---|---|
| `8d079211…6182121` | 7 | 1 | 7, 132, 4,151 | 7, 132, 4,096 |
| `137e5a75…197c7c6` | 6 | 1 | 4, 128, 4,096 | 4, 128, 2,945 |

**"Registered" means, for this project, a row of upstream's `zk_spec.rs` table at the pin, held here by hash.** The rows above are two of upstream's sixteen at d5e6be7 (`ZK_SPECS`; `lib/circuits/mdoc/zk_spec.cc` holds the same table for the C++ code), with the same identifiers and configurations, checked by `mdoc_kat` against a vector file written from the Rust source. When the scheme owner of the age-verification profile publishes a list of accepted circuits, that list becomes a second source: a row is then registered when both name it, and a row that only one names is recorded as such.

**The claim is per row, and the two rows differ.**

- **Version 7.** May cite upstream's Lean certificate: extraction and soundness of the pair of circuits with one attribute at 116 bits of T-security (`v7Hash1_deployed_fs_extraction_116_circuit` and `v7Hash1_deployed_false_statement_116`, at 7bf8a6b), zero knowledge as the correspondence page states it, under the trusted entries of the register: R2 (what the circuits compute, the tag equation each circuit enforces among it), S1 and S2 (the theorems and their ideal objects: the transcript as an ideal coin, the Merkle hash and the transcript as independent random oracles), R8 to R12 (the construction as upstream's code specifies it: the tags, the layouts, e2's headers, the specification table, the curve formulas, the parse). The Lean development is a model of the verifier: the correspondence of this project's verifier with that model is by reading, and the correspondence page lists what is proved of it.
- **Version 6.** May not cite the certificate. The same code, the same proofs of this project and the same protocol theorem by reading (S1 for a Ligero V1 over a padded sumcheck), but no Lean certificate exists for its geometry (rate 1/4 with 128 columns), so no security level is claimed for it; and the order constraint of #150 on the credential. Chapter 9 and the register state the two rows separately.

**Version 6 stays a supported row**, with the caveat beside it: it is tested at every gate on the same code, at no cost in code and seven minutes of the gate.

**Two to four attributes are refused by the entry points** until an archive of upstream with that many attributes is pinned here: both rows hold one attribute, and the entry points refuse any other count with `Attribute_Count`. The layouts for two to four attributes stay in `Mdoc_Inputs` and `Mdoc_Witness`, untested end to end; a Task in Backlog (#152) pins upstream's two-attribute archive and tests it when it is needed.

**The issuer's key and the nonce stay with the relying party.** The verifier takes the issuer's key as given and does not read the certificate chain of the issuer, nor a trust list; it takes the session transcript as given and does not check the freshness or the single use of the nonce inside it, nor the date `now`. Chapter 9 Section 6 says so beside each condition. A trust anchor and an expected nonce are the product of Phase E (the decision note of 8 November on the transport and the repositories), not of this repository.

**One library entry point per role**, taking the profile's name and refusing everything else, called by the programs; the claims are scoped to it.

- `Mdoc_Spec.Select_Profile`: the row named, if the two circuits given are the row's (their identifiers) and the request holds the row's number of attributes; `Profile_Unknown`, `Profile_Mismatch` and `Attribute_Count` otherwise, in that order.
- `Mdoc_Prover.Prove_Profile` (the prover): `Select_Profile`, then that the circuits fit the row's configurations and the three buffers have the row's lengths (`Profile_Mismatch` otherwise), then the proof from the credential (`Prove_Mdoc`) with the row's version and configurations. On every refusal, of the profile, of the request, of the witness or of the proof, the two witnesses and the proof buffer are zero; on success the witnesses hold the credential's secrets, and the caller wipes them once the proof is written.
- `Mdoc_Verifier.Verify_Profile` (the verifier): `Select_Profile`, then `Verify` with the row's version and configurations.

`longfellow_verify_mdoc` calls `Verify_Profile`; `longfellow_prove_mdoc --mdoc` calls `Prove_Profile`; the reference path from upstream's witness files (block 5) checks the profile with `Select_Profile` before `Prove`. The generic entry points (`Prove`, `Prove_Mdoc`, `Verify`, and the single-circuit programs) stay available for reference work, and the claims of this record do not extend to them. What the entry points leave to their caller, as preconditions or as an obligation the contracts cannot state: the bounds of the request (at most four attributes, a date of at most 20 bytes, a document type of at most 65,535 bytes, and for the verifier a proof buffer that starts at zero), the loader's validity of the two circuits (`Circuit_Reader.Read_Packed`'s postcondition), and that the circuits given are the ones their identifiers name: the entry points compare the identifiers with the row's, and the binding of an identifier to a circuit is the loader's, by the identifier it computes or, on the command line, by the SHA-256 of the pinned file (ADR 0074, the register's row C2).

## Alternatives considered

- **A profile object with every parameter as a field**, the field, the transcript context and the MAC composition included. Rejected: those do not vary between the rows; as fields they would suggest a choice the code does not offer.
- **Claim 116 bits for both rows.** Rejected: the Lean certificate is about the version 7 geometry; for version 6 it would be a claim without a theorem.
- **Drop version 6** and keep one supported row. Rejected: the second artifact family is tested on the same code at every gate, and its caveat is stated.
- **Allow two to four attributes now**, as the layouts permit. Rejected: no archive is pinned, so no proof with more than one attribute is made or tested here.
- **A trust anchor for the issuer's key and an expected nonce in the entry point.** Deferred to Phase E: they are a relying party's product, with its own configuration and its own threat model.
- **The profile check in the programs only.** Rejected: the claims are about the library, and the check belongs where they are scoped.

## Consequences

- `Mdoc_Status` gains `Profile_Unknown`, `Profile_Mismatch` and `Attribute_Count`; the programs print them. Two attributes against either row, given to either program, now give `attribute_count` where they gave `input_count`.
- Chapter 9 Section 6 states the profile: the invariants, the two rows, the claim of each, what stays with the relying party. The trust model and the trusted base register state the claim per row.
- A new row needs: the archive pinned by hash, a row of upstream's table at the pin (and of the scheme owner's list, once published), its line in `Mdoc_Spec`, its vectors, its round trip in the gate, and an amendment of this record saying what may be claimed for it.

## Verification impact

- Proved: `Select_Profile` returns a row whose name, circuit identifiers and number of attributes are the ones given, when it accepts (Gold, trivially); `Spec` states that both rows are of version 6 or 7 with one attribute; the two entry points meet the preconditions of the flows they call from the row's values and the checks they make; the statuses of both, and the prover's three buffers zero on every refusal (Silver with these contracts).
- Tested: each row accepted with its own circuits; an unknown name, the other row's hash circuit, an altered signature circuit and zero, two, three and four attributes refused; the prover's entry point on the version 7 circuits refusing each of its three buffers one element short and the proof buffer not starting at zero, and refusing a value of 65 bytes after the witnesses are built (`Attribute_Invalid`), each time with zero buffers and zero length (`mdoc_kat`); two attributes refused by both programs, from the witness files and from the document (the `cli` step).
- Trusted: unchanged; the claim of each row lists its entries.

## References

- Upstream at d5e6be7: `rust/applications/mdoc_zk/runtime/src/zk_spec.rs` (`ZK_SPECS`), `lib/circuits/mdoc/zk_spec.cc`; at 7bf8a6b, `formal/lfzk-v1/README.md` and the theorems named above.
- [ADR 0058](0058-mdoc-layer.md), [ADR 0074](0074-circuit-identifier-checked-once.md), [ADR 0086](0086-mdoc-witness-bounds-and-constant-time.md); issues #79, #150.
- [Chapter 9](../guide/09-mdoc.md), Section 6; [the Lean correspondence](../guide/lean-correspondence.md); [the trusted base register](../guide/trusted-base.md).
