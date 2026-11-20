# 0092 The guide for the evaluator closed

## Status

Accepted (2026-11-19, at the merge of pull request #204; proposed 2026-11-19, close of the guide milestone).

## Date

2026-11-19

## Context

[ADR 0081](0081-audience-certification-evaluators.md) set the audience of the repository: evaluators in a certification laboratory, experts in certification and not, as a rule, in cryptography or in SPARK. It gave the guide a milestone of its own, after the mDoc layer and before the certification block ([ADR 0082](0082-order-after-the-memory-milestone.md)): a primer on the cryptography, a primer on the Ada/SPARK constructs, a glossary, a reading path for an evaluator, and every chapter checked against the audience. [ADR 0091](0091-certified-circuits-milestone.md) placed the milestone Certified circuits after it.

The milestone ran from 12 to 19 November:

- the primer, Part A on the cryptography and Part B on Ada and SPARK, with a worked evaluation of one claim (#175, #182);
- the glossary and the two reading paths, a short one for a first assessment and a full one for a certification (#176, #184);
- the diagrams of the algorithm, the system map and the performance matrix by step (#119, #187), with the same matrices at upstream's 1c06629 (#179, #188);
- the check of the relative links of the documentation in the gate (#183, #185);
- the test harnesses printing their counts by section (#192, #193);
- chapters 1 to 6 and the trust model revised against the code (#177, #194), then chapters 7 to 9 and the other pages (#178, #196);
- every package header stating its proof status in the glossary's terms (#190, #199).

The review of the whole repository (#180) read every page against the code and against each other, recomputed the counts the chapters give, had the short path read cold against ten questions written beforehand, and read again after the fixes on the two it had answered in part, and ran the commands of primer B9 and B10, as written, on two clean clones on the proving machine. Its findings were fixed in four pull requests: the claims of assurance (#200), the explanations of the algorithms (#201), the commands of the evidence (#202) and the reading path (#203). The last fixes, the headers of `Sha256` and `Merkle`, are in the pull request of this record.

## Decision

**The guide milestone is closed. The criterion of ADR 0081 is met.**

- **The primer**: `docs/guide/00-primer-cryptography.md` and `docs/guide/00-primer-spark.md`, from first principles, Part A at 12,396 words of text (the limit is 13,000).
- **The glossary**: `docs/guide/glossary.md`, 196 entries, one name per thing.
- **The reading paths**: the guide's README. The short path is about 31,500 words, 30,000 without the optional system map. The author read it as its reader would in about 3 hours 20 minutes, knowing the material; the cold reading of the review estimated five and a half to six and a half hours for a reader new to it. The README states both, in place of the estimate it gave until now.
- **Every chapter checked against the audience**: the revisions of #177 and #178, by the rules of #177, and the review of #180.
- **The evidence reproduced as written**: the commands of B9 and B10 on clean clones (`make check` in 183 minutes on the proving machine), and the counts of the chapters recomputed: 39,245 checks over the 13 partitions, none justified, none unproved, no `pragma Assume`.

[ADR 0091](0091-certified-circuits-milestone.md) is Accepted by the author at this close, as #180 asked before the milestone Certified circuits opens.

### What the milestone changed in the statements of assurance

The milestone added no proof and changed no contract; the one contract change of the release, #165, belongs to the certification block (Verification impact). What it changed is what the documents declare, where the review of the code found them silent or saying more than the contracts:

- **The register's new rows.** V8 to V12: `Subfield_Coords` inverts `Inject`, `Bindeq` agrees with `Eq`, the Lagrange basis interpolates, the three Lagrange denominator inverses are inverses, the Ligero verifier's Lagrange tables interpolate; each was tested and stated in a chapter, without a row. V13: the prover's tableau and its Ligero proof as a whole. R13: the bound of 65,000 bytes on the session transcript. R14: the layouts of the two private witnesses of the mDoc circuits.
- **A third exception to the rule that the contract parts kept in every build are on public data,** found by an inventory of every call: the private inputs of the witness-file path of `longfellow_prove_mdoc`, which `P256_Field.From_Bytes` decodes.
- **The nine decisions on admission declared by their status,** from an inventory of the witness builder: the prover's two checks and the builder's seven refusals, with what the time of each reveals. And the inspection of the machine code of the field products, which have no branch on a secret (ADR 0051, its notes).
- **The conditions for certifying the circuit** (chapter 9 Section 6): e2 not 0 modulo n in place of e2 not zero, since e2 = n gives the same point at infinity; the rows added for e2 below p, x(R) below n and the device key's coordinates below n; and the scale of the issuer's digest below n, negligible for one credential and not for a population, about one in 2^32.
- **The statements corrected because they said more than the contracts:** chapter 5 Section 4.2, which said that the proofs give a verifier computing exactly upstream's checks; the header of `Ligero_Verifier`, which said Exhausted exactly when the generator ran out where the contract says only when; and the header of `Merkle`, which exempted the unit from the discipline as handling public data only, though the prover builds its tree over the digests of its secret columns.
- **The levels renamed to the glossary's definitions** in every package header, with no change of what is proved.

What the milestone leaves open is recorded as issues:

- the refusals of the witness builder gathered into one mask, the dates included (#195), and no executable conditional on a secret around ghost code in the field products (#198);
- an automatic check of the generated code for constant time, in the certification block (#70). Until then, outside the witness builder's units and the field products, whose code was inspected, the absence of branches on secrets rests on the headers and on reading;
- the two gaps of `scripts/check-map.py` (#186) and a test of the attribution of samples to the steps (#189), in the backlog;
- a vector for the prover's status `Config_Invalid` (#197) and the check of the Solinas table removed from `gen_p256_vectors.py` (#191);
- the Lean correspondence reread at the merge of upstream's ECDSA fix (#122);
- the reading on Longfellow v2 and its version 8 circuits, in a milestone of its own (#181).

## Alternatives considered

- **ADR 0081 amended with the close.** Rejected, as for ADR 0084 and ADR 0090: ADR 0081 is Accepted, so its body is immutable, and a closing record keeps the result and the decision in one place. ADR 0081 points here in its Status line.

## Consequences

- Release 0.6.0: the first version an evaluator can read from start to finish, with the review of the whole repository as its reference point. The first release with the full evidence bundle stays the one after the certification block (ADR 0082).
- The order after the close is the one ADR 0082 and ADR 0091 give: the milestone Certified circuits next, then the certification block. This record changes nothing in it.
- The guide's README states the measured reading time of the short path.
- ADR 0081 and ADR 0091 carry notes in their Status lines.

## Verification impact

- None. The milestone changed no contract, and under `src/` and `cli/src/` nothing but comments: the package headers, those of `Sha256` and `Merkle` included. The test harnesses (their counts by section) and the scripts (the check of the links) changed, and the gate runs them. The gate of the release commit proves from scratch.
- The release also carries #165, of the certification block, merged on 12 November: three refusals of the witness builder (`Validity_Form_Unsupported`, `Device_Key_Form_Unsupported`, `Random_Form_Unsupported`), with the postconditions of `Mdoc_Prover.Prove_Mdoc` extended to them, proved at its gate.
- The gate of 40a502a, proved from scratch in 175 minutes: 39,245 checks, all proved, none justified, none unproved; most steps 463,202. The release commit, which writes these counts, has the same proof inputs (ADR 0088), and its gate reuses that proof.
- The list of the fragilities (register Section 8) recomputed from that gate, as the rules of #92 ask at the close of a milestone: the same seven checks, with the same steps.

## References

- [ADR 0081](0081-audience-certification-evaluators.md), [ADR 0082](0082-order-after-the-memory-milestone.md), [ADR 0084](0084-memory-milestone-closed.md), [ADR 0090](0090-mdoc-milestone-closed-phase-d-complete.md), [ADR 0091](0091-certified-circuits-milestone.md).
- [The guide](../guide/README.md), [the primer](../guide/00-primer-cryptography.md), [the glossary](../guide/glossary.md), [the trust model](../guide/trust-model.md), [the trusted base register](../guide/trusted-base.md).
- `docs/process.md`, "The review at the close of a milestone".
