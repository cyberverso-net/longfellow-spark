# Development process

How work on this project is planned, tracked and delivered. It applies to every contributor,
including the maintainer. The rules of proof and of documentation it refers to are in the
[verification approach](guide/verification-approach.md), the [trust model](guide/trust-model.md)
and the [records](adr/README.md).

## Planning structure

| Level | GitHub feature | Purpose |
| --- | --- | --- |
| Milestone | Milestone | A deliverable with a criterion of its own, fixed by a record: a phase, a performance or memory milestone, a documentation milestone. Its description states the criterion and the record. |
| Block | Issue of type *Story* | One increment that is designed, proved, measured, documented and reviewed on its own, usually one pull request |
| Task | Issue of type *Task* | Work with no proof obligation of its own: a measurement, a document, tooling, a release |
| Bug | Issue of type *Bug* | A defect in merged or released behaviour, or a wrong statement in the documentation |

The project board, *longfellow-spark roadmap*, shows every open item with its status, milestone
and labels. A block too large for one pull request is split into sub-issues. Every item has a
milestone, except the tasks of tooling and surveillance (the scripts of the proving machine, the
watch on the proof budget), which may have none. A dependency between issues is a GitHub
blocked-by relation on the issue that waits.

## Writing a block

Every block uses the *Block* issue form and states:

- its goal, in one or two sentences; when the reader is the one served, as in the guide, the
  goal may be written as "As an evaluator, I want … so that …";
- the context: the record that governs it, the guide chapter it belongs to, the sections of the
  specification and the files of upstream it follows;
- numbered acceptance criteria, each one checkable;
- the proof obligations: the units and contracts it adds or changes, with the assurance level
  of each (Gold, Silver, tested, trusted);
- the measurements it must report, with the criterion they are compared against;
- the tests and vectors it adds;
- the documentation it owes: the chapter, the records, the package headers, the trust model, the
  changelog;
- the decisions it needs from the maintainer before the work (a contract weakened, an assurance
  level changed, a prover setting changed);
- what is out of scope.

## Definition of Ready

A block may move to *Ready* when:

- its acceptance criteria are complete and checkable;
- the decisions it depends on are recorded, as *Proposed* at least, in a record;
- every issue it is blocked by is closed;
- any decision the maintainer must take before the work has been taken, and is stated in the
  issue.

A task or a bug moves to *Ready* when every issue it is blocked by is closed. An item that
waits on an open issue stays in *Backlog*, whatever else is ready.

## Workflow

| Status | Meaning |
| --- | --- |
| Backlog | Identified, not yet ready |
| Ready | Meets the Definition of Ready |
| In progress | Being implemented on a branch |
| In review | Pull request open |
| Done | Merged and meets the Definition of Done |

Branches are named `<type>/<issue>-<short-slug>`, for example `block/57-packed-first-step`
or `task/58-prover-memory-profile`. Pull requests reference their issue with `Closes #57`.

The gate of a pull request is three checks, all green: `verify` (GitHub Actions: build,
partitions, tests, command line, vectors, lint), `lean` (GitHub Actions: the step `lean`, the
Lean proofs of `lean/` built from Mathlib's cache, their axioms checked, the environment
replayed by `leanchecker`, the model's vectors compared) and the status `prove` (`make check`
on the proving machine, posted by `scripts/remote-check.sh`). The ruleset on `main` requires
the three. The
machine runs on its own clone, restored to the commit and checked clean at it before the
run starts; the copy of upstream for the cross-check is checked the same way at the pin. The
proving machine's `make check` also runs the cross-check of the mDoc proofs with upstream's
verifier, which needs cargo and a clone of upstream and is skipped, with a line saying so,
where they are absent (`scripts/cross-check-upstream.sh`, ADR 0087), the step `lean` (the
Lean proofs of `lean/` that the SPARK proof cites, built with Mathlib's cached files, their
axioms checked, the environment replayed by `leanchecker`; skipped, with a line saying so, in
the job `verify` of GitHub Actions and run by its job `lean`; chapter 10 Section 2.8),
and the proof of age
from every one of upstream's 38 test documents (`scripts/mdoc-cases.sh`), which is skipped,
with a line saying so, on GitHub Actions, whose job would exceed its 30 minutes.

The step lint (`make lint`), in both checks, holds these rules:

- the tests of the clean checkout the proving machine makes pass (`scripts/clean-checkout-test.sh`);
- every relative link of the Markdown under `docs/` and of the README resolves: the file
  exists, with the case as written, and an anchor names a heading of the target, as GitHub
  computes it (`scripts/check-links.py`). A wrong link in the body of an Accepted record stays,
  corrected in its Status line (ADR 0042); the script lists each such link with where it is
  corrected, and fails if the link is no longer there. Its tests run first
  (`scripts/check-links-test.py`): broken links it must report, valid ones it must accept;
- every unit named in a diagram of the guide or in a code map exists, every subprogram named
  is declared in its unit, and every unit of the proof partitions and of `cli/src` is in at
  least one map (`scripts/check-map.py`);
- the attribution of profiles by step that the performance page's matrices use gives each
  recorded call stack of its tests the expected step and circuit
  (`scripts/measure/attribute-steps-test.py`);
- the script that gives each chapter of the guide its table of verification conditions counts
  small runs right and refuses those whose units do not add up to the summary of GNATprove
  (`scripts/vc-count-test.py`, for `scripts/vc-count.py`);
- every body of `src/` outside SPARK, which the proof takes as given, has a row in the register
  of the trusted base whose column Item names it, qualified, the aspect or pragma found across
  line breaks (`scripts/check-spark-off.py`, after its tests
  `scripts/check-spark-off-test.py`);
- no em-dash in any tracked file but the files ported from upstream under `lean/Upstream/`,
  which keep upstream's bytes;
- none of the attribution and tooling words that `scripts/check.sh` lists, in any tracked file.

The proof is proved again only when its inputs changed (ADR 0088). `scripts/remote-check.sh`
lists the proof inputs of the commit, every file gnatprove reads: the project file and the
source directories it names, `alire.toml` (the toolchain pins), the partition list, every
configuration pragma file, and the gnatprove command lines of `scripts/check.sh` and the
Makefile, each by its git object hash; the digest of the list identifies the proof's inputs.
If an ancestor along any parent has the same digest and its status `prove` is success, the
machine runs every check but the proof (`make check-reuse`: build, partitions, tests, the
command line with the 38 test documents and the cross-check of the mDoc proofs, vectors, lint, about twenty minutes)
and `prove` is posted naming the proved commit and the digest. Otherwise the machine runs
`make check` and proves from scratch; so it does when the project file names a source
directory, a file or an attribute the list does not cover, declares its source directories
conditionally or more than once, or when a project file the list does not know appears. A merge of `main` into a branch that brings no change of the inputs
reuses the proof like any other commit. `scripts/remote-check.sh --digest [commit]` shows the
list, the digest and the proved ancestor without starting anything.

The proof from scratch stays the rule at three points, with `scripts/remote-check.sh --full`:
every release tag, every milestone close, and once a week on `main`, started on Monday at
03:00 by a scheduled job on the maintainer's machine (`scripts/weekly-proof.plist`, a
launchd agent that runs `--full origin/main`); the run is detached on the machine and its
status is posted on the head of `main` when it ends.

## The proving machine

The proving machine is a virtual machine on Google Cloud (c4-standard-24, 12 cores, one thread per core; ADR 0060, ADR 0062). It runs `make check` on demand through `scripts/remote-check.sh`:

```bash
scripts/remote-check.sh               # make check on the pushed commit, posts the status prove
scripts/remote-check.sh --collect     # picks up that run later, if the terminal was closed
scripts/remote-check.sh --digest      # the proof inputs of HEAD, their digest, the proved ancestor with the same
scripts/remote-check.sh --full        # the proof from scratch even when the inputs are unchanged
scripts/remote-check.sh --tree prove  # the working tree as it is, any target, posts nothing
scripts/remote-check.sh --tree-collect  # picks up a tree run later, if the terminal was closed
```

No run depends on the connection: the laptop may sleep. The machine keeps the result and shuts itself down; the script reads the result when it next reaches it, and for a pushed commit posts the status. A tree run started while another run holds the machine is refused. Two runs launched at the same moment are not kept apart, so one job at a time is a rule to follow.

## Proof rules

- No `pragma Assume`, anywhere, ever.
- A contract is not weakened, and the assurance level of a unit is not changed, without the
  maintainer's explicit agreement, recorded in the record that governs the unit. The issue
  carries the label `needs: approval` until it is given.
- The prover settings (`longfellow_spark.gpr`, package `Prove`) change only with a recorded
  rationale.
- An unproved check in existing code is reported with a diagnosis before it is touched. Unproved
  checks in the code a block adds are fixed by the block and listed, with their diagnosis and
  fix, in the pull request.
- Package headers state the proof status honestly: proved, tested, trusted, and cite the
  records and the guide sections they implement.

## Measurement rules

- Measurements are taken on the proving machine, in one session, three runs per commit, the
  median reported, with upstream's bench in the same session. Sessions are not compared with
  each other.
- A performance or memory change reports the figures before and after, and the proofs of the
  command line unchanged byte for byte where that is expected.

## Testing policy

The proofs cover every line of SPARK code for every input: no run-time error anywhere, and the
functional contracts of the Gold units. Tests therefore have a different job from the one they
have in a project without proofs. They do three things:

- they check that the ghost references the code is proved against read the specification
  correctly: known-answer vectors from the specification, and vectors of intermediate state
  extracted from upstream;
- they cover what is only tested or trusted: completeness (the verifier accepts the honest
  proof), interoperability with upstream, the units outside the proof perimeter (the command
  line, the randomness source), and the tested build when there is one;
- they stand in for the properties no proof expresses: soundness and zero knowledge are
  properties of the protocol and are addressed by fidelity to the specification, checked step by
  step; constant time is a coding discipline, checked on the generated code.

Every test harness under `tests/` compiles the library with assertions on, so every executable
contract and invariant runs; a contract violation is a test failure. `interop_kat` and
`first_step_bench --check` are the exceptions: they run on the release build of the command line,
without assertions, so they test the verdict, not the contracts. In the test build a harness
compares on small inputs, since executed contracts can cost far more than the code; large inputs
are compared in the release build.

A rule for the harnesses, learnt in the memory milestone: in the test build, compare on small inputs; measure in the release build. The harnesses of `tests/` run every executable contract and ghost function, and some cost far more than the code they check: a postcondition that names a recursive reference, such as `Eval_Bound_Quad`'s `EBQ_Ref`, runs a recursion over the terms of the layer at every call, and the loop invariants of a table builder cost the size of the table at every iteration. `circuit_kat` therefore compares the packed first step with the expanded one on the small layers only (at most 128 terms without the eq tables, Logv and Logw at most 10 with them), and `first_step_bench` in the release build (`cli/`, assertions off) compares and times the two on every layer of the mDoc circuits (chapter 3, Section 3.5). A comparison on a large input belongs in the release build, as a test (`first_step_bench --check` in the `cli` step of `make check`) or as a measurement.

The categories of test, each with its place in the repository:

| Category | What it checks | Where |
| --- | --- | --- |
| Specification vectors | A reference against the specification's own examples | `tests/vectors/`, generated by independent scripts |
| Upstream vectors | Intermediate states and outputs of upstream on the same inputs | `tests/vectors/upstream/` |
| Interoperability and byte identity | Upstream's proofs accepted, and this project's accepted by upstream (interoperability); upstream's proofs reproduced byte for byte from the same inputs and seeds (byte identity) | `interop_kat`, the command-line programs |
| Negative vectors | Every refusal status produced by at least one input | the harness of the unit that reports it |
| Generated-code checks | No conditional branch or data-dependent index in the listed constant-time functions | planned: a script under `scripts/`, run by the check `verify`; until then, a reading of the disassembly |

A unit that is only tested or trusted names, in its header, the tests and vectors that cover
it. The trust model says which units these are.

Planned, each in its milestone: test coverage per unit, a differential campaign against
upstream on random inputs, a mutation campaign, and a timing measurement of the field kernels
(the certification block); fuzzing of the parsers in the tested build (M3). The policy is
recorded in a record of its own.

## Definition of Done

A block is done when:

- every acceptance criterion is met;
- the gate is green: `verify`, `lean` and `prove`;
- every check in the units it touches is proved, with no justification and no `pragma Assume`;
- the measurements it owes are reported in the pull request and, where a record requires it,
  in that record;
- the tests and vectors it owes are in the repository;
- the documentation it owes is written: the chapter, the records (*Accepted* when the code that
  realises them is merged), the package headers, the trust model, the trusted base register
  for an item it adds or discharges, the changelog;
- a chapter it changes describes the design as it is: no chapter or record carries a dated
  "Update" paragraph. What changed, and when, goes in the records and the changelog; an
  Accepted record's body is not edited, its Status line carries a dated note (ADR 0042);
- the pull request has been reviewed against the checklist below.

## Review checklist

- Does the code follow the specification section and the upstream file it cites, and is every
  divergence recorded?
- Is every new contract either proved or stated as tested or trusted, in the header and in the
  trust model? Does every new trusted item have its row in the trusted base register?
- Is any secret-dependent branch or index in executable library code?
- Do the measurements satisfy the measurement rules, and is the comparison with upstream at equal
  scope?
- Are the chapter, the records, the headers and the changelog consistent with the code, names
  and numbers included? Does the chapter describe the current design, with no dated "Update"
  paragraph?
- Is the issue's "out of scope" respected, with nothing added on the way?

## Labels

| Label | Use |
| --- | --- |
| `area: fields`, `area: sumcheck`, `area: ligero`, `area: verifier`, `area: prover`, `area: circuits`, `area: mdoc`, `area: docs`, `area: measurements`, `area: ci` | The part of the project concerned |
| `assurance: gold`, `assurance: silver`, `assurance: tested`, `assurance: trusted` | What the item delivers or changes, read with the trust model |
| `needs: adr`, `needs: discussion`, `needs: approval` | What must happen before the work can proceed |
| `blocked` | Waiting on something that is not an issue (an upstream change, an external decision), named in the issue; a wait on an issue is a blocked-by relation, not a label |
| `priority: high`, `priority: low` | Deviation from normal priority |

Issue type, milestone and status are not duplicated as labels. Dependabot labels its pull
requests `area: ci` (`.github/dependabot.yml`); they need no issue.

## The review at the close of a milestone

Before the closing record of a milestone, the whole repository is reviewed:

- the documents against each other and against the code;
- the alignment with upstream and with the pinned specification;
- the integrity of the proofs;
- the clarity of the guide for its reader, and the evidence for certification;
- the commands the guide gives for reproducing the evidence, run as written on a clean clone, on the proving machine, with their outputs compared with the text.

The author triages the findings: each is fixed in a pull request of its own before the closing record, recorded as an issue, or answered with the reason.

## Releases

A release is tagged `vX.Y.Z` from `main` when its milestone's criterion is met, and published
as a GitHub release whose notes are the changelog section of that version. Before the tag,
the version in `alire.toml`, which the library is built with, is set to the release's
number in the same pull request as the changelog section. On the release commit, beside the
proof from scratch (`scripts/remote-check.sh --full`), the Lean proofs are built once with
Mathlib from source, without its cache (`scripts/remote-check.sh --tree lean-source` on a
clean tree of that commit; register row L2); the release's pull request reports its result.
Until the interface
of the project is more than the pinned specification, the version numbers mark milestones, not
API compatibility, as [CHANGELOG.md](../CHANGELOG.md) says.
