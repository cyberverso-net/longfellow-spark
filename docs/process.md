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

The gate of a pull request is the check `verify` (GitHub Actions: build, partitions, tests,
command line, vectors, lint) and the status `prove` (`make check` on the proving machine,
posted by `scripts/remote-check.sh`), both green. The ruleset on `main` requires both.

Two cases get `prove` without a proof run, because they cannot change what the proof checks:

- A change without code: nothing under `src/`, `tests/` or `scripts/`, and not `alire.toml`.
  `scripts/remote-check.sh --text-only` checks that only Markdown files, LICENSE and the
  configuration files under `.github/` (the issue forms, `CODEOWNERS`, `dependabot.yml`, the
  pull request template; never the workflows) changed since a proved commit, and posts the
  status naming that commit.
- A merge of `main` into the branch of an open pull request that brings no such change. The
  maintainer may post `prove` by hand; the description of the status says so and names the
  commit that was proved. The review of the pull request checks that `src/`, `tests/`,
  `scripts/` and `alire.toml` are the same as in that commit.

Every other change runs the proof.

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
contract and invariant runs; a contract violation is a test failure. `interop_kat` is the
exception: it runs on the release build of the command line, without assertions, so it tests the
verdict, not the contracts. The categories of test, each with its place in the repository:

| Category | What it checks | Where |
| --- | --- | --- |
| Specification vectors | A reference against the specification's own examples | `tests/vectors/`, generated by independent scripts |
| Upstream vectors | Intermediate states and outputs of upstream on the same inputs | `tests/vectors/upstream/` |
| Interoperability | Upstream's proofs accepted; upstream's proofs reproduced byte for byte from the same inputs and seeds | `interop_kat`, the command-line programs |
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
- the gate is green: `verify` and `prove`;
- every check in the units it touches is proved, with no justification and no `pragma Assume`;
- the measurements it owes are reported in the pull request and, where a record requires it,
  in that record;
- the tests and vectors it owes are in the repository;
- the documentation it owes is written: the chapter, the records (*Accepted* when the code that
  realises them is merged), the package headers, the trust model, the changelog;
- the pull request has been reviewed against the checklist below.

## Review checklist

- Does the code follow the specification section and the upstream file it cites, and is every
  divergence recorded?
- Is every new contract either proved or stated as tested or trusted, in the header and in the
  trust model?
- Is any secret-dependent branch or index in executable library code?
- Do the measurements satisfy the measurement rules, and is the comparison with upstream at equal
  scope?
- Are the chapter, the records, the headers and the changelog consistent with the code, names
  and numbers included?
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

## Releases

A release is tagged `vX.Y.Z` from `main` when its milestone's criterion is met, and published
as a GitHub release whose notes are the changelog section of that version. Until the interface
of the project is more than the pinned specification, the version numbers mark milestones, not
API compatibility, as [CHANGELOG.md](../CHANGELOG.md) says.
