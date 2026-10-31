# Contributing to longfellow-spark

Thank you for your interest. The project is small and proof-driven, so a change is accepted when its proofs, tests and documentation are in order, not only its code.

## Before you start

How work is planned, proved, measured and accepted is described in the [development process](docs/process.md). For anything larger than a small fix, open an issue first, with the Block, Task or Bug form, so that the approach can be agreed before you invest time.

## Building, proving and testing

The [README](README.md) explains how to build the library, run the proofs and the test harnesses, and verify a proof from the command line. The toolchain is pinned in `alire.toml`.

## Commits

- Every commit carries a `Signed-off-by` line certifying the [Developer Certificate of Origin 1.1](https://developercertificate.org/). Use `git commit -s`. Contributions are licensed under Apache-2.0, as the [README](README.md) states.
- Every commit is also signed with an SSH or GPG key that GitHub shows as *Verified*. The ruleset on `main` refuses unsigned commits.

## Branches and the gate

- Branches are named `<type>/<issue>-<short-slug>`, for example `block/57-packed-first-step`, `task/58-prover-memory-profile` or `bug/59-pinned-circuits-checks`.
- A pull request references its issue (`Closes #57`) and fills in the template.
- A pull request is merged when the check `verify` and the status `prove` are both green, as the [development process](docs/process.md) describes.

## Security

Do not report a vulnerability in a public issue. Use [private vulnerability reporting](https://github.com/cyberverso-net/longfellow-spark/security/advisories/new).
