# longfellow-spark

A formally verified reimplementation, in Ada/SPARK, of [Longfellow ZK](https://github.com/longfellow-zk/longfellow-zk), a zero-knowledge proof system for identity credentials. Longfellow ZK was created at Google, which donated it in September 2026 to the [Post-Quantum Cryptography Alliance](https://pqca.org/), a foundation under Linux Foundation Europe.

It follows **IETF draft-irtf-cfrg-longfellow-00 (22 October 2026)**, the CFRG version of draft-google-cfrg-libzk-03, with the same technical text (ADR 0079). Changes in later drafts are handled as explicit migrations (ADR 0002).

The project is built in phases, each released when complete:

| Phase | What it adds | Release | Checks proved |
|-------|--------------|---------|---------------|
| A | A complete verifier, from the proof string to a verdict, in five stages: GF(2^128), the P-256 base field, the sumcheck algebra, the Fiat-Shamir transcript, Ligero | 0.1.0 | 10738 |
| B | A loader for the circuits the upstream compiler produces, and the upstream proofs accepted from their files | 0.2.0 | 11967 |
| C | The prover, which reproduces the two upstream example proofs byte for byte | 0.3.0 | 16671 |
| D | The production mDoc circuits at full scale: performance and memory (0.4.0), then the mDoc layer and the proof of age (0.5.0) | in progress | |

In Phase D, milestone M2 closed at a round trip of 8.13 s for the two mDoc proofs and their verifications, with every contract proved; [the performance page](docs/guide/performance.md) gives the steps and the comparison with upstream.

[CHANGELOG.md](CHANGELOG.md) describes each release.

## What you can rely on

Every claim is either proved, tested or trusted. The full list is in [the trust model](docs/guide/trust-model.md). In short:

- **No run-time errors.** GNATprove shows that no SPARK code can overflow, index out of range or read uninitialised data, for any input that meets the preconditions of the units. Proofs and circuits come from untrusted parties, so this matters on its own. A failed allocation, code outside SPARK and the probabilistic termination of the samplers stay outside, as the trust model lists.
- **Correct arithmetic.** Both fields are proved equal to simple reference implementations. Test vectors from outside the project confirm that the references follow the specification.
- **Faithful building blocks.** The sumcheck, Merkle and Ligero pieces and the proof reader and writers are proved against transcriptions of the specification's formulas. The circuit loader is proved to return only well-formed circuits; that it decodes the terms the file encodes is tested against upstream.
- **Interoperability.** The verifier accepts the proofs the upstream prover makes. The prover reproduces upstream's proofs byte for byte. Both are tested.
- **Not proved.** Soundness and zero knowledge are properties of the protocol, not of the code. The implementation follows the specification step by step instead. Constant time is a coding discipline, valid only in builds without assertions.
- **Trusted.** The compiler, GNATprove and its solvers, the specification itself, the operating system's random generator, and the upstream circuit files as to what they compute.

No check is justified away and no `pragma Assume` is used.

## Documentation

The repository is meant to be read. [docs/guide/](docs/guide/README.md) has one chapter per stage. Each chapter covers the mathematics, the algorithm and the SPARK code, explained for a reader new to SPARK, then says what is proved, tested and trusted. Start with [the verification approach](docs/guide/verification-approach.md).

Every non-trivial decision has a record in [docs/adr/](docs/adr/README.md).

How work is planned, proved and accepted is in [the development process](docs/process.md); how to contribute is in [CONTRIBUTING.md](CONTRIBUTING.md).

## Building and proving

You need [Alire](https://alire.ada.dev). The compiler, the builder and the prover are dependencies of the crate, at the versions pinned in `alire.toml`, so the first `alr build` fetches them. Python 3 is needed only to regenerate the test vectors.

```bash
alr build                                    # the library
alr exec -- gnatprove -P longfellow_spark.gpr
make check                                   # everything, in order
```

The repository is `longfellow-spark`. The Alire crate and the project file are `longfellow_spark`, because those names cannot contain hyphens.

The prover settings are in `longfellow_spark.gpr` (ADR 0020): CVC5, Z3 and Alt-Ergo with a budget of 600000 steps per check. The budget makes a proof reproducible across machines. A timeout of 120 seconds guards against runs that never end.

`make check` runs every check of the project, in order:

1. the build and the check that the proof partitions cover the project;
2. the full proof, with any unproved check treated as an error;
3. the nine test harnesses;
4. the release build: the interop harness, the command-line verifier on the upstream proofs, and the command-line prover reproducing them;
5. the vector generators, compared with the committed files;
6. a lint of the tracked files.

`scripts/check.sh` defines these steps. `make build`, `make prove`, `make test`, `make cli`, `make vectors` and `make lint` run them one at a time. The full proof takes about an hour on a laptop.

The project's proving machine, a virtual machine on Google Cloud (c4-standard-24, 12 cores, one thread per core), runs the same check on demand (ADR 0060, 0062):

```bash
scripts/remote-check.sh               # make check on the pushed commit, posts the status prove
scripts/remote-check.sh --collect     # picks up that run later, if the terminal was closed
scripts/remote-check.sh --text-only   # only text since the last proved commit: posts prove without the proof
scripts/remote-check.sh --tree prove  # the working tree as it is, any target, posts nothing
scripts/remote-check.sh --tree-collect  # picks up a tree run later, if the terminal was closed
```

Neither run depends on the connection: the laptop may sleep. The machine keeps the result and shuts itself down; the script reads the result when it next reaches it, and for a pushed commit posts the status. A tree run started while another run holds the machine is refused. Two runs launched at the same moment are not yet kept apart, so running one job at a time is still a rule to follow.

## Testing

The harnesses in `tests/` compile the library with assertions on, so every executable contract and invariant runs. A contract violation is a test failure. The field contracts are the exception: they are proved but never compiled, so the fields are tested through their vectors (ADR 0044).

This is not the constant-time build. Never measure or ship binaries built from `tests/`.

```bash
alr exec -- gprbuild -P tests/longfellow_spark_tests.gpr -p
make test        # the nine harnesses, concurrently, in about a minute
```

Each harness reads its vector files from `tests/vectors/` by default, prints pass and fail counts, and fails if any case fails or none ran. The [trust model](docs/guide/trust-model.md) maps each file to its generator and harness.

The release project in `cli/` builds the library as it is meant to run: no assertions, optimised. It holds the command-line verifier and prover, the interop harness, and `first_step_bench`, which measures the first step of a layer from the packed circuit against the expanded path (chapter 3, Section 3.5):

```bash
alr exec -- gprbuild -P cli/longfellow_verify.gpr -p -s
cli/bin/interop_kat
cli/bin/first_step_bench --field gf2_128 --circuit tests/vectors/upstream/circuits/sha256_circuit.lfc2
```

## Verifying a proof

`cli/bin/longfellow_verify` checks a proof file against an LFC2 circuit file (chapter 6). It needs the transcript label and the Ligero configuration the proof was made with. Public inputs are given as big-endian hex: 32 digits on GF(2^128), 64 on P-256.

It prints a status and exits with 0 when the proof is accepted, 1 when it is refused or the circuit is rejected, and 2 on a usage or file error. The two upstream examples:

```bash
alr exec -- gprbuild -P cli/longfellow_verify.gpr -p -s
cli/bin/longfellow_verify --field gf2_128 \
   --circuit tests/vectors/upstream/circuits/sha256_circuit.lfc2 \
   --proof tests/vectors/upstream/circuits/sha256_proof.bin \
   --label sha256_spec_test --rate-inv 3 --nreq 16 --ncol 256
cli/bin/longfellow_verify --field p256 \
   --circuit tests/vectors/upstream/circuits/ecdsa2_circuit.lfc2 \
   --proof tests/vectors/upstream/circuits/ecdsa2_proof.bin \
   --label ecdsa2_spec_test --rate-inv 4 --nreq 16 --ncol 256
```

Both print `ok` in about a second. The verifier proves the shape of a circuit file when it loads it and checks its identifier. It still trusts the file as to what the circuit computes (ADR 0011).

The mDoc circuits under `tests/vectors/upstream/mdoc/` are in a fixed list, `cli/src/pinned_circuits.adb`, with the digest of each file and its identifier, checked once. The verifier and the prover load a listed file without recomputing the identifier, which takes seconds on these circuits. `--check-circuit-id` recomputes it all the same (ADR 0074). Circuits that are malformed, or larger than this project's bounds, are refused with `not_well_formed` or `bound_exceeded`.

## Proving

`cli/bin/longfellow_prove` makes a proof from an LFC2 circuit file and an inputs file (chapter 7). The inputs file uses the format of the upstream test data: a JSON array of decimal strings, with the public inputs first.

It exits with 0 when the proof is written, 1 on a prover or circuit status, and 2 on a usage or file error. The prover statuses are `input_length`, `not_satisfied`, `not_in_subfield`, `config_invalid` and `exhausted`.

By default the randomness comes from the operating system. `--seed N` switches to the generator of the upstream test instead. That makes the proof reproducible, and also predictable, so it is for testing only. With the upstream seeds, the two upstream proofs come out byte for byte:

```bash
cli/bin/longfellow_prove --field gf2_128 \
   --circuit tests/vectors/upstream/circuits/sha256_circuit.lfc2 \
   --inputs tests/vectors/upstream/circuits/sha256_inputs.json \
   --label sha256_spec_test --rate-inv 3 --nreq 16 --ncol 256 \
   --seed 12345 --out /tmp/sha256_proof.bin
cmp /tmp/sha256_proof.bin tests/vectors/upstream/circuits/sha256_proof.bin
cli/bin/longfellow_prove --field p256 \
   --circuit tests/vectors/upstream/circuits/ecdsa2_circuit.lfc2 \
   --inputs tests/vectors/upstream/circuits/ecdsa2_inputs.json \
   --label ecdsa2_spec_test --rate-inv 4 --nreq 16 --ncol 256 \
   --seed 123456789 --out /tmp/ecdsa2_proof.bin
cmp /tmp/ecdsa2_proof.bin tests/vectors/upstream/circuits/ecdsa2_proof.bin
```

At Phase C each took about six seconds on the author's laptop; Phase D has made the prover much faster since ([the performance page](docs/guide/performance.md)). Without `--seed` the proof changes at every run, and `longfellow_verify` accepts it. To check a proof with the upstream verifier, see `tests/vectors/upstream/verify_proof_file.rs`.

## Continuous integration

[![verify](https://github.com/cyberverso-net/longfellow-spark/actions/workflows/verify.yml/badge.svg)](https://github.com/cyberverso-net/longfellow-spark/actions/workflows/verify.yml)

Two checks guard `main`, both with the toolchain pinned in `alire.toml`: `gnat_native 16.1.0`, `gprbuild 26.0.1` and `gnatprove 16.1.0`. The workflow reads the versions from that file, and its actions are pinned by commit hash (Dependabot proposes the updates).

To reproduce the environment on another machine:

1. Install Alire.
2. Clone the repository and run `alr build`: Alire fetches the pinned compiler, builder and prover.
3. Check the versions with `alr exec -- gnat --version` and `alr exec -- gnatprove --version`.

- **`verify`** is a workflow. It runs on every push and pull request, on a hosted Ubuntu runner, and covers everything in `make check` except the proof.
- **`prove`** is a commit status. `scripts/remote-check.sh` posts it after running `make check` on the proving machine for that exact commit. Branches that change only text, or the configuration files under `.github/` other than the workflows, get it with `--text-only`, without running the proof; [the development process](docs/process.md) says when the maintainer may post it by hand.

Work happens on a branch per stage or block, and reaches `main` through a pull request once both checks are green (ADR 0062). A red check is fixed with a new commit on the branch. Before a release, or after a toolchain change, the check is run on `main` as well.

Together the two checks certify what `make check` certifies. Neither says anything about constant time, or about fidelity to the specification beyond the vectors.

## About this project

longfellow-spark is a personal project of its author, Paolo De Rosa. It is not affiliated with the author's employer, nor with Google or the Post-Quantum Cryptography Alliance. The views and opinions expressed in it are the author's own and do not represent those of the author's employer.

## Licence

Apache-2.0.
