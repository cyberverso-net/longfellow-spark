#  Thin wrapper over scripts/check.sh, the single definition of the
#  project's checks. `make check` runs everything in order and is the
#  definition of done for every commit and every pull request (ADR
#  0041, ADR 0044).

.PHONY: check check-reuse check-reuse-spark check-reuse-lean build prove prove-partition partitions-check test cli vectors values lint lean lean-source mdoc-cases

check:
	scripts/check.sh all

#  Every check but the proofs reused, for a commit whose proof inputs
#  equal those of a commit already proved (ADR 0088): check-reuse reuses
#  the SPARK and the Lean proofs, check-reuse-spark the SPARK proof only,
#  check-reuse-lean the Lean proofs only. scripts/remote-check.sh chooses
#  them, never a developer by hand.
check-reuse:
	scripts/check.sh reuse

check-reuse-spark:
	scripts/check.sh reuse-spark

check-reuse-lean:
	scripts/check.sh reuse-lean

build:
	scripts/check.sh build

prove:
	scripts/check.sh prove

#  One proof partition of the hosted runner (ADR 0033), for example
#  `make prove-partition PARTITION=p256`; names in scripts/prove-partitions.txt.
prove-partition:
	scripts/check.sh prove-partition $(PARTITION)

partitions-check:
	scripts/check.sh partitions-check

test:
	scripts/check.sh test

#  The command-line verifier on the upstream proofs (ADR 0046, 0048).
cli:
	scripts/check.sh cli

vectors:
	scripts/check.sh vectors

#  The values check of the SHA-256 clauses on the registered hash circuit
#  (#171), in make check.
values:
	scripts/check.sh values

#  The proof of age from every test document of upstream, alone (the
#  cli step of make check runs it too on the proving machine, not on
#  GitHub Actions; about seven minutes; ADR 0086).
#  Needs the release build.
mdoc-cases:
	scripts/mdoc-cases.sh

lint:
	scripts/check.sh lint

#  The Lean proofs of lean/ and the axiom check of the theorems the
#  SPARK proof cites (ADR 0091; chapter 10 Section 2).
lean:
	scripts/check.sh lean

#  At a release: the same proofs with Mathlib built from source, without
#  its cache (docs/process.md, "Releases"; register row L2).
lean-source:
	scripts/check.sh lean-source
