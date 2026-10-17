#  Thin wrapper over scripts/check.sh, the single definition of the
#  project's checks. `make check` runs everything in order and is the
#  definition of done for every commit and every pull request (ADR
#  0041, ADR 0044).

.PHONY: check build prove prove-partition partitions-check test cli vectors lint

check:
	scripts/check.sh all

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

lint:
	scripts/check.sh lint
