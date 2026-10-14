#  Thin wrapper over scripts/check.sh, the single definition of the
#  project's checks. `make check` runs everything in order; `make hooks`
#  installs the pre-push hook that runs the proof before every push.

.PHONY: check build prove prove-partition partitions-check test vectors lint hooks

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

vectors:
	scripts/check.sh vectors

lint:
	scripts/check.sh lint

hooks:
	git config core.hooksPath .githooks
