#  Thin wrapper over scripts/check.sh, the single definition of the
#  project's checks. `make check` runs everything in order and is the
#  definition of done for every commit; `make check-full` adds the slow
#  harness cases (ADR 0041), before a pull request.

.PHONY: check check-full build prove prove-partition partitions-check test test-slow vectors lint

check:
	scripts/check.sh all

check-full:
	scripts/check.sh full

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

#  The harnesses with the slow cases (ADR 0041).
test-slow:
	scripts/check.sh test-slow

vectors:
	scripts/check.sh vectors

lint:
	scripts/check.sh lint
