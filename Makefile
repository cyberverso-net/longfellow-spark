#  Thin wrapper over scripts/check.sh, the single definition of the
#  project's checks. `make check` runs everything in order; `make hooks`
#  installs the pre-push hook that runs the proof before every push.

.PHONY: check build prove test vectors lint hooks

check:
	scripts/check.sh all

build:
	scripts/check.sh build

prove:
	scripts/check.sh prove

test:
	scripts/check.sh test

vectors:
	scripts/check.sh vectors

lint:
	scripts/check.sh lint

hooks:
	git config core.hooksPath .githooks
