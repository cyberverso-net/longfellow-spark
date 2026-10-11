#!/usr/bin/env bash
#  check.sh: the single definition of the project's checks, used locally
#  (make check) and in continuous integration. Run from the repository
#  root. Every step prints a header and the script stops at the first
#  failure with a non-zero exit status.
#
#  Subcommands: build, prove, test, vectors, lint, all.

set -euo pipefail

usage() {
   echo "usage: scripts/check.sh {build|prove|test|vectors|lint|all}" >&2
   exit 2
}

header() {
   printf '\n=== %s ===\n' "$1"
}

#  Resolve the repository root from the script's own location and insist
#  on running there, so that relative paths (tests/bin, obj/...) hold.
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd -P)"
if [ "$(pwd -P)" != "$root" ]; then
   echo "check.sh: run from the repository root ($root)" >&2
   exit 2
fi

do_build() {
   header "build: alr build"
   alr -n build
}

do_prove() {
   #  The prover configuration (provers, step budget, no timeout) lives in
   #  package Prove of longfellow_spark.gpr, so that a plain gnatprove -P
   #  run and this gate prove the same thing.
   header "prove: gnatprove -P longfellow_spark.gpr -j0 --checks-as-errors=on"
   alr -n exec -- gnatprove -P longfellow_spark.gpr -j0 --checks-as-errors=on
   header "prove: summary (obj/development/gnatprove/gnatprove.out)"
   sed -n '/^Summary of SPARK/,/^max steps/p' obj/development/gnatprove/gnatprove.out
}

do_test() {
   header "test: build the harnesses (assertions on)"
   alr -n exec -- gprbuild -P tests/longfellow_spark_tests.gpr -p
   header "test: gf2_128_kat"
   tests/bin/gf2_128_kat
   header "test: p256_kat"
   tests/bin/p256_kat
}

do_vectors() {
   header "vectors: regenerate into a scratch directory and compare"
   #  The generators take an output directory as their first argument;
   #  writing there rather than in tests/vectors keeps the check from
   #  touching the working tree. Only the generated files are compared,
   #  so the generators themselves (and any new file a generator starts
   #  producing) are not masked by the directory listing.
   #  Not local: the EXIT trap runs after the function has returned.
   scratch="$(mktemp -d)"
   trap 'rm -rf "$scratch"' EXIT
   python3 -I tests/vectors/gen_gf2_128_vectors.py "$scratch"
   python3 -I tests/vectors/gen_p256_vectors.py "$scratch"
   local name status=0
   for name in "$scratch"/*.txt; do
      name="$(basename "$name")"
      if ! diff -u "tests/vectors/$name" "$scratch/$name"; then
         echo "vectors: $name differs from the generator's output" >&2
         status=1
      fi
   done
   if [ "$status" -ne 0 ]; then
      exit "$status"
   fi
   echo "vectors: tests/vectors matches the generators"
}

do_lint() {
   header "lint: forbidden content over tracked files"
   #  git grep searches tracked files only, in one process, and exits 0
   #  exactly when something matched. This script is excluded from the
   #  sweep because it has to spell the patterns out.
   local status=0
   local -a scope=(-- . ':!scripts/check.sh')
   #  U+2014 (em-dash) anywhere.
   if git grep -n -I -e $'\xe2\x80\x94' "${scope[@]}"; then
      echo "lint: em-dash found" >&2
      status=1
   fi
   #  Attribution and tooling words, case-insensitive.
   local words='claude|anthropic|co-authored-by|generated with'
   if git grep -n -I -i -E -e "$words" "${scope[@]}"; then
      echo "lint: forbidden word found" >&2
      status=1
   fi
   #  The token AI only as a standalone word surrounded by blanks.
   if git grep -n -I -e ' AI ' "${scope[@]}"; then
      echo "lint: standalone token AI found" >&2
      status=1
   fi
   if [ "$status" -ne 0 ]; then
      exit "$status"
   fi
   echo "lint: clean"
}

case "${1:-}" in
   build)   do_build ;;
   prove)   do_prove ;;
   test)    do_test ;;
   vectors) do_vectors ;;
   lint)    do_lint ;;
   all)
      do_build
      do_prove
      do_test
      do_vectors
      do_lint
      header "all checks passed"
      ;;
   *) usage ;;
esac
