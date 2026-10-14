#!/usr/bin/env bash
#  check.sh: the single definition of the project's checks, used locally
#  (make check), by the pre-push hook (prove) and in continuous
#  integration (build, test, vectors, lint on every push; prove weekly
#  and on demand). Run from the repository root. Every step prints a header and the script stops at the first
#  failure with a non-zero exit status.
#
#  Subcommands: build, prove, prove-partition <name>, partitions-check,
#  test, vectors, lint, all. The proof partitions of the hosted runner
#  are listed in scripts/prove-partitions.txt (ADR 0033).

set -euo pipefail

usage() {
   echo "usage: scripts/check.sh {build|prove|prove-partition <name>|" \
        "partitions-check|test|vectors|lint|all}" >&2
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

partitions=scripts/prove-partitions.txt

#  The Why3 session under obj/ returns stale "unproved" results for
#  unchanged checks without re-running them (false failures three times
#  in stage 4); every proof starts from a clean session.
clean_session() {
   alr -n exec -- gnatprove -P longfellow_spark.gpr --clean >/dev/null
}

prove_summary() {
   header "prove: summary (obj/development/gnatprove/gnatprove.out)"
   sed -n '/^Summary of SPARK/,/^max steps/p' obj/development/gnatprove/gnatprove.out
}

do_prove() {
   #  The prover configuration (provers, step budget, safety timeout) lives
   #  in package Prove of longfellow_spark.gpr, so that a plain gnatprove -P
   #  run and this check prove the same thing.
   header "prove: gnatprove -P longfellow_spark.gpr -j0 --checks-as-errors=on"
   clean_session
   alr -n exec -- gnatprove -P longfellow_spark.gpr -j0 --checks-as-errors=on
   prove_summary
}

#  The units of one partition, as the files gnatprove -u takes: the body
#  when the unit has one, the spec otherwise (an instance, say).
partition_files() {
   local name="$1" line pname unit found=false
   while read -r line; do
      case "$line" in ''|'#'*) continue ;; esac
      # shellcheck disable=SC2086
      set -- $line
      pname="$1"; shift
      if [ "$pname" = "$name" ]; then
         found=true
         for unit in "$@"; do
            if [ -f "src/$unit.adb" ]; then
               echo "$unit.adb"
            elif [ -f "src/$unit.ads" ]; then
               echo "$unit.ads"
            else
               echo "check.sh: partition $name names $unit, not under src/" >&2
               exit 2
            fi
         done
      fi
   done < "$partitions"
   if [ "$found" = false ]; then
      echo "check.sh: no partition named $name in $partitions" >&2
      exit 2
   fi
}

do_prove_partition() {
   local name="${1:-}" files
   if [ -z "$name" ]; then
      usage
   fi
   files=$(partition_files "$name" | tr '\n' ' ')
   header "prove-partition $name: gnatprove -u $files"
   clean_session
   # shellcheck disable=SC2086
   alr -n exec -- gnatprove -P longfellow_spark.gpr -j0 --checks-as-errors=on \
      -u $files
   prove_summary
   header "prove-partition $name: units analysed"
   grep '^Analyzed\|^in unit' obj/development/gnatprove/gnatprove.out
}

#  The partitions cover exactly the non-generic units under src/, each
#  once; a new unit without a partition would otherwise be proved
#  locally and never on the hosted runner.
do_partitions_check() {
   header "partitions-check: $partitions against src/"
   local expected listed status=0
   expected=$(for f in src/*.ads; do
                 if ! grep -q '^generic' "$f"; then
                    basename "$f" .ads
                 fi
              done | sort)
   listed=$(grep -v '^[[:space:]]*#' "$partitions" | grep -v '^[[:space:]]*$' \
            | cut -d' ' -f2- | tr ' ' '\n' | grep -v '^$' | sort)
   if [ -n "$(echo "$listed" | uniq -d)" ]; then
      echo "partitions-check: listed more than once:" >&2
      echo "$listed" | uniq -d >&2
      status=1
   fi
   if ! diff <(echo "$expected") <(echo "$listed" | uniq); then
      echo "partitions-check: the partitions (>) differ from src/ (<);" \
           "generic units are excluded, everything else is required" >&2
      status=1
   fi
   #  The matrix of prove.yml names the same partitions, in the same
   #  order; the workflow cannot read the file, so this keeps them equal.
   local names matrix
   names=$(grep -v '^[[:space:]]*#' "$partitions" | grep -v '^[[:space:]]*$' \
           | cut -d' ' -f1 | tr '\n' ' ' | sed 's/ $//')
   matrix=$(sed -n 's/^ *partition: \[\(.*\)\]$/\1/p' .github/workflows/prove.yml \
            | tr -d ',' | sed 's/  */ /g')
   if [ "$names" != "$matrix" ]; then
      echo "partitions-check: prove.yml matrix [$matrix] differs from" \
           "the partitions [$names]" >&2
      status=1
   fi
   if [ "$status" -ne 0 ]; then
      exit "$status"
   fi
   echo "partitions-check: $(echo "$listed" | wc -l | tr -d ' ') units in" \
        "$(grep -cv '^[[:space:]]*#\|^[[:space:]]*$' "$partitions") partitions," \
        "complete and matching the prove.yml matrix"
}

do_test() {
   header "test: build the harnesses (assertions on)"
   alr -n exec -- gprbuild -P tests/longfellow_spark_tests.gpr -p
   header "test: gf2_128_kat"
   tests/bin/gf2_128_kat
   header "test: p256_kat"
   tests/bin/p256_kat
   header "test: sumcheck_kat"
   tests/bin/sumcheck_kat
   header "test: transcript_kat"
   tests/bin/transcript_kat
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
   python3 -I tests/vectors/gen_sumcheck_vectors.py "$scratch"
   python3 -I tests/vectors/gen_transcript_vectors.py "$scratch"
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
   build)            do_build ;;
   prove)            do_prove ;;
   prove-partition)  do_prove_partition "${2:-}" ;;
   partitions-check) do_partitions_check ;;
   test)             do_test ;;
   vectors)          do_vectors ;;
   lint)             do_lint ;;
   all)
      do_build
      do_partitions_check
      do_prove
      do_test
      do_vectors
      do_lint
      header "all checks passed"
      ;;
   *) usage ;;
esac
