#!/usr/bin/env bash
#  check.sh: the single definition of the project's checks, used locally
#  (make check before every commit and before every pull request, ADR
#  0041, ADR 0044) and in continuous integration (build, test, vectors,
#  lint on every push; prove on pull requests, weekly and on demand).
#  Run from the repository root. Every step prints a header and the
#  script stops at the first failure with a non-zero exit status.
#
#  Subcommands: build, prove, prove-partition <name>, partitions-check,
#  test, cli, vectors, values, lint, all. The proof partitions of the hosted
#  runner are listed in scripts/prove-partitions.txt (ADR 0033).

set -euo pipefail

usage() {
   echo "usage: scripts/check.sh {build|prove|prove-partition <name>|" \
        "partitions-check|test|cli|vectors|values|lint|lean|lean-source|all|reuse|" \
        "reuse-spark|reuse-lean}" >&2
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
   if [ "$status" -ne 0 ]; then
      exit "$status"
   fi
   echo "partitions-check: $(echo "$listed" | wc -l | tr -d ' ') units in" \
        "$(grep -cv '^[[:space:]]*#\|^[[:space:]]*$' "$partitions") partitions," \
        "complete (the workflow proves them in one job, ADR 0060)"
}

#  The harnesses are independent, so they run concurrently (ADR 0034)
#  and the step lasts as long as the slowest. Each writes its own log,
#  printed in a fixed order once all have finished, so that the output
#  reads as before and a failure is attributed to its harness. Every
#  case runs, on both fields: since ADR 0044 the field contracts are
#  proof-only, and the step lasts as long as circuit_kat on the mDoc
#  circuits, minutes.
do_test() {
   header "test: build the harnesses (assertions on)"
   alr -n exec -- gprbuild -P tests/longfellow_spark_tests.gpr -p
   local harnesses="gf2_128_kat p256_kat q256_kat ecdsa_kat mdoc_parse_kat mdoc_witness_kat sumcheck_kat transcript_kat ligero_kat circuit_kat writer_kat prover_kat fft_kat mdoc_kat gadgets_kat checker_kat"
   local logs status=0 h code
   logs="$(mktemp -d)"
   header "test: $harnesses, concurrently"
   for h in $harnesses; do
      ( tests/bin/"$h" > "$logs/$h.log" 2>&1; echo $? > "$logs/$h.status" ) &
   done
   wait
   #  A harness whose exit status is anything but 0, or was never
   #  written (the harness or its subshell killed by a signal), fails.
   for h in $harnesses; do
      header "test: $h"
      cat "$logs/$h.log"
      code="$(cat "$logs/$h.status" 2> /dev/null)"
      if [ "${code:-none}" != 0 ]; then
         echo "test: $h failed (exit status ${code:-unknown})" >&2
         status=1
      fi
   done
   rm -rf "$logs"
   if [ "$status" -ne 0 ]; then
      exit "$status"
   fi
}

#  The Lean proofs the SPARK proof cites (lean/; ADR 0091, chapter 10
#  Section 2): Mathlib's compiled files from its cache, the build of
#  the project's proofs (warnings are errors in LongfellowSpark), the
#  axiom check of the cited theorems, and the vectors of the model,
#  which must be the committed file the tests read. lean/.lake is kept
#  between runs (it is ignored by git). It runs on the proving machine,
#  where elan is installed, and in the job lean of the GitHub workflow.
do_lean() {
   header "lean: the Lean proofs of lean/, their axioms and the model's vectors"
   #  On GitHub Actions only the job lean of the workflow runs it
   #  (LONGFELLOW_LEAN=1); the job verify skips it.
   if [ -n "${GITHUB_ACTIONS:-}" ] && [ -z "${LONGFELLOW_LEAN:-}" ]; then
      echo "lean: skipped in this job; the job lean runs it, and the gate on the proving machine"
      return 0
   fi
   if ! command -v lake > /dev/null 2>&1 && [ -x "$HOME/.elan/bin/lake" ]; then
      PATH="$HOME/.elan/bin:$PATH"
   fi
   command -v lake > /dev/null 2>&1 || { echo "lean: lake not found (install elan)" >&2; exit 1; }
   ( cd lean && lake exe cache get && lake build && lake env lean scripts/Axioms.lean )
   #  The kernel again, on the files the build used: leanchecker, of the
   #  pinned toolchain, replays every declaration of the environment the
   #  project's modules import, Mathlib's cached files included, and
   #  exits non-zero on one it refuses (register row L2).
   ( cd lean && lake env leanchecker --fresh LongfellowSpark ) || {
      echo "lean: leanchecker refused a declaration of the environment" >&2
      exit 1
   }
   ( cd lean && lake env lean scripts/Vectors.lean ) | diff - tests/vectors/lean_gf2_128.txt || {
      echo "lean: tests/vectors/lean_gf2_128.txt is not the output of lean/scripts/Vectors.lean" >&2
      exit 1
   }
   echo "lean: built, axioms checked, replayed by leanchecker, vectors current"
}

#  At a release (docs/process.md, register row L2): the Lean proofs built
#  in a copy of lean/ without Mathlib's cache, so that every imported
#  Mathlib module is elaborated and checked again from its source at the
#  revision of lean/lake-manifest.json. Lake clones the packages into the
#  copy; about 10 minutes on the proving machine, and 3 GB of disk.
do_lean_source() {
   header "lean-source: the Lean proofs with Mathlib built from source, without its cache"
   if ! command -v lake > /dev/null 2>&1 && [ -x "$HOME/.elan/bin/lake" ]; then
      PATH="$HOME/.elan/bin:$PATH"
   fi
   command -v lake > /dev/null 2>&1 || { echo "lean-source: lake not found (install elan)" >&2; exit 1; }
   local d
   d="$(mktemp -d)"
   mkdir "$d/lean"
   ( cd lean && tar --exclude=./.lake -cf - . ) | ( cd "$d/lean" && tar -xf - )
   #  Neither of Lake's caches: LAKE_NO_CACHE stops the download of
   #  packages' prebuilt archives, LAKE_ARTIFACT_CACHE=false the reading
   #  of the shared artefact cache, so every module is compiled here.
   ( cd "$d/lean" && LAKE_NO_CACHE=1 LAKE_ARTIFACT_CACHE=false lake build \
        && lake env lean scripts/Axioms.lean ) || {
      rm -rf "$d"
      echo "lean-source: the build from source failed" >&2
      exit 1
   }
   #  The evidence that the modules were compiled in the copy: the
   #  compiled Mathlib modules found there.
   local n
   n="$(find "$d/lean/.lake/packages/mathlib/.lake/build/lib/lean" -name '*.olean' 2> /dev/null | wc -l | tr -d ' ')"
   rm -rf "$d"
   if [ "$n" -eq 0 ]; then
      echo "lean-source: no Mathlib module was compiled in the copy" >&2
      exit 1
   fi
   echo "lean-source: Mathlib and the project built from source ($n Mathlib modules compiled in the copy), axioms checked"
}

#  The release build (ADR 0046, 0048): the command-line verifier and
#  the interop harness, built without assertions as the verifier is
#  meant to run. interop_kat verifies the two upstream proofs end to
#  end and refuses the altered copies; the verifier accepts the same
#  two proofs with exit status 0, refuses with 1 under a wrong label and
#  reports a usage error with 2. The step ends with the round trip on
#  the four production mDoc circuits (scripts/measure-mdoc.sh, once,
#  with the default 8 MB stack of ADR 0056): the proofs state what the
#  prover computes, not that the verifier accepts it, so completeness
#  on the circuits the project is about is tested here (the trusted
#  base register, V6); then the mDoc proof of age on both archives
#  (measure-mdoc.sh mdoc, ADR 0058): made from the upstream witnesses,
#  accepted by longfellow_verify_mdoc, the upstream example proofs
#  accepted, the altered copies refused.
#  In the build "proved" the run-time checks are suppressed (-gnatp) in
#  the library units of src/ only (ADR 0068). The switches each unit was
#  compiled with are read from its ALI file (lines "A"), so the check
#  covers what the compiler did, not the list in the project file.
check_cli_switches() {
   local obj=cli/obj/proved status=0 f u ali
   header "cli: run-time checks on in cli/src/, suppressed in src/ only"
   for f in cli/src/*.ad[sb]; do
      u=$(basename "${f%.*}")
      ali=$obj/$u.ali
      if [ ! -f "$ali" ]; then
         echo "cli: $f was not compiled ($ali missing)" >&2
         status=1
      elif grep -q -x -e 'A -gnatp' "$ali"; then
         echo "cli: $f compiled with -gnatp" >&2
         status=1
      fi
   done
   #  Specs and bodies: an instance declared by a spec alone, such as
   #  zk_verifier_p256.ads, holds executable code too. One ALI per unit.
   for u in $(for f in src/*.ad[sb]; do basename "${f%.*}"; done | sort -u); do
      ali=$obj/$u.ali
      if [ -f "$ali" ] && ! grep -q -x -e 'A -gnatp' "$ali"; then
         echo "cli: unit $u of src/ compiled with run-time checks" >&2
         status=1
      fi
   done
   if [ "$status" -ne 0 ]; then
      exit "$status"
   fi
   echo "cli: checks on in every unit of cli/src/, off in the units of src/"
}

do_cli() {
   header "cli: build cli/longfellow_verify.gpr (assertions off)"
   alr -n exec -- gprbuild -P cli/longfellow_verify.gpr -p -s
   if [ "${LONGFELLOW_CLI_BUILD:-proved}" = proved ]; then
      check_cli_switches
   fi
   local c=tests/vectors/upstream/circuits status
   header "cli: interop_kat, the upstream proofs end to end"
   cli/bin/interop_kat
   header "cli: first_step_bench --check, the packed first step against the exact bound quad on the mDoc version 7 circuits"
   local m=tests/vectors/upstream/mdoc h=8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121
   cli/bin/first_step_bench --field gf2_128 --circuit $m/${h}_hash.lfc2 --check
   cli/bin/first_step_bench --field p256 --circuit $m/${h}_sig.lfc2 --check
   #  The checker's walk on the registered hash circuit with its pinned
   #  certificate (ADR 0094), in the release build; then one changed
   #  count of the certificate and one changed byte of the circuit, each
   #  refused (exit status 1).
   header "cli: longfellow_check_circuit, the walk on the registered hash circuit"
   local cert=tests/vectors/certificates/${h}_hash.lfck out mut
   out="$(cli/bin/longfellow_check_circuit --field gf2_128 \
      --circuit $m/${h}_hash.lfc2 --certificate $cert)"
   echo "$out"
   if ! grep -qx "walk: accepted" <<< "$out"; then
      echo "cli: the walk does not accept the registered hash circuit" >&2
      exit 1
   fi
   mut="$(mktemp -d)"
   python3 -I -c 'import sys; d = bytearray(open(sys.argv[1], "rb").read()); d[-1] ^= 1; open(sys.argv[2], "wb").write(d)' \
      "$cert" "$mut/count.lfck"
   python3 -I -c 'import sys; d = bytearray(open(sys.argv[1], "rb").read()); d[len(d) // 2] ^= 1; open(sys.argv[2], "wb").write(d)' \
      "$m/${h}_hash.lfc2" "$mut/circuit.lfc2"
   status=0
   cli/bin/longfellow_check_circuit --field gf2_128 --circuit $m/${h}_hash.lfc2 \
      --certificate "$mut/count.lfck" || status=$?
   if [ "$status" -ne 1 ]; then
      echo "cli: a changed count is not refused (exit $status)" >&2
      exit 1
   fi
   status=0
   cli/bin/longfellow_check_circuit --field gf2_128 --circuit "$mut/circuit.lfc2" \
      --certificate $cert || status=$?
   if [ "$status" -ne 1 ]; then
      echo "cli: a changed byte of the circuit is not refused (exit $status)" >&2
      exit 1
   fi
   status=0
   cli/bin/longfellow_check_circuit --field gf2_128 --circuit "$mut/none.lfc2" \
      --certificate $cert || status=$?
   if [ "$status" -ne 2 ]; then
      echo "cli: a missing file is not a usage error (exit $status)" >&2
      exit 1
   fi
   rm -rf "$mut"
   header "cli: longfellow_verify on the two upstream proofs"
   cli/bin/longfellow_verify --field gf2_128 --circuit $c/sha256_circuit.lfc2 \
      --proof $c/sha256_proof.bin --label sha256_spec_test \
      --rate-inv 3 --nreq 16 --ncol 256
   cli/bin/longfellow_verify --field p256 --circuit $c/ecdsa2_circuit.lfc2 \
      --proof $c/ecdsa2_proof.bin --label ecdsa2_spec_test \
      --rate-inv 4 --nreq 16 --ncol 256
   header "cli: a wrong label is refused, a missing argument is a usage error"
   status=0
   cli/bin/longfellow_verify --field gf2_128 --circuit $c/sha256_circuit.lfc2 \
      --proof $c/sha256_proof.bin --label wrong \
      --rate-inv 3 --nreq 16 --ncol 256 || status=$?
   if [ "$status" -ne 1 ]; then
      echo "cli: expected exit status 1 under a wrong label, got $status" >&2
      exit 1
   fi
   status=0
   cli/bin/longfellow_verify --field p256 2>/dev/null || status=$?
   if [ "$status" -ne 2 ]; then
      echo "cli: expected exit status 2 on a usage error, got $status" >&2
      exit 1
   fi
   echo "cli: both proofs accepted, refusal and usage error reported"
   header "cli: longfellow_prove reproduces the two upstream proofs byte for byte"
   mkdir -p cli/out
   cli/bin/longfellow_prove --field gf2_128 --circuit $c/sha256_circuit.lfc2 \
      --inputs $c/sha256_inputs.json --label sha256_spec_test \
      --rate-inv 3 --nreq 16 --ncol 256 --seed 12345 \
      --out cli/out/sha256_proof.bin
   cmp cli/out/sha256_proof.bin $c/sha256_proof.bin
   cli/bin/longfellow_prove --field p256 --circuit $c/ecdsa2_circuit.lfc2 \
      --inputs $c/ecdsa2_inputs.json --label ecdsa2_spec_test \
      --rate-inv 4 --nreq 16 --ncol 256 --seed 123456789 \
      --out cli/out/ecdsa2_proof.bin
   cmp cli/out/ecdsa2_proof.bin $c/ecdsa2_proof.bin
   header "cli: proofs under another seed and under the system source are accepted"
   cli/bin/longfellow_prove --field gf2_128 --circuit $c/sha256_circuit.lfc2 \
      --inputs $c/sha256_inputs.json --label sha256_spec_test \
      --rate-inv 3 --nreq 16 --ncol 256 --seed 7 \
      --out cli/out/sha256_seed7.bin
   cli/bin/longfellow_verify --field gf2_128 --circuit $c/sha256_circuit.lfc2 \
      --proof cli/out/sha256_seed7.bin --label sha256_spec_test \
      --rate-inv 3 --nreq 16 --ncol 256
   cli/bin/longfellow_prove --field p256 --circuit $c/ecdsa2_circuit.lfc2 \
      --inputs $c/ecdsa2_inputs.json --label ecdsa2_spec_test \
      --rate-inv 4 --nreq 16 --ncol 256 \
      --out cli/out/ecdsa2_system.bin
   cli/bin/longfellow_verify --field p256 --circuit $c/ecdsa2_circuit.lfc2 \
      --proof cli/out/ecdsa2_system.bin --label ecdsa2_spec_test \
      --rate-inv 4 --nreq 16 --ncol 256
   header "cli: wrong inputs are a prover status, a missing argument a usage error"
   echo '["1", "0"]' > cli/out/short_inputs.json
   status=0
   cli/bin/longfellow_prove --field gf2_128 --circuit $c/sha256_circuit.lfc2 \
      --inputs cli/out/short_inputs.json --label sha256_spec_test \
      --rate-inv 3 --nreq 16 --ncol 256 --seed 1 \
      --out cli/out/never.bin || status=$?
   if [ "$status" -ne 1 ]; then
      echo "cli: expected exit status 1 on short inputs, got $status" >&2
      exit 1
   fi
   status=0
   cli/bin/longfellow_prove --field p256 2>/dev/null || status=$?
   if [ "$status" -ne 2 ]; then
      echo "cli: expected exit status 2 on a usage error, got $status" >&2
      exit 1
   fi
   echo "cli: both upstream proofs reproduced byte for byte, other proofs accepted"
   header "cli: the round trip on the four mDoc circuits, default stack (measure-mdoc.sh)"
   MEASURE_STACK_KB=8192 scripts/measure-mdoc.sh
   echo "cli: the four mDoc proofs made from the upstream witnesses and accepted"
   header "cli: the mDoc proof of age on both archives, default stack (measure-mdoc.sh mdoc)"
   MEASURE_STACK_KB=8192 scripts/measure-mdoc.sh mdoc
   echo "cli: the mDoc proofs made from the witness files and from the documents and accepted, the upstream example proofs accepted, the altered copies and the wrong requests refused"
   header "cli: the proof of age from every test document of upstream, both versions (mdoc-cases.sh; skipped on GitHub Actions)"
   if [ "${GITHUB_ACTIONS:-}" = true ]; then
      echo "cli: mdoc-cases skipped on GitHub Actions, whose job would exceed its 30 minutes;" \
         "the step runs on the proving machine (docs/process.md)"
   else
      scripts/mdoc-cases.sh
   fi
   header "cli: the relation of the hash circuit against its evaluator, case by case (relation_cases; skipped on GitHub Actions)"
   if [ "${GITHUB_ACTIONS:-}" = true ]; then
      echo "cli: relation_cases skipped on GitHub Actions, with mdoc-cases;" \
         "the step runs on the proving machine (docs/process.md)"
   else
      alr -n exec -- gprbuild -P tests/relation/relation_cases.gpr -p -s
      tests/relation/bin/relation_cases \
         tests/vectors/upstream/mdoc/8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121_hash.lfc2 \
         tests/vectors/relation_cases.txt tests/vectors/upstream/mdoc/testcases
   fi
   header "cli: the cross-check with upstream's verifier (cross-check-upstream.sh; skipped without LONGFELLOW_UPSTREAM)"
   scripts/cross-check-upstream.sh
}

#  The values check (#171): every assertion that the clauses Bits, Chain,
#  Zero_Tail and Length of the hash relation require is found in the
#  registered hash circuit, at two points derived from the file's digest.
#  A tested polynomial identity, not a proof (register row V15). It runs
#  in every gate, the gates that reuse a proof included, since its
#  inputs are no proof's.
do_values() {
   header "values: the SHA-256 clauses of the hash relation on the registered circuit (values-check.py)"
   python3 -I scripts/values-check.py \
      tests/vectors/upstream/mdoc/8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121_hash.lfc2
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
   python3 -I tests/vectors/gen_ligero_vectors.py "$scratch"
   python3 -I tests/vectors/gen_circuit_vectors.py "$scratch"
   python3 -I tests/vectors/gen_prover_vectors.py "$scratch"
   python3 -I tests/vectors/gen_mdoc_vectors.py "$scratch"
   python3 -I tests/vectors/gen_fft_vectors.py "$scratch"
   python3 -I tests/vectors/gen_rs_p256_vectors.py "$scratch"
   python3 -I tests/vectors/gen_mdoc_layer_vectors.py "$scratch"
   python3 -I tests/vectors/gen_q256_vectors.py "$scratch"
   python3 -I tests/vectors/gen_ecdsa_witness_vectors.py "$scratch"
   python3 -I tests/vectors/gen_mdoc_parse_vectors.py "$scratch"
   python3 -I tests/vectors/gen_mdoc_witness_vectors.py "$scratch"
   python3 -I tests/vectors/gen_checker_vectors.py "$scratch"
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
   #  The circuit checker against scripts/census.py, its independent
   #  computation, on the registered version 7 pair (ADR 0093): with the
   #  certificate census.py writes, the checker must accept and give the
   #  digest of the facts census.py gives.
   header "vectors: the circuit checker against census.py on the registered pair"
   alr -n exec -- gprbuild -P tests/checker/checker_census.gpr -p -s
   local kind field circuit want got
   for kind in hash sig; do
      field=gf2_128
      [ "$kind" = sig ] && field=p256
      circuit="tests/vectors/upstream/mdoc/8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121_$kind.lfc2"
      python3 -I scripts/census.py "$circuit" "$field" \
         --json "$scratch/census-$kind.json" --certificate "$scratch/$kind.lfck"
      want="$(python3 -I -c 'import json, sys; print(json.load(open(sys.argv[1]))["facts_sha256"])' "$scratch/census-$kind.json")"
      got="$(tests/checker/bin/checker_census "$field" "$circuit" "$scratch/$kind.lfck")"
      echo "vectors: $kind: census.py $want; checker $got"
      if [ "$got" != "accepted - $want" ]; then
         echo "vectors: the checker differs from census.py on the $kind circuit" >&2
         exit 1
      fi
   done
   #  The pinned certificate of the hash circuit (ADR 0094) is the one
   #  census.py writes, and has the digest pinned beside it.
   local pinned=tests/vectors/certificates/8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121_hash.lfck
   if ! cmp -s "$pinned" "$scratch/hash.lfck"; then
      echo "vectors: $pinned is not the certificate census.py writes" >&2
      exit 1
   fi
   if ! (cd tests/vectors/certificates && sha256sum -c "$(basename "$pinned").sha256"); then
      echo "vectors: $pinned does not have its pinned digest" >&2
      exit 1
   fi
   echo "vectors: tests/vectors matches the generators"
}

do_lint() {
   header "lint: the clean checkout of the gate (clean-checkout-test.sh)"
   scripts/clean-checkout-test.sh
   #  Every relative link of docs/ and the README resolves, anchors
   #  included; this step reads files only, so it runs everywhere.
   header "lint: relative links of docs/ and the README (check-links.py)"
   python3 -I scripts/check-links-test.py
   python3 -I scripts/check-links.py
   #  Every unit a diagram or a code map of the guide names exists, and
   #  every unit is placed in a map.
   header "lint: the code maps of the guide (check-map.py)"
   python3 -I scripts/check-map-test.py
   python3 -I scripts/check-map.py
   #  The roots by which the performance page's matrices by step are
   #  attributed: recorded stacks and the step each must go to.
   header "lint: the attribution of profiles by step (attribute-steps-test.py)"
   python3 -I scripts/measure/attribute-steps-test.py
   #  The script that gives the guide its tables of verification
   #  conditions: small runs it must count, or refuse when they do not
   #  add up to their summary.
   header "lint: the counts of verification conditions (vc-count-test.py)"
   python3 -I scripts/vc-count-test.py
   #  census.py, the independent computation of the checker's facts (ADR
   #  0093), on small circuits whose facts are written out by hand.
   header "lint: the census of a circuit's facts (census-test.py)"
   python3 -I scripts/census-test.py
   header "lint: the values check of the SHA-256 clauses (values-check-test.py)"
   python3 -I scripts/values-check-test.py
   #  Every body of src/ outside SPARK is an assumption of the proof and
   #  has its row in the register of the trusted base.
   header "lint: the code outside SPARK and its register rows (check-spark-off.py)"
   python3 -I scripts/check-spark-off-test.py
   python3 -I scripts/check-spark-off.py
   header "lint: forbidden content over tracked files"
   #  git grep searches tracked files only, in one process, and exits 0
   #  exactly when something matched. This script is excluded from the
   #  sweep because it has to spell the patterns out.
   local status=0
   local -a scope=(-- . ':!scripts/check.sh')
   #  Outside a git work tree (the copy remote-check.sh makes on the
   #  proving machine) git grep fails and would read as clean; that
   #  script runs this step on the developer's machine instead.
   if ! git rev-parse --is-inside-work-tree > /dev/null 2>&1; then
      echo "lint: not a git work tree, not run here"
      return 0
   fi
   #  U+2014 (em-dash) anywhere but in lean/Upstream/: the files ported
   #  from upstream's formal/ keep upstream's bytes, so that they can be
   #  compared with it by a hash (their provenance headers say so). The
   #  other rules below cover lean/Upstream/ too.
   if git grep -n -I -e $'\xe2\x80\x94' "${scope[@]}" ':!lean/Upstream/'; then
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
   cli)              do_cli ;;
   vectors)          do_vectors ;;
   values)           do_values ;;
   lint)             do_lint ;;
   lean)             do_lean ;;
   lean-source)      do_lean_source ;;
   all)
      do_build
      do_partitions_check
      do_prove
      do_lean
      do_test
      do_cli
      do_vectors
      do_values
      do_lint
      header "all checks passed"
      ;;
   reuse|reuse-spark|reuse-lean)
      #  Every check but the proofs reused, for a commit whose inputs of
      #  the SPARK proof, of the Lean proofs or of both are those of a
      #  commit already proved (ADR 0088): reuse reuses both, reuse-spark
      #  the SPARK proof and runs the step lean, reuse-lean the Lean
      #  proofs and runs the SPARK proof. scripts/remote-check.sh chooses
      #  it and names the proved commits in the status.
      do_build
      do_partitions_check
      if [ "$1" = reuse-lean ]; then do_prove; fi
      if [ "$1" = reuse-spark ]; then do_lean; fi
      do_test
      do_cli
      do_vectors
      do_values
      do_lint
      case "$1" in
         reuse)       header "all checks but the proofs passed; the SPARK and Lean proofs are reused (ADR 0088)" ;;
         reuse-spark) header "all checks but the SPARK proof passed; the SPARK proof is reused (ADR 0088)" ;;
         reuse-lean)  header "all checks but the Lean proofs passed; the Lean proofs are reused (ADR 0088)" ;;
      esac
      ;;
   *) usage ;;
esac
