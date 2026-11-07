#!/bin/bash
#  Measurement of the prover and the verifier on the mDoc production
#  circuits (Phase D, block 1): time and peak memory of longfellow_prove
#  and longfellow_verify on the four circuits of tests/vectors/upstream/
#  mdoc/ with the upstream witnesses, under the configurations of
#  runtime/src/zk_spec.rs. Writes under cli/out/. A prover or verifier
#  that fails ends the script with a non-zero status, so the cli step
#  of make check runs it once, with the default stack, as the test that
#  every proof of the four production circuits is accepted (the trusted
#  base register, V6): the proofs state the structure of the prover,
#  not that the verifier accepts its output.
#
#  Usage: scripts/measure-mdoc.sh [v7|v6] [hash|sig]
#  Needs the release build (make cli) and python3 for the witness
#  conversion. MEASURE_STACK_KB sets the stack limit (default 65520, the
#  64 MB that the hash circuit needed before ADR 0056; 8192 checks that
#  the prover and the verifier fit the default stack).
#
#  Runs on macOS (time -l) and on Linux (GNU time -v), the proving
#  machine of ADR 0060 included; without /usr/bin/time (a hosted runner)
#  the commands run untimed. MEASURE_BIN names another directory of
#  binaries (default cli/bin). MEASURE_PROFILE=1 runs each command under
#  perf record at 99 samples a second with call graphs, and writes two
#  reports per run under cli/out/: the time per function including its
#  callees (*.children.txt), which gives the phases, and the time spent
#  in each function itself (*.self.txt). Call graphs need a build with
#  frame pointers (-cargs -fno-omit-frame-pointer); the timing runs use
#  the plain release build.
set -euo pipefail
cd "$(dirname "$0")/.."
#  The two labels of every series (#127): this project's commit, from
#  git or from MEASURE_COMMIT where the tree is not a repository (the
#  copy on the proving machine), and the upstream commit measured in
#  the same session, d5e6be7 (the pin) unless MEASURE_UPSTREAM says
#  otherwise. The pin does not move when a newer upstream is measured.
OURS="${MEASURE_COMMIT:-$(git describe --always --dirty --tags 2> /dev/null || echo unknown)}"
echo "measure-mdoc: longfellow-spark $OURS, upstream ${MEASURE_UPSTREAM:-d5e6be7}"
ulimit -s "${MEASURE_STACK_KB:-65520}"
BIN="${MEASURE_BIN:-cli/bin}"
if [ "$(uname)" = Linux ]; then
   TIME=(/usr/bin/time -v)
   KEEP="ok:|^ok|Elapsed|User time|Maximum resident|_failed|error|exhausted|encoding|length"
else
   TIME=(/usr/bin/time -l)
   KEEP="ok:|^ok|real|user|maximum resident|_failed|error|exhausted|encoding|length"
fi
if [ ! -x /usr/bin/time ]; then
   echo "measure-mdoc: no /usr/bin/time, the runs are not timed"
   TIME=()
fi
#  run <name> <command...>: timed, and under perf when profiling. A
#  command that fails ends the script with its last lines: a prover or
#  verifier that refuses the case must not pass for a measurement.
run() {
   local name="$1" out; shift
   if [ -n "${MEASURE_PROFILE:-}" ]; then
      out="$(perf record -q -F 99 -g -o "cli/out/$name.perf.data" -- "$@" 2>&1)" \
         || { echo "$out" | tail -20; echo "measure-mdoc: $name failed" >&2; return 1; }
      echo "$out" | grep -E "$KEEP" || true
      perf report -i "cli/out/$name.perf.data" --children --sort symbol --stdio \
         --percent-limit 0.5 2> /dev/null | grep -v '^$' > "cli/out/$name.children.txt" || true
      perf report -i "cli/out/$name.perf.data" --no-children --sort symbol --stdio \
         --percent-limit 0.5 -g none 2> /dev/null | grep -v '^$' > "cli/out/$name.self.txt" || true
      echo "profile: cli/out/$name.children.txt, cli/out/$name.self.txt"
   else
      #  The expansion is written so that an empty TIME is no error
      #  under set -u in the bash of macOS (3.2).
      out="$(${TIME[@]+"${TIME[@]}"} "$@" 2>&1)" \
         || { echo "$out" | tail -20; echo "measure-mdoc: $name failed" >&2; return 1; }
      echo "$out" | grep -E "$KEEP" || true
   fi
}
M=tests/vectors/upstream/mdoc
#  The circuit hash and the Ligero configuration of each version, by
#  case statements: the bash of macOS (3.2) has no associative arrays.
hash_of() {
   case $1 in
      v7) echo 8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121 ;;
      v6) echo 137e5a75ce72735a37c8a72da1a8a0a5df8d13365c2ae3d2c2bd6a0e7197c7c6 ;;
   esac
}
cfg_of() {
   case $1 in
      v7_hash) echo "7 132 4151" ;;
      v7_sig)  echo "7 132 4096" ;;
      v6_hash) echo "4 128 4096" ;;
      v6_sig)  echo "4 128 2945" ;;
   esac
}
#  The public inputs of each circuit, from tests/vectors/mdoc_summary.txt
#  (the sixth field of its summary rows): the hash circuits differ.
public_of() {
   case $1 in
      v7_hash) echo 952 ;;
      v6_hash) echo 944 ;;
      *)       echo 900 ;;
   esac
}
mkdir -p cli/out
#  The arguments are read once, before the loops: nothing below may
#  reassign the positional parameters.
VERSIONS="${1:-v7 v6}"
CASES="${2:-hash sig}"
for v in $VERSIONS; do
   for c in $CASES; do
      h=$(hash_of "$v")
      case $c in hash) f=gf2_128; s=16 ;; sig) f=p256; s=32 ;; esac
      read -r rate nreq ncol <<< "$(cfg_of "${v}_$c")"
      in=cli/out/mdoc_${v}_${c}_inputs.json
      python3 - "$M/${h}_${c}_witness.bin" "$s" "$in" <<'PY'
import json, sys
raw = open(sys.argv[1], "rb").read(); size = int(sys.argv[2])
vals = [str(int.from_bytes(raw[i:i + size], "little")) for i in range(0, len(raw), size)]
open(sys.argv[3], "w").write(json.dumps(vals))
PY
      echo "=== $v $c: prove (rate $rate, nreq $nreq, ncol $ncol) ==="
      run mdoc_${v}_${c}_prove "$BIN/longfellow_prove" --field $f --circuit $M/${h}_$c.lfc2 \
         --inputs $in --label mdoc_${c}_test --rate-inv $rate --nreq $nreq --ncol $ncol \
         --seed 1 --out cli/out/mdoc_${v}_$c.bin
      echo "=== $v $c: verify ==="
      np=$(public_of "${v}_$c")
      python3 - "$in" "$np" "$s" > cli/out/mdoc_${v}_${c}_public.args <<'PY'
import json, sys
vals = json.load(open(sys.argv[1])); n = int(sys.argv[2]); digits = 2 * int(sys.argv[3])
print(" ".join("--public %0*x" % (digits, int(x)) for x in vals[:n]))
PY
      run mdoc_${v}_${c}_verify "$BIN/longfellow_verify" --field $f --circuit $M/${h}_$c.lfc2 \
         --proof cli/out/mdoc_${v}_$c.bin --label mdoc_${c}_test --rate-inv $rate --nreq $nreq --ncol $ncol \
         $(cat cli/out/mdoc_${v}_${c}_public.args)
   done
done
