#!/bin/bash
#  Measurement of the prover and the verifier on the mDoc production
#  circuits (Phase D, block 1): time and peak memory of longfellow_prove
#  and longfellow_verify on the four circuits of tests/vectors/upstream/
#  mdoc/ with the upstream witnesses, under the configurations of
#  runtime/src/zk_spec.rs. Not part of make check: it takes minutes to
#  hours while the encoder is the Lagrange one. Writes under cli/out/.
#
#  Usage: scripts/measure-mdoc.sh [v7|v6] [hash|sig]
#  Needs the release build (make cli) and python3 for the witness
#  conversion. MEASURE_STACK_KB sets the stack limit (default 65520, the
#  64 MB that the hash circuit needed before ADR 0056; 8192 checks that
#  the prover and the verifier fit the default stack).
#
#  Runs on macOS (time -l) and on Linux (GNU time -v), the proving
#  machine of ADR 0060 included. MEASURE_BIN names another directory of
#  binaries (default cli/bin). MEASURE_PROFILE=1 runs each command under
#  perf record at 99 samples a second with call graphs, and writes two
#  reports per run under cli/out/: the time per function including its
#  callees (*.children.txt), which gives the phases, and the time spent
#  in each function itself (*.self.txt). Call graphs need a build with
#  frame pointers (-cargs -fno-omit-frame-pointer); the timing runs use
#  the plain release build.
set -eu
cd "$(dirname "$0")/.."
ulimit -s "${MEASURE_STACK_KB:-65520}"
BIN="${MEASURE_BIN:-cli/bin}"
if [ "$(uname)" = Linux ]; then
   TIME=(/usr/bin/time -v)
   KEEP="ok:|^ok|Elapsed|User time|Maximum resident|_failed|error|exhausted|encoding|length"
else
   TIME=(/usr/bin/time -l)
   KEEP="ok:|^ok|real|user|maximum resident|_failed|error|exhausted|encoding|length"
fi
#  run <name> <command...>: timed, and under perf when profiling.
run() {
   local name="$1"; shift
   if [ -n "${MEASURE_PROFILE:-}" ]; then
      perf record -q -F 99 -g -o "cli/out/$name.perf.data" -- "$@" 2>&1 | grep -E "$KEEP" || true
      perf report -i "cli/out/$name.perf.data" --children --sort symbol --stdio \
         --percent-limit 0.5 2> /dev/null | grep -v '^$' > "cli/out/$name.children.txt" || true
      perf report -i "cli/out/$name.perf.data" --no-children --sort symbol --stdio \
         --percent-limit 0.5 -g none 2> /dev/null | grep -v '^$' > "cli/out/$name.self.txt" || true
      echo "profile: cli/out/$name.children.txt, cli/out/$name.self.txt"
   else
      "${TIME[@]}" "$@" 2>&1 | grep -E "$KEEP" || true
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
mkdir -p cli/out
for v in ${1:-v7 v6}; do
   for c in ${2:-hash sig}; do
      h=$(hash_of "$v")
      case $c in hash) f=gf2_128; s=16 ;; sig) f=p256; s=32 ;; esac
      # shellcheck disable=SC2046 # the three numbers are split on purpose
      set -- $(cfg_of "${v}_$c")
      in=cli/out/mdoc_${v}_${c}_inputs.json
      python3 - "$M/${h}_${c}_witness.bin" "$s" "$in" <<'PY'
import json, sys
raw = open(sys.argv[1], "rb").read(); size = int(sys.argv[2])
vals = [str(int.from_bytes(raw[i:i + size], "little")) for i in range(0, len(raw), size)]
open(sys.argv[3], "w").write(json.dumps(vals))
PY
      echo "=== $v $c: prove (rate $1, nreq $2, ncol $3) ==="
      run mdoc_${v}_${c}_prove "$BIN/longfellow_prove" --field $f --circuit $M/${h}_$c.lfc2 \
         --inputs $in --label mdoc_${c}_test --rate-inv $1 --nreq $2 --ncol $3 \
         --seed 1 --out cli/out/mdoc_${v}_$c.bin
      echo "=== $v $c: verify ==="
      case $c in hash) np=952 ;; sig) np=900 ;; esac
      python3 - "$in" "$np" "$s" > cli/out/mdoc_${v}_${c}_public.args <<'PY'
import json, sys
vals = json.load(open(sys.argv[1])); n = int(sys.argv[2]); digits = 2 * int(sys.argv[3])
print(" ".join("--public %0*x" % (digits, int(x)) for x in vals[:n]))
PY
      run mdoc_${v}_${c}_verify "$BIN/longfellow_verify" --field $f --circuit $M/${h}_$c.lfc2 \
         --proof cli/out/mdoc_${v}_$c.bin --label mdoc_${c}_test --rate-inv $1 --nreq $2 --ncol $3 \
         $(cat cli/out/mdoc_${v}_${c}_public.args)
   done
done
