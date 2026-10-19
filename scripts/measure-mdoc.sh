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
#  conversion; raises the stack limit to 64 MB for Eval_Circuit.
set -eu
cd "$(dirname "$0")/.."
ulimit -s 65520
M=tests/vectors/upstream/mdoc
declare -A HASH=([v7]=8d079211715200ff06c5109639245502bfe94aa869908d31176aae4016182121
                 [v6]=137e5a75ce72735a37c8a72da1a8a0a5df8d13365c2ae3d2c2bd6a0e7197c7c6)
declare -A CFG=([v7_hash]="7 132 4151" [v7_sig]="7 132 4096"
                [v6_hash]="4 128 4096" [v6_sig]="4 128 2945")
mkdir -p cli/out
for v in ${1:-v7 v6}; do
   for c in ${2:-hash sig}; do
      h=${HASH[$v]}
      case $c in hash) f=gf2_128; s=16 ;; sig) f=p256; s=32 ;; esac
      set -- ${CFG[${v}_$c]}
      in=cli/out/mdoc_${v}_${c}_inputs.json
      python3 - "$M/${h}_${c}_witness.bin" "$s" "$in" <<'PY'
import json, sys
raw = open(sys.argv[1], "rb").read(); size = int(sys.argv[2])
vals = [str(int.from_bytes(raw[i:i + size], "little")) for i in range(0, len(raw), size)]
open(sys.argv[3], "w").write(json.dumps(vals))
PY
      echo "=== $v $c: prove (rate $1, nreq $2, ncol $3) ==="
      /usr/bin/time -l cli/bin/longfellow_prove --field $f --circuit $M/${h}_$c.lfc2 \
         --inputs $in --label mdoc_${c}_test --rate-inv $1 --nreq $2 --ncol $3 \
         --seed 1 --out cli/out/mdoc_${v}_$c.bin 2>&1 | grep -E "ok:|real|user|maximum resident|_|error"
      echo "=== $v $c: verify ==="
      case $c in hash) np=952 ;; sig) np=900 ;; esac
      python3 - "$in" "$np" "$s" > cli/out/mdoc_${v}_${c}_public.args <<'PY'
import json, sys
vals = json.load(open(sys.argv[1])); n = int(sys.argv[2]); digits = 2 * int(sys.argv[3])
print(" ".join("--public %0*x" % (digits, int(x)) for x in vals[:n]))
PY
      /usr/bin/time -l cli/bin/longfellow_verify --field $f --circuit $M/${h}_$c.lfc2 \
         --proof cli/out/mdoc_${v}_$c.bin --label mdoc_${c}_test --rate-inv $1 --nreq $2 --ncol $3 \
         $(cat cli/out/mdoc_${v}_${c}_public.args) 2>&1 \
         | grep -E "^ok|real|user|maximum resident|_failed|error|exhausted|encoding|length"
   done
done
