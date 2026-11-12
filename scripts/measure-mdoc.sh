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
#         scripts/measure-mdoc.sh mdoc [v7|v6]
#  The second form is the mDoc proof of age (Phase D, blocks 5 and 6,
#  ADR 0058, ADR 0086) on each archive: longfellow_prove_mdoc from the
#  two upstream witness files under the parameters of the test case they
#  come from (FAMILYNAME_MUSTERMANN_MDOC_3 of upstream's
#  testcases/src/vectors.rs: the attribute family_name with the text
#  value "Mustermann"), then longfellow_verify_mdoc on that proof and on
#  upstream's example proof of the archive, both timed; then, untimed,
#  the refusals: a wrong date, a wrong value, a wrong document type, a
#  tag altered, the proof cut short. Then the proof from the document
#  itself (--mdoc, block 6): the same case's document at each version,
#  and upstream's TEST_DATA document with age_over_18 at version 7, each
#  proved (timed) and verified; then, untimed, the refusals of the
#  document path: an attribute the document does not hold, a document
#  that is not CBOR, one above the parser's bound, an attribute value
#  the document contradicts (upstream's fail-not_over_18 case), both
#  input forms at once. The
#  cli step of make check runs it once with the default stack as the
#  test of the layer (the register, V6 and the mDoc rows).
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
MODE=circuits
if [ "${1:-}" = mdoc ]; then
   MODE=mdoc
   VERSIONS="${2:-v7 v6}"
else
   VERSIONS="${1:-v7 v6}"
fi
CASES="${2:-hash sig}"
#  The test case of the witness files (gen_mdoc_layer_vectors.py has the
#  same constants, checked against the files).
CASE_PKX=0xdc1c1f55cff4cd5c76cf4169278f7217667f86ee81d8669b63f2e19bc12a0c9f
CASE_PKY=0x12355dd0385fed3bc33bedc9781b9aad47b33e4c24704b8d14288b1b3cb45c28
CASE_TRANSCRIPT=83f6f6847142726f7773657248616e646f76657276315820f93ebac4ce4d9901b9aea472145ae5421f8fbecbe5f0389683f59f08fcf90e455833a363636174016474797065016764657461696c73a1676261736555726c75687474703a2f2f6c6f63616c686f73743a3830383058203c79914b7f81a1c2558fc81619dd4a074d32143e6cf6895fe47da156d1c5b0ae
CASE_NOW=2024-10-01T09:00:00Z
CASE_DOC_TYPE=org.iso.18013.5.1.mDL
CASE_ATTR=family_name:6a4d75737465726d616e6e
CASE_DIR=$M/testcases/FAMILYNAME_MUSTERMANN_MDOC_3
#  Upstream's TEST_DATA document (the same bytes as its case
#  age_over_18-website-mdoc[5].json), with its request.
TD_DIR=$M/testcases/TEST_DATA
TD_PKX=0xb4682ec20e06e8df840b5dd32959798ab20c544d4da50109ff4684d06fd261fc
TD_PKY=0xf6f8e9a811911329a5f653fcec5990092c91a65bc1695d291cd51de9c94e7db7
TD_NOW=2025-04-30T00:00:00Z
TD_ATTR=age_over_18:f5
#  expect_refused <name> <status pattern> <command...>: the command must
#  exit with 1 and print a typed status that matches the pattern (an
#  unhandled exception exits with 1 too, and prints a traceback instead).
expect_refused() {
   local name="$1" pattern="$2" status=0 out; shift 2
   out="$("$@" 2>&1)" || status=$?
   if [ "$status" -ne 1 ]; then
      echo "measure-mdoc: $name: expected exit status 1, got $status" >&2
      echo "$out" | tail -5 >&2
      return 1
   fi
   if ! echo "$out" | head -1 | grep -q -E "^${pattern}\$"; then
      echo "measure-mdoc: $name: expected a status matching '$pattern', got:" >&2
      echo "$out" | head -5 >&2
      return 1
   fi
   echo "refused: $name ($(echo "$out" | head -1))"
}
mdoc_round_trip() {
   local v h proof
   for v in $VERSIONS; do
      h=$(hash_of "$v")
      proof=cli/out/mdoc_${v}_proof.bin
      echo "=== $v mdoc: prove (both circuits, one transcript) ==="
      run mdoc_${v}_prove_mdoc "$BIN/longfellow_prove_mdoc" --spec "$h" \
         --hash-witness "$M/${h}_hash_witness.bin" --sig-witness "$M/${h}_sig_witness.bin" \
         --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
         --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR" \
         --seed 1 --out "$proof"
      echo "=== $v mdoc: verify ==="
      run mdoc_${v}_verify_mdoc "$BIN/longfellow_verify_mdoc" --spec "$h" --proof "$proof" \
         --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
         --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR"
      echo "=== $v mdoc: upstream's example proof ==="
      run mdoc_${v}_verify_upstream "$BIN/longfellow_verify_mdoc" --spec "$h" --proof "$M/$h.bin" \
         --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
         --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR"
      echo "=== $v mdoc: the refusals ==="
      expect_refused "$v wrong date" "hash_failed [a-z_]+" "$BIN/longfellow_verify_mdoc" --spec "$h" --proof "$proof" \
         --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
         --now 2024-10-02T09:00:00Z --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR"
      expect_refused "$v wrong value" "hash_failed [a-z_]+" "$BIN/longfellow_verify_mdoc" --spec "$h" --proof "$proof" \
         --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
         --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr family_name:6a4d75737465726d616e6f
      expect_refused "$v wrong document type" "sig_failed [a-z_]+" "$BIN/longfellow_verify_mdoc" --spec "$h" --proof "$proof" \
         --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
         --now "$CASE_NOW" --doc-type org.iso.18013.5.1.mDX --attr "$CASE_ATTR"
      python3 - "$proof" cli/out/mdoc_${v}_altered.bin cli/out/mdoc_${v}_short.bin <<'PY'
import sys
p = bytearray(open(sys.argv[1], "rb").read())
p[5] ^= 1
open(sys.argv[2], "wb").write(p)
open(sys.argv[3], "wb").write(open(sys.argv[1], "rb").read()[:-1])
PY
      expect_refused "$v tag altered" "(hash_failed|sig_failed) [a-z_]+" "$BIN/longfellow_verify_mdoc" --spec "$h" --proof cli/out/mdoc_${v}_altered.bin \
         --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
         --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR"
      expect_refused "$v proof cut short" "sig_failed proof_encoding" "$BIN/longfellow_verify_mdoc" --spec "$h" --proof cli/out/mdoc_${v}_short.bin \
         --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
         --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR"
   done
   #  The refusals of the request itself, through both programs: the
   #  session transcript above 65,000 bytes, an identifier that does not
   #  fit the version 7 layout (31 bytes with a two-byte head), two
   #  attributes against a one-attribute profile (ADR 0089: two to four
   #  are refused by the entry points). On upstream's
   #  checked-in example proof of the version 7 archive, so that the
   #  check does not depend on the proofs this run made.
   local h7 long_tr
   h7=$(hash_of v7)
   long_tr=$(python3 -c 'print("00" * 65001)')
   local long_id=abcdefghijklmnopqrstuvwxyzabcde
   expect_refused "verifier, transcript too long" "transcript_too_long" "$BIN/longfellow_verify_mdoc" --spec "$h7" \
      --proof "$M/$h7.bin" --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$long_tr" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR"
   expect_refused "verifier, attribute invalid" "attribute_invalid" "$BIN/longfellow_verify_mdoc" --spec "$h7" \
      --proof "$M/$h7.bin" --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$long_id:f5"
   expect_refused "verifier, two attributes" "attribute_count" "$BIN/longfellow_verify_mdoc" --spec "$h7" \
      --proof "$M/$h7.bin" --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR" --attr age_over_18:f5
   expect_refused "prover, transcript too long" "transcript_too_long" "$BIN/longfellow_prove_mdoc" --spec "$h7" \
      --hash-witness "$M/${h7}_hash_witness.bin" --sig-witness "$M/${h7}_sig_witness.bin" \
      --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$long_tr" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR" --seed 1 --out cli/out/never.bin
   expect_refused "prover, attribute invalid" "attribute_invalid" "$BIN/longfellow_prove_mdoc" --spec "$h7" \
      --hash-witness "$M/${h7}_hash_witness.bin" --sig-witness "$M/${h7}_sig_witness.bin" \
      --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$long_id:f5" --seed 1 --out cli/out/never.bin
   expect_refused "prover, two attributes" "attribute_count" "$BIN/longfellow_prove_mdoc" --spec "$h7" \
      --hash-witness "$M/${h7}_hash_witness.bin" --sig-witness "$M/${h7}_sig_witness.bin" \
      --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR" --attr age_over_18:f5 --seed 1 --out cli/out/never.bin
   #  A file above the programs' bound (16 MB) is a usage error, exit
   #  status 2, before anything is allocated: a sparse file of 17 MB.
   local status=0 out
   dd if=/dev/zero of=cli/out/mdoc_oversized.bin bs=1 count=0 seek=17825792 2> /dev/null
   out="$("$BIN/longfellow_verify_mdoc" --spec "$h7" --proof cli/out/mdoc_oversized.bin \
      --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR" 2>&1)" || status=$?
   if [ "$status" -ne 2 ] || ! echo "$out" | grep -q "file larger than"; then
      echo "measure-mdoc: oversized proof file: expected exit status 2 and the message, got $status" >&2
      echo "$out" | head -3 >&2
      return 1
   fi
   echo "refused: oversized proof file (usage error)"
   rm -f cli/out/mdoc_oversized.bin
   #  A proof file below the bound but above the default stack (10 MB of
   #  zeros) is read on the heap and refused as a proof, exit status 1.
   dd if=/dev/zero of=cli/out/mdoc_large.bin bs=1048576 count=10 2> /dev/null
   expect_refused "large proof file of zeros" "(hash_failed|sig_failed) [a-z_]+" "$BIN/longfellow_verify_mdoc" --spec "$h7" \
      --proof cli/out/mdoc_large.bin --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR"
   rm -f cli/out/mdoc_large.bin
}
#  The proof from the document (block 6): the Mustermann document at
#  each version, under the same request as the witness files, and the
#  TEST_DATA document at version 7; each verified. The proofs stay under
#  cli/out/ for the cross-check with upstream's verifier.
mdoc_from_documents() {
   local v h proof
   for v in $VERSIONS; do
      h=$(hash_of "$v")
      proof=cli/out/mdoc_doc_${v}_proof.bin
      echo "=== $v mdoc: prove from the document ==="
      run mdoc_doc_${v}_prove "$BIN/longfellow_prove_mdoc" --spec "$h" --mdoc "$CASE_DIR/mdoc.bin" \
         --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript-file "$CASE_DIR/transcript.bin" \
         --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR" \
         --seed 1 --out "$proof"
      echo "=== $v mdoc: verify the proof from the document ==="
      run mdoc_doc_${v}_verify "$BIN/longfellow_verify_mdoc" --spec "$h" --proof "$proof" \
         --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
         --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR"
   done
   local h7
   h7=$(hash_of v7)
   if echo "$VERSIONS" | grep -q v7; then
      echo "=== v7 mdoc: prove from the TEST_DATA document (age_over_18) ==="
      run mdoc_doc_test_data_prove "$BIN/longfellow_prove_mdoc" --spec "$h7" --mdoc "$TD_DIR/mdoc.bin" \
         --pkx "$TD_PKX" --pky "$TD_PKY" --transcript-file "$TD_DIR/transcript.bin" \
         --now "$TD_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$TD_ATTR" \
         --seed 1 --out cli/out/mdoc_doc_test_data_proof.bin
      echo "=== v7 mdoc: verify the TEST_DATA proof ==="
      run mdoc_doc_test_data_verify "$BIN/longfellow_verify_mdoc" --spec "$h7" --proof cli/out/mdoc_doc_test_data_proof.bin \
         --pkx "$TD_PKX" --pky "$TD_PKY" --transcript-file "$TD_DIR/transcript.bin" \
         --now "$TD_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$TD_ATTR"
   fi
   echo "=== mdoc: the refusals of the document path ==="
   expect_refused "two attributes from the document" "attribute_count" "$BIN/longfellow_prove_mdoc" --spec "$h7" \
      --mdoc "$CASE_DIR/mdoc.bin" --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR" --attr age_over_18:f5 --seed 1 --out cli/out/never.bin
   expect_refused "attribute not in the document" "attribute_not_found" "$BIN/longfellow_prove_mdoc" --spec "$h7" \
      --mdoc "$CASE_DIR/mdoc.bin" --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr age_over_99:f5 --seed 1 --out cli/out/never.bin
   expect_refused "document that is not CBOR" "parse_failed cbor_root [a-z_]+" "$BIN/longfellow_prove_mdoc" --spec "$h7" \
      --mdoc "$CASE_DIR/request.txt" --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR" --seed 1 --out cli/out/never.bin
   expect_refused "document above the parser's bound" "parse_failed document_too_long" "$BIN/longfellow_prove_mdoc" --spec "$h7" \
      --mdoc "$M/$h7.bin" --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR" --seed 1 --out cli/out/never.bin
   #  Upstream's negative case fail-not_over_18-mdoc[0]: the document of
   #  +18-mdoc[0] (age_over_18 true) against a request for false.
   local f0=$M/testcases/FAIL_NOT_OVER_18_MDOC_0
   expect_refused "value the document contradicts" "hash_failed not_satisfied" "$BIN/longfellow_prove_mdoc" --spec "$h7" \
      --mdoc "$f0/mdoc.bin" --pkx 0x$(sed -n 's/^pkx 0x//p' "$f0/request.txt") --pky 0x$(sed -n 's/^pky 0x//p' "$f0/request.txt") \
      --transcript-file "$f0/transcript.bin" --now "$(sed -n 's/^now //p' "$f0/request.txt")" \
      --doc-type "$CASE_DOC_TYPE" --attr age_over_18:f4 --seed 1 --out cli/out/never.bin
   #  The case's document with the T of its validUntil in lower case
   #  (#165): refused by the builder before any commitment, since both
   #  circuits compare the dates byte for byte.
   python3 -I - "$CASE_DIR/mdoc.bin" cli/out/mdoc_lower_t.bin <<'PY'
import sys
d = bytearray(open(sys.argv[1], "rb").read())
key = b"\x6avalidUntil\xc0\x74"
i = d.find(key)
if i < 0 or d.find(key, i + 1) >= 0 or d[i + len(key) + 10] != ord("T"):
    sys.exit("measure-mdoc: the case's validUntil is not where expected")
d[i + len(key) + 10] = ord("t")
open(sys.argv[2], "wb").write(bytes(d))
PY
   expect_refused "validity date not in the circuit's form" "validity_form_unsupported" "$BIN/longfellow_prove_mdoc" --spec "$h7" \
      --mdoc cli/out/mdoc_lower_t.bin --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR" --seed 1 --out cli/out/never.bin
   #  The case's document with the device key's crv 1 (P-256) changed to
   #  2 (P-384) (#165): refused by the builder, since both circuits
   #  compare the COSE_Key's bytes with the one form kty, crv, x, y.
   python3 -I - "$CASE_DIR/mdoc.bin" cli/out/mdoc_crv2.bin <<'PY'
import sys
d = bytearray(open(sys.argv[1], "rb").read())
key = b"\x69deviceKey\xa4\x01\x02\x20\x01"
i = d.find(key)
if i < 0 or d.find(key, i + 1) >= 0:
    sys.exit("measure-mdoc: the case's device key is not where expected")
d[i + len(key) - 1] = 0x02
open(sys.argv[2], "wb").write(bytes(d))
PY
   expect_refused "device key not in the circuit's form" "device_key_form_unsupported" "$BIN/longfellow_prove_mdoc" --spec "$h7" \
      --mdoc cli/out/mdoc_crv2.bin --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR" --seed 1 --out cli/out/never.bin
   local status=0 out
   out="$("$BIN/longfellow_prove_mdoc" --spec "$h7" --mdoc "$CASE_DIR/mdoc.bin" \
      --hash-witness "$M/${h7}_hash_witness.bin" --sig-witness "$M/${h7}_sig_witness.bin" \
      --pkx "$CASE_PKX" --pky "$CASE_PKY" --transcript "$CASE_TRANSCRIPT" \
      --now "$CASE_NOW" --doc-type "$CASE_DOC_TYPE" --attr "$CASE_ATTR" --seed 1 --out cli/out/never.bin 2>&1)" || status=$?
   if [ "$status" -ne 2 ] || ! echo "$out" | grep -q "excludes"; then
      echo "measure-mdoc: both input forms: expected exit status 2 and the message, got $status" >&2
      echo "$out" | head -3 >&2
      return 1
   fi
   echo "refused: both input forms at once (usage error)"
}
if [ "$MODE" = mdoc ]; then
   mkdir -p cli/out
   mdoc_round_trip
   mdoc_from_documents
   exit 0
fi
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
