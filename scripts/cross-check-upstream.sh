#!/usr/bin/env bash
#  The cross-check of the mDoc proofs with upstream's verifier (chapter 9,
#  Section 5.1; ADR 0087), a step of `make check` through scripts/check.sh.
#
#  Builds tests/vectors/upstream/verify_mdoc.rs as an example of upstream's
#  runtime crate at the pin d5e6be7, on a working copy made from the clone
#  of upstream that LONGFELLOW_UPSTREAM names, and runs it on the two mDoc
#  proofs the cli step writes under cli/out/ (both must be accepted) and
#  on the altered copy of the version 6 proof (it must be refused).
#
#  Environment:
#     LONGFELLOW_UPSTREAM         a clone of longfellow-zk/longfellow-zk that
#                                 contains the pin. Unset: the step is
#                                 skipped and says so; it runs on the
#                                 proving machine, which has the clone.
#     LONGFELLOW_CROSS_CHECK_DIR  where the working copy and its build
#                                 stay between runs, so that only the first
#                                 run builds upstream's crate (default
#                                 ~/.cache/longfellow-spark/cross-check).
#  cargo must be on PATH, or installed by rustup (~/.cargo/env is sourced).
#
#  Exit status: 0 when both proofs are accepted and the altered copy is
#  refused, or when the step is skipped; 1 otherwise.

set -euo pipefail

PIN=d5e6be77336933d50bf7f25a954f8ec273eb51ce
V7=cli/out/mdoc_v7_proof.bin
V6=cli/out/mdoc_v6_proof.bin
ALTERED=cli/out/mdoc_v6_altered.bin

if [ -z "${LONGFELLOW_UPSTREAM:-}" ]; then
   echo "cross-check: skipped, LONGFELLOW_UPSTREAM is not set;" \
      "the step runs on the proving machine (docs/process.md)"
   exit 0
fi

for f in "$V7" "$V6" "$ALTERED"; do
   if [ ! -f "$f" ]; then
      echo "cross-check: $f is missing;" \
         "scripts/measure-mdoc.sh mdoc writes it" >&2
      exit 1
   fi
done

if ! command -v cargo > /dev/null 2>&1 && [ -f "$HOME/.cargo/env" ]; then
   # shellcheck disable=SC1091
   . "$HOME/.cargo/env"
fi
if ! command -v cargo > /dev/null 2>&1; then
   echo "cross-check: cargo is not on PATH" >&2
   exit 1
fi

if ! git -C "$LONGFELLOW_UPSTREAM" cat-file -e "$PIN^{commit}" 2> /dev/null
then
   echo "cross-check: $LONGFELLOW_UPSTREAM has no commit $PIN" >&2
   exit 1
fi

#  The working copy: a shared clone at the pin, never the clone itself,
#  so that nothing is built or written in a reference checkout.
DIR="${LONGFELLOW_CROSS_CHECK_DIR:-$HOME/.cache/longfellow-spark/cross-check}"
mkdir -p "$DIR"
DIR="$(cd "$DIR" && pwd)"   # absolute: cargo and this script agree on it
UP="$DIR/upstream"
if [ ! -d "$UP/.git" ]; then
   git clone -q --shared --no-checkout "$LONGFELLOW_UPSTREAM" "$UP"
fi
if ! git -C "$UP" -c advice.detachedHead=false checkout -q --detach "$PIN" 2> /dev/null; then
   git -C "$UP" fetch -q "$LONGFELLOW_UPSTREAM" "$PIN"
   git -C "$UP" -c advice.detachedHead=false checkout -q --detach "$PIN"
fi
EXAMPLES="$UP/rust/applications/mdoc_zk/runtime/examples"
mkdir -p "$EXAMPLES"
cp tests/vectors/upstream/verify_mdoc.rs "$EXAMPLES/verify_mdoc.rs"

echo "cross-check: upstream $PIN in $UP, $(cargo --version)"
#  The target directory is given, so that no CARGO_TARGET_DIR or cargo
#  configuration sends the build elsewhere, and the executable's path is
#  the one cargo reports for the example (a configured build target adds
#  a directory that a fixed path would miss).
TARGET="$UP/rust/target"
BIN="$(cd "$UP/rust" && cargo build --release -p mdoc-zk-runtime \
   --example verify_mdoc --target-dir "$TARGET" \
   --message-format=json-render-diagnostics \
   | python3 -I -c '
import json, sys
path = ""
for line in sys.stdin:
    try:
        m = json.loads(line)
    except ValueError:
        continue
    if (m.get("reason") == "compiler-artifact"
            and m.get("target", {}).get("name") == "verify_mdoc"
            and m.get("executable")):
        path = m["executable"]
print(path)')"
if [ -z "$BIN" ] || [ ! -x "$BIN" ]; then
   echo "cross-check: cargo did not report the executable of verify_mdoc" >&2
   exit 1
fi

"$BIN" 7 "$V7"
"$BIN" 6 "$V6"
#  A refusal is exactly exit status 3 of the example; anything else, a
#  verdict of acceptance or a failure of the program (a panic, a signal),
#  fails the step. The subshell of two commands keeps the shell's own
#  report of a signal out of the log; the example's output is kept for
#  the report of an unexpected status.
status=0
("$BIN" 6 "$ALTERED" > "$DIR/altered.log" 2>&1; exit $?) 2> /dev/null \
   || status=$?
if [ "$status" -ne 3 ]; then
   echo "cross-check: expected upstream's verifier to refuse $ALTERED" \
      "(exit 3), got exit $status:" >&2
   cat "$DIR/altered.log" >&2
   exit 1
fi
echo "cross-check: both mDoc proofs accepted by upstream's run_mdoc_verifier" \
   "at ${PIN:0:7}, the altered copy refused ($(tail -c 60 "$DIR/altered.log" | tr -d '\n' | sed 's/.*: //'))"
