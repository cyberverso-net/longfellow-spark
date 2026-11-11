#!/bin/bash
#  The tests of scripts/clean-checkout.sh, on temporary git clones: a
#  clone with a staged edit, an unstaged edit, a deleted tracked file,
#  an untracked file and an ignored one is restored to the commit, the
#  ignored file kept; the refusals of a commit that does not exist, of
#  a short name that is not the full commit, and of a directory that
#  is not a clone, each with exit status 1. Run by the lint step of
#  make check; needs only git.

set -uo pipefail
cd "$(dirname "$0")/.."
SCRIPT="$PWD/scripts/clean-checkout.sh"
T="$(mktemp -d)"
trap 'rm -rf "$T"' EXIT
fail() { echo "clean-checkout-test: $1" >&2; exit 1; }

g() { git -C "$T/repo" -c user.name=t -c user.email=t@t -c commit.gpgsign=false "$@"; }
mkdir "$T/repo" && g init -q && g config core.hooksPath /dev/null
printf 'a\n' > "$T/repo/a.txt"
printf 'b\n' > "$T/repo/b.txt"
printf 'c\n' > "$T/repo/c.txt"
printf 'build/\n' > "$T/repo/.gitignore"
g add . && g commit -q -m one
C="$(g rev-parse HEAD)"

#  Every kind of change at once.
printf 'staged\n' > "$T/repo/a.txt" && g add a.txt
printf 'unstaged\n' > "$T/repo/b.txt"
rm "$T/repo/c.txt"
printf 'new\n' > "$T/repo/untracked.txt"
mkdir "$T/repo/build" && printf 'kept\n' > "$T/repo/build/out.o"
"$SCRIPT" "$T/repo" "$C" || fail "a dirty clone was not restored"
[ "$(cat "$T/repo/a.txt")" = a ] || fail "the staged edit survived"
[ "$(cat "$T/repo/b.txt")" = b ] || fail "the unstaged edit survived"
[ -f "$T/repo/c.txt" ] || fail "the deleted file was not restored"
[ ! -e "$T/repo/untracked.txt" ] || fail "the untracked file survived"
[ -f "$T/repo/build/out.o" ] || fail "the ignored file was removed"
g diff --quiet HEAD || fail "tracked files differ after the restore"

#  The refusals, each with status 1.
"$SCRIPT" "$T/repo" 0123456789abcdef0123456789abcdef01234567 2> /dev/null
[ $? -eq 1 ] || fail "a missing commit was not refused"
"$SCRIPT" "$T/repo" "${C:0:12}" 2> /dev/null
[ $? -eq 1 ] || fail "a short name was accepted as the commit"
mkdir "$T/plain"
"$SCRIPT" "$T/plain" "$C" 2> /dev/null
[ $? -eq 1 ] || fail "a directory that is not a clone was not refused"

echo "clean-checkout-test: restored, the ignored file kept, three refusals"
