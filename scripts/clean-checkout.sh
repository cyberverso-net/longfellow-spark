#!/bin/bash
#  Puts a git clone at a commit and nothing else, or refuses.
#
#  scripts/clean-checkout.sh DIR COMMIT
#     Checks out COMMIT in the clone DIR with every tracked file restored
#     (git checkout -f: staged and unstaged edits and deleted files are
#     undone), removes the untracked files (git clean -fd; the ignored
#     ones, build directories, stay), then checks that HEAD is COMMIT
#     and that no tracked file differs from it. Exit status 0 when the
#     clone is clean at COMMIT, 1 otherwise, with a line saying why.
#     COMMIT is a full object name, as the callers have it.
#
#  Used by remote-check.sh on the proving machine's clone before a
#  gate, and by cross-check-upstream.sh on its copy of upstream at the
#  pin, so that a result is never posted for a commit that was not
#  exactly what ran. Tested by scripts/clean-checkout-test.sh in the
#  lint step of make check.

set -uo pipefail
if [ $# -ne 2 ]; then
   echo "usage: scripts/clean-checkout.sh DIR COMMIT" >&2
   exit 2
fi
DIR="$1"
COMMIT="$2"

if ! git -C "$DIR" -c advice.detachedHead=false \
       checkout -q -f --detach "$COMMIT" 2> /dev/null
then
   echo "clean-checkout: cannot check out $COMMIT in $DIR" >&2
   exit 1
fi
if ! git -C "$DIR" clean -q -fd; then
   echo "clean-checkout: git clean failed in $DIR" >&2
   exit 1
fi
if [ "$(git -C "$DIR" rev-parse HEAD)" != "$COMMIT" ]; then
   echo "clean-checkout: $DIR is not at $COMMIT" >&2
   exit 1
fi
if ! git -C "$DIR" diff --quiet HEAD \
   || [ -n "$(git -C "$DIR" ls-files --others --exclude-standard)" ]
then
   echo "clean-checkout: $DIR differs from $COMMIT" >&2
   exit 1
fi
