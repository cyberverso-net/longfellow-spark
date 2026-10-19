#!/bin/bash
#  The proof on demand on the project's proving machine (ADR 0060, 0062).
#
#  scripts/remote-check.sh
#     Runs make check on the Google Cloud VM prove-runner for the commit
#     checked out here, and posts the result on that commit as the
#     status `prove`, which branch protection requires. The working tree
#     must be clean and the commit pushed: the VM fetches it from GitHub
#     into its own clone, so what is checked is exactly that commit.
#
#  scripts/remote-check.sh --text-only
#     Checks that the branch changes only text against origin/main
#     (Markdown files and LICENSE) and posts `prove` as passed without
#     starting the VM.
#
#  scripts/remote-check.sh --tree [make target...]
#     Copies the working tree as it is, committed or not, and runs the
#     make target (default check) there. Posts nothing: it is for a
#     result before a push, for example while working on a hard proof.
#
#  The VM is started if it is stopped, and stopped at the end unless
#  REMOTE_CHECK_KEEP is set. The log is written to remote-check.log here.
#  Needs gcloud authenticated on the developer's account (OS Login), the
#  key that gcloud compute ssh created (~/.ssh/google_compute_engine),
#  rsync, and gh authenticated with the right to post commit statuses.
set -eu
cd "$(dirname "$0")/.."
PROJECT=longfellow-512114
ZONE=europe-west4-c
VM=prove-runner
CONTEXT=prove

PROXY="gcloud compute start-iap-tunnel $VM 22 --listen-on-stdin --zone $ZONE --project $PROJECT --quiet"
KEY="$HOME/.ssh/google_compute_engine"
SSH_OPTS=(-i "$KEY" -o IdentitiesOnly=yes -o BatchMode=yes
          -o "ProxyCommand=$PROXY" -o StrictHostKeyChecking=no
          -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR)
#  The same options as one string, for rsync -e, which honours quotes.
SSH_STRING="ssh -i '$KEY' -o IdentitiesOnly=yes -o BatchMode=yes -o 'ProxyCommand=$PROXY' -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR"

repo() { gh repo view --json nameWithOwner --jq .nameWithOwner; }

post_status() {  # state, description (at most 140 characters)
   gh api --silent -X POST "repos/$(repo)/statuses/$SHA" \
      -f state="$1" -f context="$CONTEXT" -f description="$2"
   echo "remote-check: status $CONTEXT = $1 on ${SHA:0:12}: $2"
}

#  The commit modes need a clean tree whose HEAD is on GitHub.
commit_preconditions() {
   if [ -n "$(git status --porcelain)" ]; then
      echo "remote-check: the working tree has changes; commit them, or use --tree" >&2
      exit 2
   fi
   SHA="$(git rev-parse HEAD)"
   if ! gh api --silent "repos/$(repo)/commits/$SHA" 2> /dev/null; then
      echo "remote-check: ${SHA:0:12} is not on GitHub; push it first" >&2
      exit 2
   fi
}

MODE=commit
if [ "${1:-}" = "--text-only" ]; then
   MODE=text
elif [ "${1:-}" = "--tree" ]; then
   MODE=tree
   shift
fi

if [ "$MODE" = text ]; then
   commit_preconditions
   git fetch -q origin main
   others="$(git diff --name-only "origin/main...$SHA" | grep -v -E '(\.md$|^LICENSE$)' || true)"
   if [ -n "$others" ]; then
      echo "remote-check: the branch changes files that are not text:" >&2
      echo "$others" >&2
      exit 1
   fi
   post_status success "Text only: Markdown files and LICENSE, proof not run"
   exit 0
fi

if [ "$MODE" = commit ]; then
   commit_preconditions
fi

USER_NAME="$(gcloud compute os-login describe-profile --project "$PROJECT" \
               --format='value(posixAccounts[0].username)')"
remote() { ssh "${SSH_OPTS[@]}" "$USER_NAME@$VM" "$1"; }

status="$(gcloud compute instances describe "$VM" --zone "$ZONE" --project "$PROJECT" --format='value(status)')"
if [ "$status" != "RUNNING" ]; then
   echo "remote-check: starting $VM ($status)"
   gcloud compute instances start "$VM" --zone "$ZONE" --project "$PROJECT" --quiet
   sleep 30
fi

if [ "$MODE" = commit ]; then
   post_status pending "make check running on $VM"
   #  Whatever stops the script from here on, the status must not stay
   #  pending.
   trap 'post_status error "remote-check stopped before the end"' EXIT
   #  The VM's own clone, at exactly this commit. Untracked files go;
   #  ignored ones (the toolchain state of alire/, the build) stay.
   DIR='~/longfellow-spark'
   remote "cd $DIR && git fetch -q origin && git checkout -q --detach $SHA && git clean -q -fd"
   TARGETS=check
else
   #  What .gitignore ignores stays out (alire/ and config/ of this
   #  machine name its own toolchain) and survives on the VM.
   DIR='~/remote-check'
   remote "mkdir -p $DIR"
   echo "remote-check: copying the working tree"
   rsync -az --delete --exclude .git --exclude remote-check.log \
      --filter=':- .gitignore' -e "$SSH_STRING" ./ "$USER_NAME@$VM:remote-check/"
   TARGETS="${*:-check}"
fi

echo "remote-check: make $TARGETS on $VM"
START=$(date +%s)
set +e
remote "cd $DIR && (time make $TARGETS) > ~/remote-check.log 2>&1; echo \"exit \$?\" >> ~/remote-check.log; tail -3 ~/remote-check.log"
remote 'cat ~/remote-check.log' > remote-check.log
set -e
MINUTES=$(( ($(date +%s) - START + 59) / 60 ))

if [ -z "${REMOTE_CHECK_KEEP:-}" ]; then
   echo "remote-check: stopping $VM"
   gcloud compute instances stop "$VM" --zone "$ZONE" --project "$PROJECT" --quiet > /dev/null
fi

trap - EXIT
if grep -q "^exit 0" remote-check.log; then
   if [ "$MODE" = commit ]; then
      post_status success "make check passed on $VM in $MINUTES min"
   fi
   echo "remote-check: make $TARGETS passed (remote-check.log)"
else
   step="$(grep '^=== ' remote-check.log | tail -1 | sed 's/^=== \([a-z-]*\).*/\1/')"
   if [ "$MODE" = commit ]; then
      post_status failure "make check failed in step ${step:-unknown} on $VM after $MINUTES min"
   fi
   echo "remote-check: make $TARGETS FAILED (remote-check.log)" >&2
   exit 1
fi
