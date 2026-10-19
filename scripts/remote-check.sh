#!/bin/bash
#  The proof on demand on the project's proving machine (ADR 0060, 0062).
#
#  scripts/remote-check.sh
#     Runs make check on the Google Cloud VM prove-runner for the commit
#     checked out here, and posts the result on that commit as the
#     status `prove`, which branch protection requires. The working tree
#     must be clean and the commit pushed: the VM fetches it from GitHub
#     into its own clone, so what is checked is exactly that commit.
#     The run is detached on the VM: the laptop may sleep or lose the
#     network. The VM keeps the log and the result on its disk and shuts
#     itself down when done. This script checks once a minute, starting
#     the VM again only to read the result if it has already stopped,
#     then posts the status and stops the VM.
#
#  scripts/remote-check.sh --collect [commit]
#     Picks up a run started earlier whose script did not stay to the
#     end (the terminal was closed), and posts its status. The commit
#     defaults to HEAD.
#
#  scripts/remote-check.sh --text-only
#     Checks that the branch changes only text against origin/main
#     (Markdown files and LICENSE) and posts `prove` as passed without
#     starting the VM.
#
#  scripts/remote-check.sh --tree [make target...]
#     Copies the working tree as it is, committed or not, and runs the
#     make target (default check) there, attached: the laptop must stay
#     awake. Posts nothing: it is for a result before a push.
#
#  One run at a time: a run started while another is in progress on the
#  VM is refused. The VM is stopped at the end unless REMOTE_CHECK_KEEP
#  is set. The log is written to remote-check.log here.
#  Needs gcloud authenticated on the developer's account (OS Login), the
#  key that gcloud compute ssh created (~/.ssh/google_compute_engine),
#  rsync, and gh authenticated with the right to post commit statuses.
#  The status is posted from this machine, with the developer's gh
#  account; the VM holds no GitHub credential beyond its read-only
#  deploy key.
set -eu
cd "$(dirname "$0")/.."
PROJECT=longfellow-512114
ZONE=europe-west4-c
VM=prove-runner
CONTEXT=prove
POLL=60

PROXY="gcloud compute start-iap-tunnel $VM 22 --listen-on-stdin --zone $ZONE --project $PROJECT --quiet"
KEY="$HOME/.ssh/google_compute_engine"
SSH_OPTS=(-i "$KEY" -o IdentitiesOnly=yes -o BatchMode=yes
          -o ConnectTimeout=30 -o "ProxyCommand=$PROXY"
          -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null
          -o LogLevel=ERROR)
#  The same options as one string, for rsync -e, which honours quotes.
SSH_STRING="ssh -i '$KEY' -o IdentitiesOnly=yes -o BatchMode=yes -o 'ProxyCommand=$PROXY' -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR"

repo() { gh repo view --json nameWithOwner --jq .nameWithOwner; }

post_status() {  # state, description (at most 140 characters)
   local i
   for i in 1 2 3 4 5; do
      if gh api --silent -X POST "repos/$(repo)/statuses/$SHA" \
            -f state="$1" -f context="$CONTEXT" -f description="$2"; then
         echo "remote-check: status $CONTEXT = $1 on ${SHA:0:12}: $2"
         return 0
      fi
      sleep 30
   done
   echo "remote-check: could not post the status $1; post it again with --collect" >&2
   return 1
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

vm_status() {
   gcloud compute instances describe "$VM" --zone "$ZONE" --project "$PROJECT" \
      --format='value(status)' 2> /dev/null || echo UNKNOWN
}

vm_start() {
   if [ "$(vm_status)" != "RUNNING" ]; then
      echo "remote-check: starting $VM"
      gcloud compute instances start "$VM" --zone "$ZONE" --project "$PROJECT" --quiet
      sleep 30
   fi
}

vm_stop() {
   if [ -z "${REMOTE_CHECK_KEEP:-}" ]; then
      echo "remote-check: stopping $VM"
      gcloud compute instances stop "$VM" --zone "$ZONE" --project "$PROJECT" --quiet > /dev/null || true
   fi
}

USER_NAME=""
need_user() {
   USER_NAME="$(gcloud compute os-login describe-profile --project "$PROJECT" \
                  --format='value(posixAccounts[0].username)')"
}
remote() { ssh "${SSH_OPTS[@]}" "$USER_NAME@$VM" "$1"; }

#  The log of the run of $SHA, with retries over a network that may come
#  and go.
fetch_log() {
   local i
   for i in 1 2 3 4 5; do
      remote "cat ~/runs/$SHA.log 2> /dev/null" > remote-check.log && return 0
      sleep 20
   done
   echo "remote-check: could not read the log from $VM" >&2
}

#  Wait for the detached run of $SHA and post its result. Every failure
#  to reach the VM (the laptop asleep, the network gone) is retried.
collect() {
   echo "remote-check: waiting for the run of ${SHA:0:12} (checked every $POLL s)"
   local state result
   while true; do
      state="$(vm_status)"
      if [ "$state" = "TERMINATED" ]; then
         #  The run ended and the VM shut itself down, or the VM was
         #  stopped under it: start it to read what is on its disk.
         vm_start
      fi
      if [ "$state" = "RUNNING" ] || [ "$state" = "TERMINATED" ]; then
         result="$(remote "if [ -e ~/runs/$SHA.done ]; then cat ~/runs/$SHA.done;
                           elif [ \"\$(cat ~/runs/current 2> /dev/null)\" = $SHA ] && pgrep -f '[m]ake check' > /dev/null; then echo running;
                           else echo lost; fi" 2> /dev/null || echo unreachable)"
         case "$result" in
            running|unreachable) ;;
            lost)
               fetch_log
               post_status error "make check of this commit was lost on $VM; run remote-check.sh again"
               vm_stop
               exit 1 ;;
            [0-9]*\ [0-9]*)
               fetch_log
               vm_stop
               local code minutes step
               code="${result%% *}"
               minutes="${result##* }"
               if [ "$code" = 0 ]; then
                  post_status success "make check passed on $VM in $minutes min"
                  echo "remote-check: make check passed (remote-check.log)"
                  exit 0
               fi
               step="$(grep '^=== ' remote-check.log | tail -1 | sed 's/^=== \([a-z-]*\).*/\1/')"
               post_status failure "make check failed in step ${step:-unknown} on $VM after $minutes min"
               echo "remote-check: make check FAILED (remote-check.log)" >&2
               exit 1 ;;
            *) ;;   # an answer cut short: ask again
         esac
      fi
      sleep "$POLL"
   done
}

MODE=commit
case "${1:-}" in
   --text-only) MODE=text ;;
   --collect)   MODE=collect; shift ;;
   --tree)      MODE=tree; shift ;;
   "")          ;;
   *)           echo "usage: scripts/remote-check.sh [--text-only | --collect [commit] | --tree [target...]]" >&2
                exit 2 ;;
esac

if [ "$MODE" != text ]; then
   need_user
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

if [ "$MODE" = collect ]; then
   SHA="$(git rev-parse "${1:-HEAD}")"
   collect
fi

if [ "$MODE" = commit ]; then
   commit_preconditions
   vm_start
   #  The run, detached from this connection: the VM's own clone at
   #  exactly this commit (untracked files go, ignored ones such as the
   #  toolchain state of alire/ and the build stay), make check, the
   #  exit code and the minutes in ~/runs/<commit>.done, then the VM
   #  powers itself off five minutes later unless REMOTE_CHECK_KEEP is
   #  set here. A plain wait then poweroff, not shutdown -h +N, which
   #  refuses ssh logins in its last minutes: the script reads the
   #  result within a minute and stops the VM itself. A run started in
   #  those five minutes first cancels the pending poweroff. The target is spelt make "chec"k so that no command line
   #  but the one of make itself matches the pattern [m]ake check.
   if [ -n "${REMOTE_CHECK_KEEP:-}" ]; then OFF=true; else OFF='echo $$ > ~/runs/off.pid; sleep 300 && sudo poweroff'; fi
   launched="$(remote "mkdir -p ~/runs
      if [ -e ~/runs/current ] && pgrep -f '[m]ake check' > /dev/null; then echo busy \$(cat ~/runs/current); exit 0; fi
      if [ -e ~/runs/off.pid ]; then kill \$(cat ~/runs/off.pid) 2> /dev/null; rm -f ~/runs/off.pid; fi
      echo $SHA > ~/runs/current
      rm -f ~/runs/$SHA.done ~/runs/$SHA.log
      cd ~/longfellow-spark && git fetch -q origin && git checkout -q --detach $SHA && git clean -q -fd || { echo fetch-failed; exit 0; }
      nohup setsid bash -c 'start=\$(date +%s); (time make \"chec\"k) > ~/runs/$SHA.log 2>&1; code=\$?; echo \"\$code \$(( (\$(date +%s) - start + 59) / 60 ))\" > ~/runs/$SHA.done; rm -f ~/runs/current; $OFF' > /dev/null 2>&1 < /dev/null &
      echo started" 2> /dev/null || echo unreachable)"
   case "$launched" in
      started)
         post_status pending "make check running on $VM" ;;
      busy*)
         echo "remote-check: $VM is already checking ${launched#busy }; wait for it, or --collect it" >&2
         exit 2 ;;
      *)
         echo "remote-check: could not start the run on $VM: ${launched:-no answer}" >&2
         vm_stop
         exit 1 ;;
   esac
   collect
fi

#  --tree: attached, posts nothing.
vm_start
remote "mkdir -p ~/remote-check"
echo "remote-check: copying the working tree"
rsync -az --delete --exclude .git --exclude remote-check.log \
   --filter=':- .gitignore' -e "$SSH_STRING" ./ "$USER_NAME@$VM:remote-check/"
TARGETS="${*:-check}"
echo "remote-check: make $TARGETS on $VM"
set +e
remote "cd ~/remote-check && (time make $TARGETS) > ~/remote-check.log 2>&1; echo \"exit \$?\" >> ~/remote-check.log; tail -3 ~/remote-check.log"
remote 'cat ~/remote-check.log' > remote-check.log
set -e
vm_stop
if grep -q "^exit 0" remote-check.log; then
   echo "remote-check: make $TARGETS passed (remote-check.log)"
else
   echo "remote-check: make $TARGETS FAILED (remote-check.log)" >&2
   exit 1
fi
