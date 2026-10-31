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
#     Checks that the commit changes only text (Markdown files and
#     LICENSE) since a commit already proved: the nearest ancestor whose
#     status `prove` is success, or else origin/main. Then posts `prove`
#     as passed, naming that commit, without starting the VM.
#
#  scripts/remote-check.sh --tree [make target...]
#     Copies the working tree as it is, committed or not, and runs the
#     make target (default check) there. Posts nothing: it is for a
#     result before a push. The run is detached on the VM, as in the
#     commit mode: the laptop may sleep or lose the network, the VM
#     keeps the log and powers itself off when done, and this script
#     checks once a minute, fetches the log and stops the VM.
#
#  scripts/remote-check.sh --tree-collect [run]
#     Picks up a tree run whose script did not stay to the end: the
#     latest, or the one named (tree-<date>-<time>-<pid>, printed at the
#     start of the run).
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
#  ForwardAgent=no: the developer's keys never reach the VM, which
#  fetches with its own read-only deploy key (core.sshCommand of its
#  clone names that key and no agent).
SSH_OPTS=(-i "$KEY" -o IdentitiesOnly=yes -o BatchMode=yes -o ForwardAgent=no
          -o ConnectTimeout=30 -o "ProxyCommand=$PROXY"
          -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null
          -o LogLevel=ERROR)
#  The same options as one string, for rsync -e, which honours quotes.
SSH_STRING="ssh -i '$KEY' -o IdentitiesOnly=yes -o BatchMode=yes -o ForwardAgent=no -o 'ProxyCommand=$PROXY' -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR"

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

#  The shell test, run on the VM, that a run of either mode holds it:
#  a tree run reserved the VM in the last 30 minutes and has not started
#  yet (~/runs/tree.reserved, made while its tree is copied); or
#  ~/runs/current is set, by a run that is starting (written in the last
#  30 minutes) or whose make is alive (make check for a commit, the
#  process in ~/runs/tree.pid for a tree run, on the same boot). Each
#  run removes ~/runs/current when it ends; one left by a lost run
#  expires.
BUSY='{ [ -n "$(find ~/runs -maxdepth 1 -name tree.reserved -mmin -30 2> /dev/null)" ] || { [ -e ~/runs/current ] && { [ -n "$(find ~/runs -maxdepth 1 -name current -mmin -30 2> /dev/null)" ] || pgrep -f "[m]ake check" > /dev/null || { [ -e ~/runs/tree.pid ] && read -r p b < ~/runs/tree.pid && [ "$b" = "$(cat /proc/sys/kernel/random/boot_id)" ] && kill -0 "$p" 2> /dev/null; }; }; }; }'

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
               remote "if [ \"\$(cat ~/runs/current 2> /dev/null)\" = $SHA ]; then rm -f ~/runs/current; fi" 2> /dev/null || true
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
   --tree-collect) MODE=tree-collect; shift ;;
   "")          ;;
   *)           echo "usage: scripts/remote-check.sh [--text-only | --collect [commit] | --tree [target...] | --tree-collect [run]]" >&2
                exit 2 ;;
esac

if [ "$MODE" != text ]; then
   need_user
fi

#  The nearest ancestor of $SHA, at most 50 first-parent steps back,
#  whose status `prove` is success; empty if none.
proved_ancestor() {
   local c
   for c in $(git rev-list --first-parent --max-count=50 "$SHA^" 2> /dev/null); do
      if [ "$(gh api "repos/$(repo)/commits/$c/statuses" \
                --jq "[.[] | select(.context == \"$CONTEXT\")][0].state" 2> /dev/null)" = success ]; then
         echo "$c"
         return 0
      fi
   done
}

if [ "$MODE" = text ]; then
   commit_preconditions
   git fetch -q origin main
   BASE="$(proved_ancestor)"
   if [ -n "$BASE" ]; then
      RANGE="$BASE..$SHA"; FROM="${BASE:0:7}, proved"
   else
      RANGE="origin/main...$SHA"; FROM="main"
   fi
   others="$(git diff --name-only "$RANGE" | grep -v -E '(\.md$|^LICENSE$)' || true)"
   if [ -n "$others" ]; then
      echo "remote-check: files that are not text changed since $FROM:" >&2
      echo "$others" >&2
      exit 1
   fi
   post_status success "Text only since $FROM: Markdown files and LICENSE, proof not run"
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
      if $BUSY; then echo busy \$(cat ~/runs/current); exit 0; fi
      if [ -e ~/runs/off.pid ]; then kill \$(cat ~/runs/off.pid) 2> /dev/null; rm -f ~/runs/off.pid; fi
      echo $SHA > ~/runs/current
      rm -f ~/runs/$SHA.done ~/runs/$SHA.log
      cd ~/longfellow-spark && git fetch -q origin && git checkout -q --detach $SHA && git clean -q -fd || { rm -f ~/runs/current; echo fetch-failed; exit 0; }
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

#  Every tree run has its own identifier, $RUN: its log, result and
#  targets are ~/runs/$RUN.log, .done and .targets on the VM, so that a
#  collector reads its own run and no later one. ~/runs/tree.last names
#  the latest run for --tree-collect.

#  The log of the tree run, with retries; false if it cannot be read.
fetch_tree_log() {
   local i
   for i in 1 2 3 4 5; do
      remote "cat ~/runs/$RUN.log" > remote-check.log 2> /dev/null && return 0
      sleep 20
   done
   echo "remote-check: could not read the log of $RUN from $VM" >&2
   return 1
}

#  Stop the VM unless another run holds it: collecting an old result
#  must not stop someone else's run.
stop_if_idle() {
   local held
   held="$(remote "if $BUSY; then echo busy; fi" 2> /dev/null || echo unreachable)"
   if [ -z "$held" ]; then
      vm_stop
   else
      echo "remote-check: $VM is ${held}; not stopped"
   fi
}

#  Wait for the detached tree run $RUN, fetch its log and report. Every
#  failure to reach the VM is retried, as in collect.
collect_tree() {
   echo "remote-check: waiting for the tree run $RUN (checked every $POLL s)"
   local state result logged targets
   while true; do
      state="$(vm_status)"
      if [ "$state" = "TERMINATED" ]; then
         vm_start
      fi
      if [ "$state" = "RUNNING" ] || [ "$state" = "TERMINATED" ]; then
         result="$(remote "if [ -e ~/runs/$RUN.done ]; then cat ~/runs/$RUN.done;
                           elif [ \"\$(cat ~/runs/current 2> /dev/null)\" = $RUN ] && read -r p b < ~/runs/tree.pid && [ \"\$b\" = \"\$(cat /proc/sys/kernel/random/boot_id)\" ] && kill -0 \$p 2> /dev/null; then echo running;
                           elif [ -n \"\$(find ~/runs/tree.reserved -maxdepth 1 -name $RUN -mmin -30 2> /dev/null)\" ]; then echo running;
                           elif [ -e ~/runs/$RUN.done ]; then cat ~/runs/$RUN.done;
                           else echo lost; fi" 2> /dev/null || echo unreachable)"
         case "$result" in
            running|unreachable) ;;
            lost)
               fetch_tree_log || true
               #  Its own markers only: another run's stay.
               remote "if [ \"\$(cat ~/runs/current 2> /dev/null)\" = $RUN ]; then rm -f ~/runs/current ~/runs/tree.pid; fi
                       if [ -e ~/runs/tree.reserved/$RUN ]; then rm -rf ~/runs/tree.reserved; fi" 2> /dev/null || true
               stop_if_idle
               echo "remote-check: the tree run $RUN was lost on $VM (remote-check.log)" >&2
               exit 1 ;;
            [0-9]*\ [0-9]*)
               logged=yes
               fetch_tree_log || logged=no
               targets="$(remote "cat ~/runs/$RUN.targets 2> /dev/null" || true)"
               stop_if_idle
               if [ "$logged" = no ]; then
                  echo "remote-check: make $targets ended with status ${result%% *}, log not read" >&2
                  exit 1
               fi
               if [ "${result%% *}" = 0 ]; then
                  echo "remote-check: make $targets passed in ${result##* } min (remote-check.log)"
                  exit 0
               fi
               echo "remote-check: make $targets FAILED after ${result##* } min (remote-check.log)" >&2
               exit 1 ;;
            *) ;;
         esac
      fi
      sleep "$POLL"
   done
}

if [ "$MODE" = tree-collect ]; then
   vm_start
   RUN="${1:-$(remote 'cat ~/runs/tree.last 2> /dev/null' || true)}"
   if [ -z "$RUN" ]; then
      echo "remote-check: no tree run to collect on $VM" >&2
      stop_if_idle
      exit 1
   fi
   collect_tree
fi

#  --tree: the working tree copied, make detached, posts nothing.
RUN="tree-$(date +%Y%m%d-%H%M%S)-$$"
vm_start
remote "mkdir -p ~/remote-check ~/runs"
#  Reserve the VM before the copy: mkdir is atomic, and the reservation
#  counts as busy for both modes until the run starts. A pending
#  poweroff of an earlier run is cancelled here, before the copy, and
#  markers left by a lost run (BUSY is false, so they are stale) go.
reserved="$(remote "if $BUSY; then echo busy \$(cat ~/runs/current 2> /dev/null); exit 0; fi
   find ~/runs -maxdepth 1 -name tree.reserved -mmin +30 -exec rm -rf {} +
   if mkdir ~/runs/tree.reserved 2> /dev/null; then
      touch ~/runs/tree.reserved/$RUN
      rm -f ~/runs/current ~/runs/tree.pid
      if [ -e ~/runs/off.pid ]; then kill \$(cat ~/runs/off.pid) 2> /dev/null; rm -f ~/runs/off.pid; fi
      echo reserved
   else echo busy; fi" 2> /dev/null || echo unreachable)"
case "$reserved" in
   reserved|busy*) ;;
   *) reserved=unreachable ;;
esac
if [ "$reserved" = unreachable ]; then
   #  The reservation may have been made: release it if it is this
   #  run's, and stop the VM if nothing else holds it.
   remote "if [ -e ~/runs/tree.reserved/$RUN ]; then rm -rf ~/runs/tree.reserved; fi" 2> /dev/null || true
   stop_if_idle
   echo "remote-check: no answer from $VM while reserving it; if it is still running, stop it with gcloud compute instances stop $VM" >&2
   exit 1
fi
if [ "$reserved" != reserved ]; then
   echo "remote-check: $VM is not free (${reserved}); wait for it" >&2
   exit 2
fi
#  Until the run starts, any exit releases the reservation and stops
#  the VM if nothing else holds it.
trap 'remote "if [ -e ~/runs/tree.reserved/$RUN ]; then rm -rf ~/runs/tree.reserved; fi" 2> /dev/null || true; stop_if_idle' EXIT
echo "remote-check: copying the working tree"
rsync -az --delete --exclude .git --exclude remote-check.log \
   --filter=':- .gitignore' -e "$SSH_STRING" ./ "$USER_NAME@$VM:remote-check/"
TARGETS="${*:-check}"
echo "remote-check: make $TARGETS on $VM, detached, as $RUN"
if [ -n "${REMOTE_CHECK_KEEP:-}" ]; then OFF=true; else OFF='echo $$ > ~/runs/off.pid; sleep 300 && sudo poweroff'; fi
#  The targets travel on stdin, so that their quoting reaches the VM's
#  shell as typed; the worker evaluates them as the attached mode did.
printf '%s\n' "$TARGETS" | remote "cat > ~/runs/$RUN.targets"
#  The reservation must still be this run's and unexpired, and no run of
#  the other mode may have started meanwhile.
launched="$(remote "{ [ -n \"\$(find ~/runs/tree.reserved -maxdepth 1 -name $RUN -mmin -30 2> /dev/null)\" ] && [ ! -e ~/runs/current ]; } || { echo reservation-lost; exit 0; }
   echo $RUN > ~/runs/current
   echo $RUN > ~/runs/tree.last
   cd ~/remote-check
   nohup setsid bash -c 'echo \$\$ \$(cat /proc/sys/kernel/random/boot_id) > ~/runs/tree.pid; rm -rf ~/runs/tree.reserved; start=\$(date +%s); (time eval \"make \$(cat ~/runs/$RUN.targets)\") > ~/runs/$RUN.log 2>&1; code=\$?; echo \"exit \$code\" >> ~/runs/$RUN.log; echo \"\$code \$(( (\$(date +%s) - start + 59) / 60 ))\" > ~/runs/$RUN.done; rm -f ~/runs/current ~/runs/tree.pid; $OFF' > /dev/null 2>&1 < /dev/null &
   echo started" 2> /dev/null || echo unreachable)"
case "$launched" in
   started)
      trap - EXIT ;;
   *started*|unreachable)
      #  The answer was lost, not necessarily the run: read the state.
      trap - EXIT
      echo "remote-check: no answer from the launch; reading the state of $VM" >&2 ;;
   *)
      echo "remote-check: could not start the tree run on $VM: ${launched:-no answer}" >&2
      remote "if [ -e ~/runs/tree.reserved/$RUN ]; then rm -rf ~/runs/tree.reserved; fi" 2> /dev/null || true
      trap - EXIT
      stop_if_idle
      exit 1 ;;
esac
collect_tree
