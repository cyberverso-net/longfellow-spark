#!/bin/bash
#  make check on the project's proving machine (ADR 0060): starts the
#  Google Cloud VM prove-runner, copies the working tree there with
#  rsync through an IAP tunnel (no git push: the files travel, not the
#  repository), runs make check, brings the log back and stops the VM.
#  The proof that gates a commit (ADR 0041) is then run on the same
#  machine as the hosted check, and the developer's machine stays free.
#
#  Usage: scripts/remote-check.sh [make target, default check]
#  Needs gcloud authenticated on the developer's account (OS Login), the
#  key gcloud compute ssh created (~/.ssh/google_compute_engine) and
#  rsync. The log is written to remote-check.log in the working tree.
set -eu
cd "$(dirname "$0")/.."
PROJECT=longfellow-512114
ZONE=europe-west4-c
VM=prove-runner
TARGET="${1:-check}"
USER_NAME="$(gcloud compute os-login describe-profile --project "$PROJECT" \
               --format='value(posixAccounts[0].username)')"
SSH="ssh -i $HOME/.ssh/google_compute_engine -o IdentitiesOnly=yes -o BatchMode=yes -o ProxyCommand='gcloud compute start-iap-tunnel $VM 22 --listen-on-stdin --zone $ZONE --project $PROJECT --quiet' -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR"

status="$(gcloud compute instances describe "$VM" --zone "$ZONE" --project "$PROJECT" --format='value(status)')"
if [ "$status" != "RUNNING" ]; then
   echo "remote-check: starting $VM ($status)"
   gcloud compute instances start "$VM" --zone "$ZONE" --project "$PROJECT" --quiet
   sleep 30
fi
#  While we work, a GitHub job finishing on the same VM must not shut it down.
eval "$SSH" "$USER_NAME@$VM" "touch /tmp/keep-running; mkdir -p ~/remote-check"
echo "remote-check: copying the working tree"
eval rsync -az --delete --exclude .git --exclude obj --exclude lib --exclude bin \
   --exclude tests/obj --exclude tests/bin --exclude cli/obj --exclude cli/bin \
   --exclude cli/out --exclude remote-check.log -e "\"$SSH\"" ./ "$USER_NAME@$VM:~/remote-check/"
echo "remote-check: make $TARGET on $VM"
set +e
eval "$SSH" "$USER_NAME@$VM" "cd ~/remote-check && (time make $TARGET) > ~/remote-check.log 2>&1; echo \"exit \$?\" >> ~/remote-check.log; tail -3 ~/remote-check.log"
eval "$SSH" "$USER_NAME@$VM" "cat ~/remote-check.log" > remote-check.log
eval "$SSH" "$USER_NAME@$VM" "rm -f /tmp/keep-running"
set -e
if [ "${REMOTE_CHECK_KEEP:-}" = "" ]; then
   echo "remote-check: stopping $VM"
   gcloud compute instances stop "$VM" --zone "$ZONE" --project "$PROJECT" --quiet > /dev/null
fi
grep -q "^exit 0" remote-check.log && echo "remote-check: make $TARGET passed (remote-check.log)" || { echo "remote-check: make $TARGET FAILED (remote-check.log)" >&2; exit 1; }
