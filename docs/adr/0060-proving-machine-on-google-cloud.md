# 0060 A proving machine on Google Cloud: prove as one job, make check remote

## Status

Accepted (2026-10-19)

## Date

2026-10-19

## Context

The hosted runners of GitHub Actions have four cores. At the close of Phase C the proof no longer fits them: the prover units as one partition exceeded first the forty-five minute job limit and then the sixty minute one ([ADR 0054](0054-prove-job-limit-sixty-minutes.md)), the `verifier` partition took forty-nine minutes, and the project was heading for ten partitions and more with Phase D. Each job also pays five to six minutes of toolchain installation. On the author's laptop (ten cores) the whole proof inside `make check` takes about an hour and a quarter and saturates the machine, and the prover timeouts of [ADR 0020](0020-prover-configuration-step-budget.md) make the proof sensitive to contention: a check run while another compilation ran failed on one assertion that passes on an idle machine (block 6 of Phase C).

The larger hosted runners of GitHub need a Team or Enterprise plan and bill from the first minute; a machine of the project's own on Google Cloud, started for a job and stopped after it, costs a fraction and serves the measurements of Phase D as well.

## Decision

- **The proving machine.** A Compute Engine virtual machine `prove-runner` in project `longfellow-512114`, zone `europe-west4-c`, type `c4-standard-24` (24 vCPU Intel Emerald Rapids, 90 GB; the family nearest to the author's laptop per thread among those available, the C4 quota of the project allowing 24 vCPU at the date of this record, 32 once raised), Ubuntu 24.04 LTS, a 100 GB Hyperdisk Balanced, Shielded VM, OS Login, no public address: outbound traffic through Cloud NAT, inbound ssh only through Identity-Aware Proxy (firewall rule `allow-ssh-iap` from `35.235.240.0/20` on the tag `prove-runner`). The toolchain is installed once (Alire 2.1.1, `gnat_native 16.1.0`, `gprbuild 26.0.1`, `gnatprove 16.1.0` as the crate's dependency), the repository is cloned with a read-only deploy key.
- **The runner.** The GitHub Actions self-hosted runner (`actions/runner`) registered to the repository with the labels `prove` and `gcp`, as a systemd service, not ephemeral: the registration survives the VM being stopped, and the job-completed hook (`ACTIONS_RUNNER_HOOK_JOB_COMPLETED`) shuts the VM down a minute after every job unless `/tmp/keep-running` exists, which `scripts/remote-check.sh` creates while it works. GitHub removes a self-hosted runner that has not connected for fourteen days; the weekly schedule keeps it alive.
- **The `prove` workflow** has two jobs: `start-runner`, on a hosted runner, authenticates to Google Cloud through Workload Identity Federation (pool `github`, provider `github-oidc`, attribute condition on the repository, service account `gh-runner-starter` with `compute.instanceAdmin.v1` on the one instance; no key in the repository, two secrets naming the provider and the service account) and starts the VM if it is not running; `prove` runs on the self-hosted runner: build, the partition coverage check, `make prove` in one job with one prover per core, the report uploaded; limit ninety minutes. One required check, `prove`, replaces the nine of ADR 0054 in branch protection. The partitions of `scripts/prove-partitions.txt` remain for `make prove-partition` locally and for the coverage check.
- **`make check` remote.** `scripts/remote-check.sh` starts the VM, copies the working tree with rsync through an IAP tunnel (no git push: the files travel, not the repository, so the rule of no push before the author's own holds), runs `make check` there, brings the log back as `remote-check.log` and stops the VM. The definition of done of [ADR 0041](0041-verification-cadence.md), `make check` by the developer before every commit, stands; the machine it runs on may be this one.
- **Cost.** About 1.35 dollars an hour while running, a few cents a month for the stopped disk and the NAT; a proof of about twenty to thirty minutes per run, hence under a dollar per pull request or remote check.
- **Reference machine for Phase D.** The performance targets of [ADR 0055](0055-phase-d-scope-mdoc-scale.md) stay stated as factors over the baseline on the named machine; if the author moves the measurements to this VM, the baseline is measured again there and the absolute numbers derived with the same factors, as that record says.

## Alternatives considered

- **Larger hosted runners.** 16 or 32 cores at 0.064 or 0.128 dollars a minute, a Team plan, and the same cost per core-minute: three to four dollars per run against under one, and no machine for measurements.
- **Raising the limit or splitting further.** The route of ADR 0054, exhausted: the limit was exceeded twice and every partition costs a job and a required check.
- **An ephemeral runner registered at boot.** Cleaner, but it needs a registration token at every boot, hence a GitHub token stored on the machine or in Secret Manager; the non-ephemeral runner with the shutdown hook needs no stored credential.
- **A public address on the VM.** Not needed: the runner and the proofs talk outwards; IAP gives ssh without exposing a port.

## Consequences

- The `prove` workflow, `scripts/remote-check.sh`, this record; ADR 0041 and ADR 0054 amended in their Status lines; the README's continuous integration section.
- Branch protection: `verify` and `prove` required (two checks), to be set by the author.
- Pull request 19 (the partition split) is superseded by this record: the split stays useful locally and is kept, the nine required checks are not.
- Trusted: Google Cloud as the operator of the machine, as GitHub was for the hosted runners; the same pinned toolchain as the hosted check and the laptop.

## Verification impact

Nothing changes in what is proved, tested or trusted about the code. What changes is where the hosted proof runs, in how many jobs, and that the developer's check can run there too.

## References

- `.github/workflows/prove.yml`, `scripts/remote-check.sh`; the runner's hook `~/actions-runner/hooks/job-completed.sh` on the machine.
- Google Cloud: Compute Engine, Identity-Aware Proxy TCP forwarding, Workload Identity Federation with GitHub Actions (`google-github-actions/auth`).
- [ADR 0019](0019-proof-off-the-hosted-gate.md), [ADR 0020](0020-prover-configuration-step-budget.md), [ADR 0021](0021-proof-on-pull-requests.md), [ADR 0033](0033-parallel-proof-partitions.md), [ADR 0041](0041-verification-cadence.md), [ADR 0045](0045-proof-gate-restored-through-partitions.md), [ADR 0054](0054-prove-job-limit-sixty-minutes.md).
