## Summary

<!-- What this change does and why. The record it realises, if any. -->

Closes #

## Proof

<!-- The partitions proved on the proving machine and their check counts. Unproved checks in new code, with diagnosis and fix. "No contract changes" or the agreement the change rests on. -->

## Measurements

<!-- Proving machine, one session, median of three runs, before and after, upstream in the same session. "None" if no time or memory change. The proofs of the command line unchanged byte for byte, where expected. -->

## Definition of Done

- [ ] Every acceptance criterion of the issue is met
- [ ] `verify` and `prove` are green
- [ ] Every check in the touched units is proved; no justification, no `pragma Assume`
- [ ] No contract weakened and no assurance level changed, or the maintainer's agreement is recorded
- [ ] Chapter, records, package headers, trust model and changelog updated and consistent with the code
- [ ] Reviewed against the checklist in [docs/process.md](https://github.com/cyberverso-net/longfellow-spark/blob/main/docs/process.md)
