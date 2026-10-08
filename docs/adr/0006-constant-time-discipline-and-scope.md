# 0006 Constant-time discipline and its scope

## Status

Accepted

## Date

2026-10-06 (retroactive record, written 2026-10-09; the review finding that fixed the scope predates the first commit, exact date not recorded)

## Context

The prover handles secret witnesses, so field arithmetic must not leak them through timing. SPARK proves nothing about execution time: constant-time behaviour is a coding discipline, not a contract. An independent review of the first version of the package (recorded in the header as finding P2) observed that SPARK contracts and ghost code are compiled and executed when assertions are enabled, and that `Mul_Ref` then branches on the bits of its operand at run time, so a build with assertions enabled is not constant time whatever the executable code does.

## Decision

- No secret-dependent branching or indexing in any executable statement of library code. Conditional xors are realised with arithmetic masks (`0 - bit`, all-ones or all-zeros), never with `if`. If-expressions appear only in contracts and ghost code.
- The constant-time guarantee is scoped to builds with assertions disabled (`Assertion_Policy (Ignore)`, for example the Alire release profile). The package header says in capitals never to benchmark, measure or deploy a build with assertions enabled.
- The README trust model lists constant time under "out of scope for proofs, compensated" with this scope.

## Alternatives considered

- Make the ghost reference branch-free as well. Rejected implicitly: ghost code is specification, and readability of the specification matters more than its timing; the executable code is what ships.
- Claim constant time unconditionally. Rejected by the review finding: the claim would be false for assertion-enabled builds.
- Verify constant time with a tool (for instance a dudect-style measurement or a binary-level checker). Not pursued at stage 1; it remains a possible future control and would not change the scope decision.

## Consequences

- `Xtime` and `Mul` use masks; `Inv` uses a fixed chain with no exponent bit tests ([0008](0008-inv-fixed-chain-total-function.md)).
- The test build ([0010](0010-assertion-enabled-test-project.md)) is by construction not constant time and is declared as such.
- Any future hardware kernel outside SPARK must document its own timing behaviour at the trust boundary.

## Verification impact

- Provable: nothing about timing.
- Tested: nothing about timing at stage 1.
- Trusted: the discipline itself, reviewed by reading; the compiler's preservation of branch-free code at the chosen optimisation level.
- Constant time: guaranteed only for assertion-free builds, by discipline.

## References

- `src/gf2_128.ads` header, "Constant-time discipline" and "SCOPE OF THE GUARANTEE (independent review, P2)".
- README, "Trust model", "Out of scope for proofs, compensated".
- [0003](0003-proof-policy-and-trust-model.md).
