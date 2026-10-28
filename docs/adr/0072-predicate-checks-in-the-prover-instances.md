# 0072 The prover instances of the command line do not check the circuit predicate again

## Status

Proposed (2026-10-26, milestone M2 of Phase D). Amended 2026-10-28: the command-line programs check the predicate of the circuit once, explicitly, after the load, and suppress the predicate checks of their own calls and of the expression functions of `Zk_Prover`'s specification, which walked the circuit again about four times (0.18 s of the hash proof); the contracts and the proofs do not change.

## Date

2026-10-26

## Context

ADR 0068 compiles the units of `src/` without run-time checks, because GNATprove proves that none can fail. The instances of the prover made for the command line live in `cli/src/` and keep their checks. They take `Cli_Random.Fill` as the formal `Fill`, and GNATprove analyses only the instances of `src/`.

`Circuit` is a subtype of `Raw_Circuit` with the predicate `Well_Formed`. In a build with checks, GNAT checks the predicate whenever a circuit is passed to a formal of subtype `Circuit`. Each check scans every term of every layer.

ADR 0071 moved the work of a layer into `Prove_Layer`, which takes the circuit. On the mdoc hash circuit the instances for the command line then checked the predicate once per layer, 17 times per proof:

- `Well_Formed` and the predicate took 9.9 % of the hash proof on the proving machine, about 0.84 s. Before ADR 0071 they took 3.7 %.
- Every one of these checks sits inside the generic bodies of `Sumcheck_Prover` and `Zk_Prover`. GNATprove proves each of them for the instances of `src/`.
- The predicate is a property of the circuit alone. It does not depend on `Fill`, the only difference between the two kinds of instance.

## Decision

**The bodies of `Sumcheck_Prover` and `Zk_Prover` suppress the predicate checks: `pragma Suppress (Predicate_Check)`.**

- The circuit is still checked where it enters the program. `longfellow_prove`, in `cli/src/`, builds the circuit from its file and keeps every check, the predicate included. So do the functions of the specifications, such as `Max_Proof_Len` and `Config_Fits`, that the program calls.
- Every other check of the instances for the command line stays, as ADR 0068 decided.
- For the instances of `src/`, compiled without checks, nothing changes.
- GNATprove ignores the pragma. It proves the predicate checks as before.

## Alternatives considered

- **Keep the checks.** Rejected: 0.8 s of the hash proof for a property the proof already gives, checked again for each layer of a circuit already checked on entry.
- **Compile the instances for the command line without any check.** That is a change to the boundary of ADR 0068: those instances would rely on the proof of the generic for the other checks too, with a `Fill` the proof did not see. It stays a candidate for M3, with its own record.
- **Pass to `Prove_Layer` only what it needs.** The contracts of `Prove_Layer` name the circuit, through `BQ_Ref` and the offsets, and SPARK refuses a ghost formal on a procedure that is not ghost. The calls inside the layer, to `Off`, `Pad_Off` and `Chal_Off`, would check the predicate anyway.

## Consequences

- Measured on the proving machine (c4-standard-24), proved build, mdoc v7, median of three runs in one session, e504b58 against f693af3:

| | before | after | change |
|---|---|---|---|
| hash prove | 8.32 s | 7.53 s | -0.79 s (-9 %) |
| hash verify | 5.06 s | 5.06 s | 0 |
| sig prove | 0.90 s | 0.86 s | -0.04 s |
| sig verify | 0.62 s | 0.62 s | 0 |

- `Well_Formed` leaves the profile of the hash proof. The check on entry stays, at about 2 %.
- The amendment of 2026-10-28, measured the same way, 9ef47a3 against ce0f755: hash prove 4.86 s to 4.70 s, the rest unchanged, round trip 8.16 s to 7.99 s. The proofs stay identical byte for byte.
- In `Run`, the suppression covers every predicate check of the function, not only the circuit's. The others were already established elsewhere: the public inputs are checked when `To_Element` returns them, and the private inputs come from `From_Bytes`, whose postcondition is proved.
- The proofs of the CLI stay identical byte for byte.
- ADR 0068 is amended. The trust model and the CHANGELOG are updated.

## Verification impact

- None on the proof: GNATprove ignores `pragma Suppress`, and every predicate check stays proved.
- No `pragma Assume`, no weaker contract.

## References

- [ADR 0068](0068-release-build-without-run-time-checks.md), [ADR 0071](0071-prover-reuses-the-bound-quad.md).
- GNAT Reference Manual, `pragma Suppress` and the check name `Predicate_Check`.
