# 0015 P-256 base field: canonical form and constant-time conditional subtraction

## Status

Accepted (2026-10-09, after review)

## Date

2026-10-09

## Context

With a direct representation ([0013](0013-p256-reduction-strategy.md)) every element should be stored as its unique integer in 0 .. p - 1. Then equality is limb equality, serialisation is a copy, and `From_Bytes` can reject non-canonical input as the Rust reference does (`from_bytes` returns an error for values >= p). The invariant has to be stated somewhere SPARK can use it at every call site, and the last step of every reduction, "subtract p if the value is at least p", must be branch-free.

## Decision

- An executable, branch-free Boolean function `Is_Canonical (L)` compares the limbs with the limbs of p from the most significant down, computed with masks (no early exit), and the element type carries `Dynamic_Predicate => Is_Canonical (Element.Limbs)`. A ghost lemma proves `Is_Canonical (L) = (To_Int (L) < P)`, so contracts can speak in values while the predicate stays cheap and executable.
- Every operation takes and returns the predicated type, so canonical form is checked by GNATprove at every call and return, with no preconditions to write by hand.
- Conditional subtraction: compute `D = E - P` with borrow propagation across the four limbs; the final borrow (0 or 1) says whether `E < P`; a mask `0 - (1 - Borrow)` selects `D` when `E >= P` and `E` otherwise, limb by limb, as in the stage 1 selectors. Its contract: result canonical and equal to `E mod P` given `E < 2 P`.
- `From_Bytes (B) return (Ok : Boolean; E : Element)` (or an out parameter plus a Boolean) with `Ok = (value of B < P)`; on failure the element is Zero. This is public data (serialised proofs), so the caller may branch on `Ok`.

## Alternatives considered

- **Predicate expressed directly as `To_Int (L) < P`.** Simpler to state, but it would execute `Big_Integer` arithmetic on every assignment in assertion-enabled builds and it would reference ghost code from a predicate, which is allowed in assertion expressions but ties the executable type to the ghost model. Rejected in favour of the executable predicate plus a lemma.
- **Postconditions only, no predicate** (every operation promises a canonical result and requires canonical inputs). Equivalent in proof strength but every subprogram repeats the precondition and postcondition, and a forgotten precondition weakens a caller silently. Rejected.
- **Non-canonical storage with normalisation on serialisation and comparison** (as unsaturated representations require). Rejected with [0012](0012-p256-limb-representation.md).

## Consequences

- Constructing an `Element` from raw limbs is only possible through `From_Bytes` or a reduction, both of which prove the predicate.
- The predicate executes on every assignment in the test build; it is four limb comparisons, negligible next to the ghost `Big_Integer` postconditions.
- Constants (Zero, One, Two, the inverse of two for the sumcheck layer) are declared with their limbs and the predicate is proved on them statically.

## Verification impact

- Provable: canonical form everywhere, by the predicate; the conditional subtraction equals `mod P` on its input range.
- Tested: `From_Bytes` acceptance boundary (p - 1 accepted, p and p + 1 rejected, all-ones rejected) and round trips.
- Trusted: nothing new.
- Constant time: comparison and selection by masks; `From_Bytes` may branch on its Boolean result because the input is public.

## References

- draft-google-cfrg-libzk-03, Section 7.2.1 (canonical little-endian encoding), Section 3.4.3 (sampling by rejection of values >= p, which presumes the same canonical range).
- google/longfellow-zk at d5e6be7, `docs/specs/rust/src/algebra/p256.rs` (`from_bytes`, `ValueOutOfRange`).
- SPARKNaCl `Subtract_P` and `CSwap` (constant-time selection by mask), AdaCore blog "Proving constant-time crypto code in SPARKNaCl", read 2026-10-09.
