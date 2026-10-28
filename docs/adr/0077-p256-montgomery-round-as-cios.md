# 0077 The Montgomery round of P-256 as upstream's CIOS step

## Status

Proposed (2026-10-28, milestone M2 of Phase D).

## Date

2026-10-28

## Context

After ADR 0076 the P-256 field was still about three times slower than upstream's generic code, with the same algorithm. On the proving machine, in ns per operation: our product 32.7 against 11.4, our sum 10.8 against 2.0 (experiments of 27 October).

The disassembly gives two causes, both in how GCC compiles our forms:

- **The rounds of `Mont_Mul`.** Each round made a five-word row (`Mul_Row`), then three carry chains over six words: add the row, add V (r), subtract U (r), where V (r) - U (r) = r p by shifted copies of r. With the copies between them, `Mont_Mul` held 88 moves and 44 memory operands.
- **The carries.** `Add_Words` and `Sub_Words` compute each word as one 128-bit sum or difference of three terms. GCC turns that into two add-and-carry pairs per word. LLVM gives upstream one chain of `adc`.

An unproved prototype gave a product of 18.7 ns and a sum of 5.5 ns, with the same words on 4096 pairs. It used upstream's CIOS step for the product, and for the carries the idiom GCC 14 and later recognise as an add with carry.

## Decision

**`Round` is upstream's CIOS step. The contracts do not change.**

- `Mac_Row` makes T + X B on six words, in place:
  - four 128-bit multiply-accumulates, t_j + x b_j + c, which never wrap;
  - then the carry added to the two words above.
- `Round` calls `Mac_Row` twice: with X and B, then with r, the low word, and the four limbs of p. Since p = -1 mod 2^64, r is the multiplier that clears the low word.
- The rest of the proof of `Round` is unchanged: r p clears the low word, and the value goes one word down.
- The body of `Mac_Row` holds no `Big_Integer` term (ADR 0076): the identities are in `Lemma_Mac`, `Lemma_Mac_Step`, `Lemma_Two` and `Lemma_Mac_Close`.
- **Removed:** `Mul_Row`, `Wide_Mul`, `V_Of`, `U_Of`, `Ext6` and their lemmas, which only the old round used.
- **`Add_Words` and `Sub_Words` keep their 128-bit forms.** The carry idiom was tried and proved (`Lemma_Addc` and `Lemma_Subb` tied it to the 128-bit sum, kept as ghost). In the loop form of these procedures it made `Add` and `Sub` about 1 ns slower, so it was taken out again.
- **Constant time** (ADR 0006): the disassembly of `Add`, `Sub`, `Mul` and `Mont_Mul` on the proving machine has no jumps.

## Alternatives considered

- **Keep the old round.** Rejected: the cost was the form, not the work.
- **The carry idiom in `Add_Words` and `Sub_Words`.** Tried and taken out, as above. The prototype's sum, written without the generic loop, stays twice as fast as ours: a candidate for later, with the form that gives it.
- **Intrinsics for add with carry** (`__builtin_addcll`, `_addcarry_u64`). Rejected: an imported intrinsic has no body, so its contract would be trusted.
- **r p from shifted copies of r**, as before. Not taken: the generic step with the four limbs of p is what upstream's generic code does, and it is the faster form here.

## Consequences

- The P-256 operations on the proving machine, ns per operation, in one session: the product 29.4 instead of 34.4 (latency) and 19.9 instead of 29.4 (throughput); the sum and the difference unchanged.
- Measured on the proving machine (c4-standard-24), proved build, mdoc v7, median of three runs in one session, ce0f755 against af1ac70:

  | | before | after | change |
  |---|---|---|---|
  | hash prove | 5.14 s | 5.14 s | 0 |
  | hash verify | 2.66 s | 2.68 s | 0 |
  | sig prove | 0.57 s | 0.50 s | -0.07 s (-12 %) |
  | sig verify | 0.36 s | 0.30 s | -0.06 s (-17 %) |

  That session ran about 8 % slower than the series of ADR 0076 for the same commits, so only the change within the session is reported.
- The proofs of the command line stay identical byte for byte.
- Guide chapter 2 describes the new round.

## Verification impact

- The contracts of `Round`, `Mont_Mul` and of every subprogram of the specification are unchanged.
- New lemmas: `Lemma_Mac`, `Lemma_Mac_Step`, `Lemma_Two`, `Lemma_Mac_Close`. The P-256 partition: 3078 checks, all proved.
- No `pragma Assume`.

## References

- [ADR 0006](0006-constant-time-discipline-and-scope.md), [ADR 0069](0069-p256-montgomery-multiplication.md), [ADR 0076](0076-field-operations-without-call-and-finalisation-overhead.md).
- google/longfellow-zk at d5e6be7: `rust/runtime/algebra/src/fp_generic.rs` (`montgomery_mul`), `runtime/algebra/benches/p256_benchmark.rs`.
- The notes of 27 and 28 October: `experiments/2026-10-27-p256-speed`, `measure-2026-10-28-p256-cios2`.
