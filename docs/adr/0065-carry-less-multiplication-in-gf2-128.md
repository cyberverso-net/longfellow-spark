# 0065 The carry-less multiplication of upstream in GF(2^128), proved Gold

## Status

Proposed (2026-10-21, at the start of milestone M2 of Phase D)

## Date

2026-10-21

## Context

After milestone M1 ([ADR 0063](0063-milestone-m1-algorithmic-parity.md)), the multiplication in GF(2^128) takes most of the time of the mDoc hash circuit: 84% of the proof and 77% of the verification on the proving machine. Milestone M2 of [ADR 0055](0055-phase-d-scope-mdoc-scale.md) asks for a round trip of at most 5 seconds.

`GF2_128.Mul` works bit by bit: 128 steps of `Xtime` and a masked xor. It is Gold against `Mul_Ref`, the same Horner scheme as a ghost function ([ADR 0005](0005-mul-ref-as-proof-target.md)).

Upstream has three forms of the same multiplication (`rust/runtime/algebra/src/arch/`):

- `x86_64.rs` and `aarch64.rs`: the processor's carry-less multiply (PCLMULQDQ, PMULL);
- `generic.rs`: the same algorithm in software, with no special instruction.

`generic.rs` splits each operand into two 64-bit halves and makes three 64 by 64 carry-less products (Karatsuba), then reduces modulo x^128 + x^7 + x^2 + x + 1 with shifts and xors. Each 64 by 64 product, `clmul64`, uses ordinary integer multiplication on masked words: each operand keeps one bit in four, so that the carries of the integer products land in bits that the masks then clear. The high half of the product comes from the low half of the product of the bit-reversed operands.

Measured in C on the development machine, with each product waiting for the previous one:

| form | ns per product |
|------|----------------|
| bit by bit (this project) | 179 |
| `generic.rs` | 25 |
| PMULL | 10 |

A four-bit window with a constant-time table read takes 437 ns, slower than today. On 2 million random products and 20 million random 64-bit products, `generic.rs` agrees with the bit-by-bit form.

## Decision

- **The software form of upstream.** `Mul` becomes the algorithm of `generic.rs`: three products `clmul64` (Karatsuba) and the two-step reduction, on the two limbs of `Element`. No special instruction, no table, no branch on the operands.
- **Gold.** The postcondition of `Mul` stays `Mul'Result = Mul_Ref (A, B, 128)`. The proof goes through two new ghost references:
  - `Clmul_Ref`, the carry-less product of two 64-bit words: bit p of the result is the parity of the pairs (i, j) with i + j = p, x_i = 1 and y_j = 1;
  - the reduction of a 256-bit product, proved to agree with `Xtime` step by step, so that `Mul_Ref` (Horner modulo the polynomial) equals the reduction of the full product.
- **The integer product with holes, proved.** `clmul64_lo` is the kernel that needs care. The argument, written as lemmas on `Big_Integers`:
  1. A word masked to one class of bit positions is a number in base 16 whose digits are 0 or 1.
  2. The integer product of two such words has, in digit k, the sum c_k of the products x_i y_j with i + j = k, at most k + 1 terms.
  3. The low bit of c_k is the carry-less coefficient. The carries go into the three bits above, which belong to other classes and are cleared by the mask.
  4. A carry into the fourth bit above needs c_k = 16, so k = 15, which lands above bit 63, outside the word.
- **The high half by bit reversal, proved.** The identity `hi (x, y) = rev (lo (rev x, rev y)) >> 1` is a property of `Clmul_Ref`, proved bit by bit.
- **The reference stays.** The bit-by-bit multiplication stays in the code as `Mul_Serial`, Gold against `Mul_Ref` as today. The harness compares the two on the vectors and on random operands.
- **Constant time.** The new `Mul` has no branch and no memory access that depends on the operands. It adds one hypothesis: the processor's integer multiplication takes a time independent of its operands. It holds on the x86-64 and ARMv8 processors this project targets, and upstream makes the same assumption. The trust model lists it.
- **What stays for M3.** The processor's carry-less instruction, as a second form chosen at build time, with the trust that it implies. It is discussed with the two trust models of M3.

## Alternatives considered

- **The processor's instruction now.** 18 times faster than today, against 7 for the software form. But its correctness would be tested, not proved, and it ties the build to the processor. Kept for M3.
- **Products of 32-bit halves.** With 32-bit operands in 64-bit words, no digit reaches 16 and no bit reversal is needed, so the proof is simpler. But it costs more products and departs from upstream. Kept as the fallback if the proof of the 64-bit form does not close.
- **A table of multiples by windows of bits.** Constant time needs a masked read of every entry, which makes it slower than today.
- **Leave `clmul64_lo` tested and not proved.** It gives the speed at once, but it leaves a hole in a Gold kernel that every other proof uses. Rejected for now: the decision is to have everything Gold before the trade-offs of M3.

## Consequences

- `GF2_128` gains `Mul_Serial`, the ghost references `Clmul_Ref` and the reduction, and the lemmas of the integer product. Its header and chapter 1 of the guide describe the new algorithm and its proof.
- `Square` stays `Mul (E, E)` and gets faster with it.
- Every caller of `Mul` keeps the same contract, so no other proof changes.
- The trust model gains the hypothesis on the integer multiplication.

## Verification impact

Proved: `Mul = Mul_Ref (A, B, 128)` for all operands, through `Clmul_Ref` and the reduction; `Mul_Serial` as today. Tested: the two forms agree on the vectors and on random operands; the mDoc proofs stay identical byte for byte. Trusted: the constant time of the processor's integer multiplication.

## References

- google/longfellow-zk at d5e6be7: `rust/runtime/algebra/src/arch/generic.rs` (`clmul64`, `clmul64_lo`, `clmul64_hi`, `gf2_128_reduce`, `gf2_128_mul`), `x86_64.rs`, `aarch64.rs`.
- [ADR 0004](0004-gf2-128-element-representation.md) (the two limbs), [ADR 0005](0005-mul-ref-as-proof-target.md) (`Mul_Ref`), [ADR 0006](0006-constant-time-discipline-and-scope.md) (constant time), [ADR 0055](0055-phase-d-scope-mdoc-scale.md) (the milestones), [ADR 0063](0063-milestone-m1-algorithmic-parity.md) (M1).
- T. Pornin, BearSSL, "Constant-time multiplication" (the integer product with holes).
