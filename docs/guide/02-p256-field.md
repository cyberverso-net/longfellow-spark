# Chapter 2: the P-256 base field F_p

Package `P256_Field` (`src/p256_field.ads`, `src/p256_field.adb`). Stage 2 of phase A. Decisions: [ADR 0012](../adr/0012-p256-limb-representation.md) to [ADR 0017](../adr/0017-p256-test-anchors.md). Specification: draft-google-cfrg-libzk-03, Table 1 (p256, FieldID 0x01), Section 7.2.1 (serialisation), Section 3.4.3 (rejection of non-canonical values). Curve constants: RFC 5903 Section 3.1, identical to SEC 2 v2.0 Section 2.4.2.

## 1. The mathematics

### 1.1 The prime and why this field

The ECDSA signatures on mDoc credentials are over the NIST curve P-256, whose points have coordinates in F_p with

    p = 2^256 - 2^224 + 2^192 + 2^96 - 1
      = FFFFFFFF 00000001 00000000 00000000 00000000 FFFFFFFF FFFFFFFF FFFFFFFF (hex)

(draft-03 Table 1 prints it in decimal; RFC 5903 Section 3.1 in hex). The circuits that verify an ECDSA signature inside the zero-knowledge proof compute in this field, so the verifier and prover need its arithmetic. It is the *base* field, in which the curve equation y^2 = x^3 - 3x + b lives; it is not the *scalar* field of order n in which signature scalars live. The draft is inconsistent on this point in two places (Section 3.4.3 and Appendix B.3.2 say "scalar field"), but the prime it prints is p.

The shape of p is a Solinas prime: a sum of a few signed powers of two, all multiples of 2^32. This is what makes reduction cheap (Section 1.5). Unlike GF(2^128), where addition was xor and there were no carries, F_p is the integers modulo p: addition carries, multiplication produces a 512-bit integer, and every result has to be brought back below p.

### 1.2 Representation and canonical form

An element is an integer in 0 .. p - 1, stored as four 64-bit limbs in little-endian limb order: `Limbs (0)` is the least significant word, so the value is

    To_Int (L) = L(0) + L(1) * 2^64 + L(2) * 2^128 + L(3) * 2^192.

Every integer below 2^256 has exactly one such representation, and p < 2^256, so elements have exactly one representation each: this is *canonical form*. Keeping every element canonical makes equality a limb comparison and serialisation a byte copy. The package enforces it with a type predicate ([ADR 0015](../adr/0015-p256-canonical-form-and-conditional-subtraction.md)): no `Element` can exist whose value is p or more.

Serialisation (Section 7.2.1) writes the 32 bytes of the integer least significant byte first, so limb i occupies bytes 8i .. 8i + 7. An encoding whose integer is p or more is not the encoding of any element and is rejected, as the upstream Rust reference does; the draft's sampling rule (Section 3.4.3) assumes the same canonical range.

### 1.3 Addition, subtraction, negation

For a, b < p, the integer sum a + b is below 2p, so a + b mod p is either a + b or a + b - p, whichever lies in 0 .. p - 1. The difference a - b lies in -p + 1 .. p - 1, so a - b mod p is a - b if that is non-negative and a - b + p otherwise. Negation is 0 - a. Each operation is therefore a limb-wise add or subtract with carries or borrows across the four limbs, followed by one conditional correction by p.

### 1.4 Multiplication: the 512-bit product

The product of two 256-bit integers has up to 512 bits. With four limbs each, the schoolbook product is sixteen 64 x 64 bit partial products, each up to 128 bits, accumulated into eight 64-bit words by columns: column k collects the products L_i * M_j with i + j = k. This is the only step with a genuine multiplication; everything after it is additions and fixed rearrangements.

### 1.5 Reduction: the special form of p

Reduction replaces a 512-bit integer X by X mod p. Writing X = X_lo + X_hi * 2^256 with both halves below 2^256, the identity

    2^256 = 2^224 - 2^192 - 2^96 + 1   (mod p)

turns the high half into a 256-bit-sized contribution. The NIST formulation (FIPS 186-4 Appendix D.2.3, also SEC 2) does this in one step for all eight high 32-bit words at once. Split X into sixteen 32-bit words c_0 .. c_15 and form nine 256-bit terms from the words c_8 .. c_15 and c_0 .. c_7, each term listing its eight words from most to least significant:

    T  = (c7, c6, c5, c4, c3, c2, c1, c0)
    S1 = (c15, c14, c13, c12, c11, 0, 0, 0)
    S2 = (0, c15, c14, c13, c12, 0, 0, 0)
    S3 = (c15, c14, 0, 0, 0, c10, c9, c8)
    S4 = (c8, c13, c15, c14, c13, c11, c10, c9)
    D1 = (c10, c8, 0, 0, 0, c13, c12, c11)
    D2 = (c11, c9, 0, 0, c15, c14, c13, c12)
    D3 = (c12, 0, c10, c9, c8, c15, c14, c13)
    D4 = (c13, 0, c11, c10, c9, 0, c15, c14)

Then X = T + 2 S1 + 2 S2 + S3 + S4 - D1 - D2 - D3 - D4 (mod p). The vector generator (`tests/vectors/gen_p256_vectors.py`) does not take this on trust: it shows that the identity is *exact*, not only modular,

    X = (S - N) + (q_8 c_8 + q_9 c_9 + ... + q_15 c_15) * p

with S = T + 2 S1 + 2 S2 + S3 + S4, N = D1 + D2 + D3 + D4 and eight fixed integer quotients q_j (q_8 = 1, q_9 = 2^32 + 1, and so on up to q_15, a 225-bit number); it derives the q_j from the table, checks that each is an integer, and verifies the identity on random 512-bit inputs and on the largest product (p - 1)^2. The exactness matters for the proofs: an equality between integers with constant coefficients is linear arithmetic, which SMT solvers handle well, whereas a congruence is not.

The signed sum S - N can be negative. The implementation adds a fixed multiple of p to make it non-negative: with all words at their maximum, S is below 2^259 and N below 2^258, and k = 5 is the smallest k with k p >= N_max, so

    V = S - N + 5 p,     0 <= V < 2^260.

V still has up to four bits above 2^256. One more application of the identity, with V = V_lo + V_hi * 2^256 and V_hi <= 9,

    W = V_lo + V_hi * (2^224 - 2^192 - 2^96 + 1),     W < 2^257 and W < 2 p,

so a single conditional subtraction of p brings W into 0 .. p - 1. All bounds are computed and asserted by the generator and are the input to the proofs of Section 3.

### 1.6 Inversion

By Fermat's little theorem, a^(p - 1) = 1 for a non-zero, so a^-1 = a^(p - 2). The exponent

    p - 2 = FFFFFFFF 00000001 00000000 00000000 00000000 FFFFFFFF FFFFFFFF FFFFFFFD

has long runs of ones and zeros, so a short addition chain computes it with about 255 squarings and a few multiplications, with no data-dependent branch. As in GF(2^128), the chain returns zero on zero and `Inv (Zero) = Zero` is the documented behaviour ([ADR 0016](../adr/0016-p256-inversion.md)).

### 1.7 The curve equation as an external anchor

The base point G = (Gx, Gy) of P-256 satisfies Gy^2 = Gx^3 - 3 Gx + b mod p, with b, Gx, Gy public constants (RFC 5903 Section 3.1). A single identity that exercises multiplication, squaring, subtraction and the constant b, whose inputs were produced by people who never saw this code, is the P-256 analogue of the subfield basis anchors of Chapter 1 ([ADR 0017](../adr/0017-p256-test-anchors.md)).

## 2. The algorithms

### 2.1 Limb addition and subtraction without wrap

A 64-bit addition can carry; a 64-bit subtraction can borrow. The package forms every limb step in 128 bits so that nothing wraps and the carry or borrow is simply the high half:

    addition:     W_i = A_i + B_i + carry_in         (< 2^65)
                  R_i = low 64 bits of W_i,  carry_out = high half of W_i (0 or 1)

    subtraction:  W_i = A_i + 2^64 - B_i - borrow_in  (in 0 .. 2^65 - 1, never negative)
                  R_i = low 64 bits of W_i,  borrow_out = 1 - high half of W_i

In the subtraction the added 2^64 keeps the intermediate non-negative; its high half is 1 exactly when no borrow occurred. Both are fixed sequences of four steps, unrolled, with no loop and no branch.

### 2.2 Conditional correction by p, in constant time

After an addition the sum is S = s + carry * 2^256 with s the four limbs. Compute D = s - p with borrow b over four limbs. The sum is at least p exactly when carry = 1 or b = 0. A mask that is all ones in that case and zero otherwise selects, limb by limb, either D or s with `and`, `or` and `not`: both candidates are always computed and the selection has no branch. The same selection applies after a subtraction (add p back when the difference borrowed) and after the final reduction step of a multiplication.

### 2.3 Canonical test and encoding

`Is_Canonical (L)` is the borrow of L - p computed by the same four-step subtraction: 1 when L < p. It is branch-free and is the executable form of the type predicate. Decoding assembles each limb from eight bytes by shifts and `or`; encoding extracts bytes by shift and mask; `From_Bytes` decodes, tests canonical form, and returns either the limbs or zero through the same masked selection.

### 2.4 The multiplication pipeline

    1. product    : sixteen 128-bit partial products into eight 64-bit words
    2. words      : split the eight words into sixteen 32-bit words c_0 .. c_15
    3. S and N    : form the nine terms of Section 1.5 and add them (five limbs each)
    4. V          : S + 5 p - N, five limbs, non-negative by the bound on N
    5. W          : V_lo + V_hi * (2^224 - 2^192 - 2^96 + 1), five limbs, below 2 p
    6. canonical  : one conditional subtraction of p

Each stage has a postcondition stated on the integer value, so the proof of `Mul` composes six smaller proofs (Section 3).

### 2.5 The inversion chain

Write X_k for E^(2^k - 1). As in Chapter 1, X_(a+b) = (X_a)^(2^b) * X_b, so X_2, X_3, X_6, X_12, X_15, X_30 and X_32 = E^(2^32 - 1) are reached with seven multiplications. The exponent p - 2, read as eight 32-bit words, is `ffffffff 00000001 00000000 00000000 00000000 ffffffff ffffffff fffffffd`; starting from R = X_32 (the first word), each further word is appended by 32 squarings followed by a multiplication: by E for `00000001`, by nothing for the three zero words (96 squarings), by X_32 for each `ffffffff`, and for the last word `fffffffd` (thirty ones, then `01`) by X_30 after 30 squarings and by E after 2 more. In total 255 squarings and 12 multiplications, a fixed sequence; the vector generator replays the chain on exponents and checks that it equals p - 2.

## 3. The Ada/SPARK implementation

This section follows `p256_field.ads` and `p256_field.adb` and explains each construct the first time it appears; Chapter 1 covered modular types, expression functions, `Ghost`, `Global`, `Post`, `Subprogram_Variant` and loop invariants.

### 3.1 Types

```ada
   Max_Words : constant := 8;
   type Word_Array is array (Natural range <>) of Unsigned_64;
   subtype Limb_Index is Natural range 0 .. 3;
   subtype Limb_Array is Word_Array (Limb_Index);     --  256 bits
   subtype Five_Array is Word_Array (0 .. 4);         --  320 bits
   subtype Wide_Array is Word_Array (0 .. 7);         --  512 bits
```

`Word_Array` is an *unconstrained* array type: its index range is fixed only when a subtype or an object is declared. One ghost model and one pair of add and subtract procedures then serve the 256-bit elements, the 320-bit accumulators of the reduction and the 512-bit product. The three subtypes are the only lengths used.

```ada
   type Element is record
      Limbs : Limb_Array;
   end record
   with Dynamic_Predicate => Is_Canonical (Element.Limbs);
```

A `Dynamic_Predicate` is a Boolean condition attached to a type: every value of the type must satisfy it, and GNATprove generates a check wherever a value of the type is created or assigned. Inside the aspect, the type name denotes the value being checked. Here the predicate is the executable, branch-free test `Is_Canonical`, so no `Element` can ever hold a value of p or more ([ADR 0015](../adr/0015-p256-canonical-form-and-conditional-subtraction.md)). The constants `Zero` and `One` are checked against it at elaboration.

### 3.2 The ghost model

```ada
   package U64_Conv is new Unsigned_Conversions (Unsigned_64);
   function Conv (X : Unsigned_64) return Big_Integer is
     (U64_Conv.To_Big_Integer (X)) with Ghost, Global => null;
   Two_64 : constant Big_Integer := Conv (Unsigned_64'Last) + 1 with Ghost;
```

`Ada.Numerics.Big_Numbers.Big_Integers` provides arbitrary-precision integers, which GNATprove understands as mathematical integers. `Unsigned_Conversions` is a *generic package*: a template parameterised by a type, here instantiated for `Unsigned_64` to obtain the conversion of a word to its integer value. `Two_64` is written as `Conv (Unsigned_64'Last) + 1` rather than `2 ** 64` because the provers evaluate the conversion of a literal but treat exponentiation as opaque; this detail decided the feasibility experiment behind [ADR 0014](../adr/0014-p256-functional-specification-and-ghost-model.md).

```ada
   function Weight (N : Natural) return Big_Integer is
     (if N = 0 then To_Big_Integer (1) else Two_64 * Weight (N - 1))
   with Ghost, Global => null, Pre => N <= Max_Words,
        Subprogram_Variant => (Decreases => N);

   function Partial (L : Word_Array; N : Natural) return Big_Integer is
     (if N = 0 then To_Big_Integer (0)
      else Partial (L, N - 1) + Conv (L (N - 1)) * Weight (N - 1))
   with Ghost, ...;

   function To_Int (L : Word_Array) return Big_Integer is (Partial (L, L'Length));
   P : constant Big_Integer := To_Int (P_Limbs) with Ghost;
```

`Weight (N)` is 2^(64 N), `Partial (L, N)` the value of the first N words, `To_Int` the value of the whole array, and `P` the prime, defined from its limbs so that no 256-bit literal appears anywhere. Every functional contract of the package is a statement about `To_Int`. `Pre` is a *precondition*: GNATprove proves it at every call and assumes it inside the body.

### 3.3 Lemmas

A *lemma* in SPARK is a ghost procedure whose postcondition states a fact and whose body proves it, usually by a sequence of `pragma Assert`. Calling the lemma makes the fact available at the call site. The project accepts no lemma with a null body: that would be an axiom ([ADR 0014](../adr/0014-p256-functional-specification-and-ghost-model.md)). The package has these:

- `Lemma_To_Int_Bounds` (and `Lemma_Partial_Bounds`, by recursion on N): 0 <= `To_Int (L)` < 2^(64 Length). A recursive lemma carries a `Subprogram_Variant` like a recursive function.
- `Lemma_Split`: a 128-bit value equals its low half plus 2^64 times its high half. Proved from `X / 2 ** 64` and `X mod 2 ** 64`, which the provers connect both to the shift and mask forms and to the integer model.
- `Lemma_Mul_Split`: the 128-bit product of two words neither wraps nor exceeds (2^64 - 1)^2, and its value is the product of the values. This is the one place where a nonlinear bound is proved; the provers manage it from the bounds of the factors.
- `Lemma_Weight_Add`: 2^(64 I) * 2^(64 J) = 2^(64 (I + J)), by recursion on J.
- `Lemma_Add_Step` and `Lemma_Sub_Step`: one word of addition with carry, or subtraction with borrow, extends the prefix identity from K words to K + 1. The addition and subtraction procedures call them once per iteration, so the loop invariant is the lemma's postcondition.
- `Lemma_To_Int_Eq`: two limb arrays that are equal element by element have the same `To_Int`. Stated with a precondition `for all I => A (I) = B (I)` rather than `A = B`, and proved by writing `Partial (A, 4)` and `Partial (B, 4)` out over the four limbs. The fact looks trivial, and it is, but the provers reach it from an array equality only through array extensionality, which they applied in some cold runs and not in others; the element-wise statement is proved every time. It exists for the last step of `Stage_Final` (3.6).
- `Lemma_Shift`, `Lemma_Weight_T32`, `Lemma_P_Poly`, `Lemma_Word_Split`, `Lemma_Word_Sum`, `Lemma_WVal_Bounds`, `Lemma_Term_Bound`, `Lemma_Solinas`, `Lemma_Constants`, `Lemma_Mod_Multiple`: the multiplication lemmas, described with the pipeline in 3.6.

### 3.4 Add_Words and Sub_Words

```ada
   procedure Add_Words
     (A, B : Word_Array; R : out Word_Array; Carry : out Unsigned_64)
   with
     Pre  => A'First = 0 and then B'First = 0 and then R'First = 0
       and then A'Length = B'Length and then R'Length = A'Length
       and then A'Length in 1 .. Max_Words,
     Post => Carry <= 1
       and then To_Int (R) + Conv (Carry) * Weight (A'Length)
                = To_Int (A) + To_Int (B);
```

A *procedure* with `out` parameters returns several results; the precondition pins the array bounds, which an unconstrained type leaves open. The body is the four-step addition of Section 2.1 as a loop over `0 .. A'Length - 1`, with the invariant

```ada
         pragma Loop_Invariant
           (Partial (R, I + 1) + Conv (C) * Weight (I + 1)
              = Partial (A, I + 1) + Partial (B, I + 1));
```

which is exactly the postcondition restricted to the words processed so far. `Sub_Words` is the same with the borrow convention of Section 2.1 and the additional postcondition `(Borrow = 1) = (To_Int (A) < To_Int (B))`, which is what makes `Is_Canonical` and the conditional corrections provable. Both loops have compile-time bounds and no data-dependent control flow.

### 3.5 Add, Sub, Neg, Is_Canonical

`Add` computes the sum with carry, the difference with p, the mask `0 - Ge` where `Ge` is 1 iff the sum is at least p, and the masked selection. The assertions in the body record the case analysis for the prover: if the sum overflowed 2^256 then the low part is below p (because the sum is below 2 p), and in both cases the selected value is the sum or the sum minus p and lies in 0 .. p - 1, which gives the `mod P` of the postcondition. `Sub` is symmetric: subtract, add p back, select by the borrow. `Neg (A)` is `Sub (Zero, A)`, Gold by composition. `Is_Canonical (L)` is the borrow of `Sub_Limbs (L, P_Limbs)`; its postcondition `= (To_Int (L) < P)` is the postcondition of `Sub_Words` read off, and it is what the predicate of `Element` means in the model.

### 3.6 Mul: the pipeline and its proof

*Stage 1, the product.* `Wide_Mul (X, Y)` is a plain function whose body is the 128-bit multiplication and whose postcondition is the exact value and the bound; callers see only the postcondition, so the provers never reason about a 128-bit multiplication at the call sites. `Mul_Row (X, B)` multiplies one word by the four limbs into five words, with the carry chain of Section 2.1 and four prefix assertions. `Product` forms the four rows, places each at its word offset in eight words, and adds them; `Lemma_Shift` proves that placing five words at offset `Off` in eight zero words multiplies the value by 2^(64 Off), and the final assertions expand `To_Int (A) * To_Int (B)` as the sum of the four shifted rows and bound it below 2^512 so that no carry escapes.

*Stages 2 to 6, the reduction.* The identity of Section 1.5 is a polynomial identity in t = 2^32: p = t^8 - t^7 + t^6 + t^3 - 1, each 2^(32 j) is t^j, and the quotients q_j are small polynomials in t with coefficients 0, 1 or -1 (for instance q_11 = t^3 + t^2 - 1). Proving it as such keeps the provers in the territory they are good at, polynomial normalisation, and away from 256-bit numerals. Accordingly the ghost side defines `T32 (K)` = t^K, proves `Weight (K) = T32 (2 K)` and `P = T32 (8) - T32 (7) + T32 (6) + T32 (3) - 1` (`Lemma_P_Poly`, from the four limb literals), expresses the product as a sum of its sixteen 32-bit words (`Word_Sum`, `Lemma_Word_Sum`), each table term as `Term_Val`, and states `Lemma_Solinas`:

```ada
     Post => To_Int (R) = (S_Val (R) - N_Val (R)) + Q_Val (R) * P
       and then ... bounds on S_Val and N_Val ...
```

with `Q_Val` the explicit quotient. The executable side mirrors it: `Word (R, J)` extracts a 32-bit word (the if-expression selects on the constant slot index from the table, never on data), `Term (R, S)` assembles a 256-bit term from a row of the table, `Add_Term` accumulates terms into five words with a precondition that the sum fits, and `Reduce` runs the six stages with ghost variables `M_V` and `M_W` tracking the exact multiple of p by which each intermediate differs from the product. `Lemma_Mod_Multiple` closes: a value that differs from X by a multiple of p and lies in 0 .. p - 1 is X mod p. `Mul` is `Reduce (Product (A.Limbs, B.Limbs))`; `Square` is `Mul (E, E)`.

*Stage 6, the conditional subtraction.* `Stage_Final` takes the five-word value W of stage 5, which the earlier postconditions bound below 2p, and returns the four-limb canonical result. The executable part is three lines: `Sub_Words` computes W - p with a borrow `Bw`, which is 1 exactly when W < p; `Mask` is all ones when `Bw` is 0 and zero otherwise; `Select_Limbs` picks the low four words of the difference under the mask and of W otherwise, with no branch on data ([ADR 0015](../adr/0015-p256-canonical-form-and-conditional-subtraction.md)). The proof is written branch by branch on `Bw`, in ghost `if` statements that the compiler removes with the rest of the ghost code. In the branch `Bw = 0`, the difference is W - p and lies below p, so its top word times 2^256 is below 2^256 and `Lemma_Div_Bound` makes that word zero; the value of the difference is then the value of its low four words. In the branch `Bw = 1`, the same argument applies to W itself. Each branch then fixes the mask, asserts that the selected array equals the low words of the chosen operand element by element, and calls `Lemma_To_Int_Eq` to carry the equality to `To_Int`. The postcondition, the value is W or W - p according to the comparison and in either case canonical, follows in each branch separately. An earlier version proved the last step with one assertion over the selected array, relying on the provers to connect array equality with equal `To_Int`; it was proved in some cold runs and not in others. The branch-wise form, with the lemma, has been stable on every cold run since.

A ghost variable (`M_V : Big_Integer with Ghost`) exists only for proof and is removed with the other ghost code when assertions are disabled; `pragma Unreferenced` silences the warning for a lemma parameter that appears only in the contract; square-bracket aggregates `[a, b, c]` are the Ada 2022 array notation; `A (0 .. 7)` is a *slice*, a contiguous part of an array.

### 3.7 Inv

`Square_N (E, N)` squares N times in a loop; `Inv` is the chain of Section 2.5 as thirteen constant declarations and a final `Mul`, with no loop over exponent bits and no `if`. Its only contract is `Global => null`: Silver, by decision ([ADR 0016](../adr/0016-p256-inversion.md)).

### 3.8 Encoding

`Limb_Of_8` assembles a word from eight bytes by shifts and `or`; `Bytes_Of_Limb` extracts them with `Byte_Of`, and its postcondition is the 64-bit round trip. `Limbs_Of_Bytes` and `Bytes_Of_Limbs` work on four slices of the 32-byte array, so the 256-bit round trip in the postcondition of `Bytes_Of_Limbs` composes from the 64-bit one. `From_Bytes` decodes, tests canonical form with `Sub_Limbs`, and returns the limbs or zero through the masked selection; its postcondition says exactly which encodings are accepted and what they decode to.

## 4. What the proofs guarantee

GNATprove 16.1 with the project's prover configuration ([ADR 0020](../adr/0020-prover-configuration-step-budget.md): CVC5, Z3 and Alt-Ergo, `--steps=600000`, `--timeout=120`), the whole project (GF(2^128) and P-256 together): 3694 checks, all proved, no justification, no `pragma Assume`; of these, 3653 belong to `P256_Field` (the remaining 41 are Chapter 1's). Maximum steps for a single successful proof: 429702, within the budget of 600000; longest successful attempt 4 to 10 seconds on a ten-core machine, far from the timeout.

| Category | Checks | Discharged by |
|----------|--------|---------------|
| Data dependencies (`Global => null`) | 94 | flow analysis |
| Initialization | 38 | flow analysis |
| Run-time checks (indices, ranges, overflow, predicates) | 2197 | 82% trivial, the rest CVC5 and Z3 |
| Assertions (`pragma Assert`, loop invariants, variants) | 273 | CVC5 and Z3, Alt-Ergo about 4%, trivial 1% |
| Functional contracts (postconditions, lemma postconditions, preconditions at calls) | 1029 | CVC5 and Z3, Alt-Ergo about 1% |
| Termination | 63 | 55 flow, 8 provers |

Where the checks are, by subprogram (proof checks, excluding flow): the field operations themselves are small (`Add` 45, `Sub` 44, `Neg` 7, `Mul` 10, `Square` 9, `Is_Canonical` 4, `From_Bytes` 3, `To_Bytes` 1, `Inv` and `Square_N` 0); the word primitives and the multiplication pipeline carry more (`Add_Words` 41, `Sub_Words` 66, `Mul_Row` 54, `Product` 132, `Term` 64, `Add_Term` 35, `Sum_S` 15, `Sum_N` 12, `Stage_V` 46, `Stage_W` 63, `Stage_Final` 108, `Reduce` 35); and the lemmas carry the rest, the largest being `Lemma_Unfold_T32` (471, the explicit monomials of t), `Lemma_Term_Bound` (188), `Lemma_Solinas_Identity` (126) and `Lemma_Unfold` (124); `Lemma_To_Int_Eq` has 36. Three solvers are needed: CVC5 and Z3 share almost everything, and which of the two is credited with a check varies from run to run, since the first to answer wins; Alt-Ergo alone closes fifteen checks, polynomial normalisation steps and the bridges between modular words and the integer model, listed in ADR 0020.

Four lessons from closing the proofs, recorded here because they are reusable in the next stages:

- The provers evaluate the conversion of a *literal* to `Big_Integer` but treat `**` as opaque, so `Two_64` is `Conv (Unsigned_64'Last) + 1`, not `2 ** 64`.
- Modular word arithmetic is connected to the integer model only through small lemmas (`Lemma_Split`, `Lemma_Sub128`, `Lemma_Add128`, `Lemma_Ext64`), each proved once from `/`, `mod` and the no-wrap condition.
- Polynomial identities prove by normalisation when every weight is written out as a monomial in one base (`Lemma_Unfold`, `Lemma_Unfold_T32`); a recursive definition left folded is an atom the normaliser cannot see through.
- Large contexts time out even when every fact is present. The cure is structural: one function per stage with its own postcondition (`Sum_S`, `Sum_N`, `Stage_V`, `Stage_W`, `Stage_Final`), and one lemma per identity with exactly the hypotheses it needs (`Lemma_Power_Reduction` for t^j = rep_j + q_j p, word by word).

In plain terms, for every input, not on samples:

- no run-time error occurs anywhere in the package;
- every `Element` holds an integer in 0 .. p - 1, and `Is_Canonical` decides exactly that;
- `To_Int (Add (A, B)) = (To_Int (A) + To_Int (B)) mod p`, and likewise for `Sub`, `Neg`, `Mul` and `Square`, where `P`, defined from the limbs, is proved equal to t^8 - t^7 + t^6 + t^3 - 1 with t = 2^32 (`Lemma_P_Poly`);
- `From_Bytes` accepts an encoding exactly when its integer is below p and then returns that integer's limbs; `To_Bytes` inverts it;
- every subprogram terminates.

Reproduce with `make prove`, which runs `gnatprove -P longfellow_spark.gpr -j0 --checks-as-errors=on` with the switches of `package Prove` in the project file (`--prover=cvc5,z3,altergo --steps=600000 --timeout=120 --memlimit=1000 --report=all`) and prints the summary of `obj/development/gnatprove/gnatprove.out`; a plain `alr exec -- gnatprove -P longfellow_spark.gpr` proves the same thing.

## 5. What is only tested

The proofs relate the code to the model and the model to the polynomial form of p. They do not say that `P_Limbs` is the prime of Table 1 (a wrong limb would move `P` and every proof would still succeed), nor that the byte order is the one of Section 7.2.1, nor that `Inv` inverts. The vectors cover these ([ADR 0017](../adr/0017-p256-test-anchors.md)):

| File | Cases | External anchors |
|------|-------|------------------|
| `p256_add.txt` | 221 | add, sub, neg on b, Gx, Gy, p - 1 and the inverse of two (RFC 5903 Section 3.1) |
| `p256_mul.txt` | 139 | the intermediate products of Gy^2 = Gx^3 - 3 Gx + b, composed by the generator; (p - 1)^2 = 1; 2^128 * 2^128 = 2^256 mod p; one product per 32-bit word position of the 512-bit product |
| `p256_inv.txt` | 46 | inv 1, inv 2 = (p + 1) / 2, inv (p - 1), the inverses of Gx, Gy and b; `Inv (Zero) = Zero`; Fermat and Euclid references agree, and the harness re-checks E * Inv (E) = One |
| `p256_bytes.txt` | 61 | the encodings of b, Gx, Gy; p - 1 accepted, p, p + 1, 2^256 - 1 rejected; `To_Bytes` round trip |

Why the curve equation is an external anchor: b, Gx and Gy were published by NIST and are used by every P-256 implementation; the identity Gy^2 = Gx^3 - 3 Gx + b holds only for the right prime, the right reduction and the right byte order at once, and its three operands were produced by nobody involved in this code. The generator refuses to write the files if the identity fails for its own reference. In addition the generator re-derives the reduction table, its exact quotients and the bounds of Section 1.5, and replays the inversion chain on exponents.

The Appendix B vectors of the draft are not field anchors: B.2 states a secp256k1 prime, and B.3.2 mislabels the field; both are logged as specification issues ([ADR 0002](../adr/0002-pin-the-specification.md)).

Reproduce with:

```bash
alr exec -- gprbuild -P tests/longfellow_spark_tests.gpr -p
tests/bin/p256_kat           # expected: passed 467, failed 0 (about three minutes with assertions on)
```

The test build is slow because every `Mul` evaluates its postcondition with `Big_Integer` arithmetic, and `Inv` performs 267 multiplications per case.

## 6. What stays trusted, and the limits

- Fermat's little theorem for `Inv`, and the exponent arithmetic of the chain (checked by the generator, not proved in SPARK).
- GNATprove's model of `Ada.Numerics.Big_Numbers.Big_Integers` and of the conversions from modular types; the SMT solvers; the compiler, including its 128-bit arithmetic.
- The target is 64-bit: `Unsigned_128` is required ([ADR 0012](../adr/0012-p256-limb-representation.md)).
- Constant time is a discipline, scoped to assertion-free builds ([ADR 0006](../adr/0006-constant-time-discipline-and-scope.md)); loop bounds and table indices are compile-time constants, every selection is masked, `From_Bytes` may branch on its Boolean result because encodings are public data. Nothing measures timing.
- Performance is not a goal: `Mul` costs sixteen 128-bit products plus the reduction, `Inv` 267 multiplications. Montgomery form and specialised squaring remain available as prover-side optimisations behind the same contracts ([ADR 0013](../adr/0013-p256-reduction-strategy.md)).
