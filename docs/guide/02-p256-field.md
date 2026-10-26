# Chapter 2: the P-256 base field F_p

Package `P256_Field` (`src/p256_field.ads`, `src/p256_field.adb`). Stage 2 of phase A. Decisions: [ADR 0012](../adr/0012-p256-limb-representation.md) to [ADR 0017](../adr/0017-p256-test-anchors.md), and [ADR 0069](../adr/0069-p256-montgomery-multiplication.md), which replaced the direct representation and the Solinas reduction of ADR 0013 by the Montgomery form and the multiplication of upstream. Specification: draft-google-cfrg-libzk-03, Table 1 (p256, FieldID 0x01), Section 7.2.1 (serialisation), Section 3.4.3 (rejection of non-canonical values). Curve constants: RFC 5903 Section 3.1, identical to SEC 2 v2.0 Section 2.4.2.

## 1. The mathematics

### 1.1 The prime and why this field

The ECDSA signatures on mDoc credentials are over the NIST curve P-256, whose points have coordinates in F_p with

    p = 2^256 - 2^224 + 2^192 + 2^96 - 1
      = FFFFFFFF 00000001 00000000 00000000 00000000 FFFFFFFF FFFFFFFF FFFFFFFF (hex)

(draft-03 Table 1 prints it in decimal; RFC 5903 Section 3.1 in hex). The circuits that verify an ECDSA signature inside the zero-knowledge proof compute in this field, so the verifier and prover need its arithmetic. It is the *base* field, in which the curve equation y^2 = x^3 - 3x + b lives; it is not the *scalar* field of order n in which signature scalars live. The draft is inconsistent on this point in two places (Section 3.4.3 and Appendix B.3.2 say "scalar field"), but the prime it prints is p.

The shape of p is a Solinas prime: a sum of a few signed powers of two, all multiples of 2^32. This is what makes reduction cheap (Section 1.5): it needs shifts and additions, not multiplications. Unlike GF(2^128), where addition was xor and there were no carries, F_p is the integers modulo p: addition carries, multiplication produces a 512-bit integer, and every result has to be brought back below p.

### 1.2 Representation and canonical form

An element is an integer in 0 .. p - 1, stored as four 64-bit limbs in little-endian limb order: `L0` is the least significant word, so the value of the limbs L = `Limbs (E)` is

    To_Int (L) = L(0) + L(1) * 2^64 + L(2) * 2^128 + L(3) * 2^192.

Every integer below 2^256 has exactly one such representation, and p < 2^256, so elements have exactly one representation each: this is *canonical form*. Keeping every element canonical makes equality a limb comparison and serialisation a byte copy. The package enforces it with a type predicate ([ADR 0015](../adr/0015-p256-canonical-form-and-conditional-subtraction.md)): no `Element` can exist whose value is p or more.

**The Montgomery form** ([ADR 0069](../adr/0069-p256-montgomery-multiplication.md)). The element of value x does not store x. It stores x R mod p, with R = 2^256. The stored integer is still canonical, so the two paragraphs above hold for it: one representation per element, equality as a limb comparison. What changes is the meaning of the limbs. Zero stores 0; One stores R mod p = 2^256 - p; the sum of two stored integers is the stored integer of the sum, since (x R + y R) mod p = (x + y) R mod p. Only the product and the boundaries need care: the bytes, the constants and the parsers convert in and out (Sections 2.3 and 3.8).

Serialisation (Section 7.2.1) writes the 32 bytes of the integer least significant byte first, so limb i occupies bytes 8i .. 8i + 7. An encoding whose integer is p or more is not the encoding of any element and is rejected, as the upstream Rust reference does; the draft's sampling rule (Section 3.4.3) assumes the same canonical range.

### 1.3 Addition, subtraction, negation

For a, b < p, the integer sum a + b is below 2p, so a + b mod p is either a + b or a + b - p, whichever lies in 0 .. p - 1. The difference a - b lies in -p + 1 .. p - 1, so a - b mod p is a - b if that is non-negative and a - b + p otherwise. Negation is 0 - a. Each operation is therefore a limb-wise add or subtract with carries or borrows across the four limbs, followed by one conditional correction by p.

### 1.4 Multiplication in Montgomery form

The product of two stored integers a = x R and b = y R is x y R^2, one factor R too many. Montgomery's method (1985) computes a b R^-1 mod p directly, which is x y R mod p, the stored integer of the product. It never divides by p. It divides by 2^64, four times, which is a shift by one word.

The method interleaves the product with the reduction, one word of a at a time. With W = 2^64 and an accumulator T, starting at 0:

    for i = 0 .. 3:
        T := T + a_i b              (one row of the product)
        r := T mod W                (the low word)
        T := (T + r p) / W          (exact: the low word becomes zero)

The division is exact because p = -1 mod W for this prime, so T + r p = r - r = 0 mod W. For a general prime one would multiply r by -p^-1 mod W first; for P-256 that factor is 1. After four rounds T W^4 = a b + Q p for the integer Q = sum of r_i W^i, so T = a b R^-1 mod p. A bound runs through the rounds: if T < 2p before a round, then after it T < (2p + (W - 1)(p - 1) + (W - 1) p) / W < 2p. So one conditional subtraction of p at the end gives the canonical result.

### 1.5 The reduction step for this p

Adding r p needs no multiplication, because

    p = 2^256 - 2^224 + 2^192 + 2^96 - 1.

So r p is r shifted to 2^256, 2^192 and 2^96, minus r shifted to 2^224, minus r. With r split into its halves r_lo = (r mod 2^32) 2^32 and r_hi = r / 2^32, the shifts by 96 and 224 land on word boundaries:

    V = [0, r_lo, r_hi, r, r, 0]       = r (2^96 + 2^192 + 2^256)
    U = [r, 0, 0, r_lo, r_hi, 0]       = r (1 + 2^224)
    T + r p = (T + V) - U

in six words, least significant first. This is upstream's `p256_reduction_step` (`rust/runtime/algebra/src/p256/p256_64.rs`). Adding V first and subtracting U after keeps every intermediate non-negative.

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

`Is_Canonical (L)` is the borrow of L - p computed by the same four-step subtraction: 1 when L < p. It is branch-free and is the executable form of the type predicate. Decoding assembles each limb from eight bytes by shifts and `or`; encoding extracts bytes by shift and mask; `From_Bytes` decodes, tests canonical form, selects the limbs or zero through the same masked selection, and puts the result in Montgomery form by one multiplication by R^2 mod p: Mont (x, R^2) = x R^2 R^-1 = x R. `To_Bytes` does the reverse with one multiplication by 1: Mont (x R, 1) = x.

### 2.4 The multiplication

    for each of the four words a_i of A, in a six-word accumulator T:
      1. row      : a_i times the four limbs of B, five words (Mul_Row)
      2. add      : T + row
      3. reduce   : r the low word; T + V (r), then - U (r)
      4. down     : drop the low word, now zero
    then          : one conditional subtraction of p from the low five words

Each round is one procedure (`Round`) with a postcondition on the integer value, and the loop over the four rounds carries the invariant T W^i = a_0..i-1 b + Q p (Section 3.6).

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
```

`Word_Array` is an *unconstrained* array type: its index range is fixed only when a subtype or an object is declared. One ghost model and one pair of add and subtract procedures then serve the 256-bit elements, the 320-bit rows and the 384-bit accumulator of the multiplication (`Six_Array`, in the body).

```ada
   function Canonical_Limbs (L0, L1, L2, L3 : Unsigned_64) return Boolean
   is (Is_Canonical ([L0, L1, L2, L3]))
   with Post => (if L3 < 16#FFFF_FFFF_0000_0001# then Canonical_Limbs'Result),
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   type Element is record
      L0, L1, L2, L3 : Unsigned_64;
   end record
   with Dynamic_Predicate =>
     Canonical_Limbs (Element.L0, Element.L1, Element.L2, Element.L3);

   function Limbs (E : Element) return Limb_Array is
     ([E.L0, E.L1, E.L2, E.L3])
   with Post => Limbs'Result (0) = E.L0 and then ... ,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");
```

The four limbs are scalar components, not an array ([ADR 0070](../adr/0070-sumcheck-and-ligero-kernels-as-upstream.md)). For the provers an array component is a map over all of `Natural`, so two elements with the same four limbs would not be equal as values; a record of scalars is a datatype, and equal limbs give equal elements with no further fact. The ring laws of the field (end of Section 3.6) rest on this. The memory layout is that of an array of four words, the `limb_` array of upstream's `Nat`. `Limbs (E)` gives the array for the arithmetic, which stays on `Limb_Array`.

Two bodies are hidden from the provers, so that no aggregate sits in the context of every proof on P-256:

- `Limbs`: the provers see its postcondition, limb by limb.
- `Canonical_Limbs`, the predicate: elsewhere it is an opaque fact that every element carries. Its postcondition covers a top limb below that of p, enough for `Zero` and `One`. The body is visible only in `Of_Limbs`, which builds an element, and in the ghost lemma `Lemma_Canonical`, which turns the predicate into `To_Int (Limbs (A)) < P`. `Add`, `Sub` and `Mul` call this lemma on their operands.

A `Dynamic_Predicate` is a Boolean condition attached to a type: every value of the type must satisfy it, and GNATprove generates a check wherever a value of the type is created or assigned. Inside the aspect, the type name denotes the value being checked. Here the predicate is the executable, branch-free test `Is_Canonical` on the four limbs, so no `Element` can ever hold a value of p or more ([ADR 0015](../adr/0015-p256-canonical-form-and-conditional-subtraction.md)). The constants `Zero` and `One` are checked against it at elaboration.

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
- `Lemma_Add_Step` and `Lemma_Sub_Step`: one word of addition with carry, or subtraction with borrow, extends the prefix identity from K words to K + 1. The addition and subtraction procedures call them once per iteration, so the loop invariant is the lemma's postcondition.
- `Lemma_To_Int_Eq`: two limb arrays that are equal element by element have the same `To_Int`. Stated with a precondition `for all I => A (I) = B (I)` rather than `A = B`, and proved by writing `Partial (A, 4)` and `Partial (B, 4)` out over the four limbs. The fact looks trivial, and it is, but the provers reach it from an array equality only through array extensionality, which they applied in some cold runs and not in others; the element-wise statement is proved every time. It closes `Mont_Mul` and `Mul` (3.6), and the accepted branch of `From_Bytes` (3.8).
- `Lemma_R_Inv`, `Lemma_R2`, `Lemma_P1`, `Lemma_VU`, `Lemma_Down`, `Lemma_Ext6`, `Lemma_Six_Split`, `Lemma_Mont_Final`, `Lemma_To_Mont`, `Lemma_Mod_Multiple`: the multiplication lemmas, described in 3.6 and 3.8.

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

`Add` computes the sum with carry, the difference with p, the mask `0 - Ge` where `Ge` is 1 iff the sum is at least p, and the masked selection. The assertions in the body record the case analysis for the prover: if the sum overflowed 2^256 then the low part is below p (because the sum is below 2 p), and in both cases the selected value is the sum or the sum minus p and lies in 0 .. p - 1, which gives the `mod P` of the postcondition. These contracts speak of the stored integers, and since the Montgomery form is linear they say the same of the elements. `Sub` is symmetric: subtract, add p back, select by the borrow. `Neg (A)` is `Sub (Zero, A)`, Gold by composition. `Is_Canonical (L)` is the borrow of `Sub_Limbs (L, P_Limbs)`; its postcondition `= (To_Int (L) < P)` is the postcondition of `Sub_Words` read off, and it is what the predicate of `Element` means in the model.

### 3.6 Mul: Montgomery multiplication and its proof

The contract of `Mul` speaks of the stored integers:

```ada
   function Mul (A, B : Element) return Element with
     Post => (Proof_Only => To_Int (Limbs (Mul'Result))
               = (To_Int (Limbs (A)) * To_Int (Limbs (B)) * R_Inv) mod P);
```

`R_Inv` is 2^-256 mod p, a ghost constant written as four limbs. `Lemma_R_Inv` proves `Two_256 * R_Inv = 1 + K * P` for a second constant K. The provers check it by evaluating the products of the literal limbs; it is the only place where 256-bit numbers are multiplied as numbers. `Add`, `Sub`, `Mul`, `From_Bytes` and `From_Canonical` compute on the limbs alone (`Add_Mod`, `Sub_Mod`, `Mont_Mul`) and build the element with `Of_Limbs`.

*The row.* `Wide_Mul (X, Y)` is a plain function whose body is the 128-bit multiplication and whose postcondition is the exact value and the bound; callers see only the postcondition, so the provers never reason about a 128-bit multiplication at the call sites. `Mul_Row (X, B)` multiplies one word by the four limbs into five words, with the carry chain of Section 2.1 and four prefix assertions.

*The round.* `Round (T, X, B, R)` takes a six-word accumulator below 2p, and its postcondition is

```ada
     Post => (Proof_Only => To_Int (T) < 2 * P
              and then To_Int (T) * Two_64
                       = To_Int (T'Old) + Conv (X) * To_Int (B) + Conv (R) * P);
```

The body is four calls: `Add_Words` adds the row, `Add_Words` adds V (r), `Sub_Words` subtracts U (r), and `Down` drops the low word. The proof states, at each call, why no carry leaves the six words and why the subtraction does not borrow. `Lemma_VU` gives V (r) - U (r) = r p. It goes through the 128-bit product r 2^32, whose two halves are the two shifted words; that is how the shifts reach the integer model. The low word is then zero: with p = W P1 - 1 (`Lemma_P1`), the value is W times an integer, and `Lemma_Digit`, the uniqueness of a base-W digit, makes the low word 0. `Lemma_Div_Bound` carries the bound below 2p from T W to T.

*The rounds.* `Mont_Mul` loops over the four words of A with a ghost `Q : Big_Integer` and the invariant

```ada
   To_Int (T) < 2 * P and then To_Int (T) * Weight (I)
                               = Partial (A, I) * To_Int (B) + Q * P
```

After the loop, `Lemma_Six_Split` shows that word 5 is zero and word 4 at most one, and the conditional subtraction of Section 2.2 gives a result below p, equal to T or T - p. It is written branch by branch, with `Lemma_To_Int_Eq` for the selected array, as in `Add`. `Lemma_Mont_Final` closes. From T 2^256 = A B + Q p and 2^256 R_Inv = 1 + K p, the result is A B R_Inv plus a multiple of p, and lies in 0 .. p - 1, so `Lemma_Mod_Multiple` makes it A B R_Inv mod p. `Mul` returns `Of_Limbs (Mont_Mul (Limbs (A), Limbs (B)))`; `Square` is `Mul (E, E)`.

*Associativity.* `Lemma_Mul_Assoc` (ADR 0066) now meets the factor R_Inv twice on each side: both products are X Y Z R_Inv^2 mod p, by `Lemma_Mod_Mul` twice, and `Lemma_Inj` turns equal integers into equal elements.

*The other ring laws* (ADR 0070): commutativity, `One` as unit, distributivity over `Add` and `Sub`, and the laws of `Add`, `Neg` and `Sub` that the sumcheck kernels use. Each is proved the same way: the two sides have the same integer mod p, and `Lemma_Inj` makes them equal elements. `Field_P256` restates them with `Same`, through `Laws.Lemma_Same`, which needs nothing more than `X = Y` since the limbs are scalar components.

A ghost variable (`Q : Big_Integer with Ghost`) exists only for proof and is removed with the other ghost code when assertions are disabled; square-bracket aggregates `[a, b, c]` are the Ada 2022 array notation; `A (0 .. 7)` is a *slice*, a contiguous part of an array. `Add_Words`, `Sub_Words` and `Mul_Row` are `Inline`, so that the compiler sees their lengths and unrolls the loops.

### 3.7 Inv

`Square_N (E, N)` squares N times in a loop; `Inv` is the chain of Section 2.5 as thirteen constant declarations and a final `Mul`, with no loop over exponent bits and no `if`. Its only contract is `Global => null`: Silver, by decision ([ADR 0016](../adr/0016-p256-inversion.md)).

### 3.8 Encoding

`Limb_Of_8` assembles a word from eight bytes by shifts and `or`; `Bytes_Of_Limb` extracts them with `Byte_Of`, and its postcondition is the 64-bit round trip. `Limbs_Of_Bytes` and `Bytes_Of_Limbs` work on four slices of the 32-byte array, so the 256-bit round trip in the postcondition of `Bytes_Of_Limbs` composes from the 64-bit one. `From_Bytes` decodes, tests canonical form with `Sub_Limbs`, selects the limbs or zero through the masked selection, and stores `Mont_Mul (S, R2)`. `Lemma_R2` proves R2 R_Inv = 2^256 + K2 p for the constant R2 = 2^512 mod p, and `Lemma_To_Mont` turns that into (S R2 R_Inv) mod p = (S 2^256) mod p. The postcondition says which encodings are accepted, that a refused one gives `Zero`, and that an accepted one stores its integer times 2^256 mod p. `To_Canonical (E)` is `Mont_Mul (Limbs (E), [1, 0, 0, 0])`, the integer E R_Inv mod p below p, and `To_Bytes` encodes it. `From_Canonical (L)`, for constants and parsers, and `Of_Natural (X)` are `Mont_Mul` by R2 again.

## 4. What the proofs guarantee

GNATprove 16.1 with the project's prover configuration ([ADR 0020](../adr/0020-prover-configuration-step-budget.md): CVC5, Z3 and Alt-Ergo, `--steps=600000`, `--timeout=120`).

- `P256_Field` alone, proved from an empty object directory: 2897 checks, all proved.
- The whole project with the scalar limbs of ADR 0070: 21332 checks, all proved. With the bound-quad reuse of ADR 0071: 25331 checks, all proved.
- No justification, no `pragma Assume`.
- Maximum steps for a single successful proof in `P256_Field`: 204295, within the budget of 600000.

| Category | Checks | Discharged by |
|----------|--------|---------------|
| Data dependencies (`Global => null`) | 71 | flow analysis |
| Initialization | 26 | flow analysis |
| Run-time checks (indices, ranges, overflow, predicates) | 1523 | 83% trivial, the rest mostly Z3, then CVC5 |
| Assertions (`pragma Assert`, loop invariants, variants) | 214 | Z3 and CVC5, Alt-Ergo about 5%, trivial 1% |
| Functional contracts (postconditions, lemma postconditions, preconditions at calls) | 540 | Z3 and CVC5, Alt-Ergo about 1% |
| Termination | 38 | 35 flow, 3 Z3 |

Where the proof checks are, by subprogram (excluding flow):

- The field operations are small: `Add` 45, `Sub` 44, `Neg` 7, `Mul` 13, `Square` 10, `Is_Canonical` 4, `From_Bytes` 54, `From_Canonical` 13, `To_Canonical` 31, `Of_Natural` 23, `To_Bytes` 1, `Inv` and `Square_N` 0.
- The word primitives and the multiplication carry more: `Add_Words` 41, `Sub_Words` 66, `Mul_Row` 54, `Round` 147, `Mont_Mul` 177.
- The lemmas carry the rest. The largest are `Lemma_Unfold` (124), `Lemma_VU` (114), `Lemma_Sub_Step` (85), `Lemma_Mul_Assoc` (80), `Lemma_Add_Step` (79), `Lemma_R_Inv` and `Lemma_Mont_Final` (78 each), `Lemma_To_Mont` (75) and `Lemma_R2` (72).

Three solvers are needed. Z3 and CVC5 share almost everything, and which of the two is credited with a check varies from run to run, since the first to answer wins. Alt-Ergo closes a few polynomial normalisation steps and bridges between modular words and the integer model, as listed in ADR 0020.

Four lessons from closing the proofs, recorded here because they are reusable in the next stages:

- The provers evaluate the conversion of a *literal* to `Big_Integer` but treat `**` as opaque, so `Two_64` is `Conv (Unsigned_64'Last) + 1`, not `2 ** 64`.
- Modular word arithmetic is connected to the integer model only through small lemmas (`Lemma_Split`, `Lemma_Sub128`, `Lemma_Add128`, `Lemma_Ext64`), each proved once from `/`, `mod` and the no-wrap condition.
- Polynomial identities prove by normalisation when every weight is written out as a monomial in one base (`Lemma_Unfold`); a recursive definition left folded is an atom the normaliser cannot see through.
- Large contexts time out even when every fact is present. The cure is structural: one subprogram per step with its own postcondition (`Round`, then `Mont_Mul`), and one lemma per identity with exactly the hypotheses it needs (`Lemma_VU`, `Lemma_Mont_Final`).

Two more came with the Montgomery form ([ADR 0069](../adr/0069-p256-montgomery-multiplication.md)):

- A shift of a word reaches the integer model most easily through a 128-bit product: r 2^32 as `Unsigned_128`, whose halves are the two shifted words, by `Lemma_Mul_Split` and `Lemma_Split`. Reasoning on `Conv` of `Shift_Left` or `mod 2 ** 32` directly did not close.
- GNAT 16 stops with an internal error on ghost constants declared in a `declare` block of executable code. The final argument of `Mont_Mul` is therefore a ghost procedure, `Lemma_Mont_Final`, which is also the clearer form.

In plain terms, for every input, not on samples:

- no run-time error occurs anywhere in the package;
- every `Element` holds an integer in 0 .. p - 1, and `Is_Canonical` decides exactly that;
- `To_Int (Add (A, B)) = (To_Int (A) + To_Int (B)) mod p`, and likewise for `Sub` and `Neg`; `To_Int (Mul (A, B)) = To_Int (A) To_Int (B) 2^-256 mod p`, and likewise for `Square`, so that in the Montgomery form the elements add and multiply as the field does;
- `From_Bytes` accepts an encoding exactly when its integer x is below p and then stores x 2^256 mod p, a refused encoding gives `Zero`; `To_Canonical` returns the integer back, below p, and `To_Bytes` encodes it;
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
tests/bin/p256_kat           # expected: passed 467, failed 0
```

Until the consolidation after Phase A the test build was slow (about three minutes for these cases) because every `Mul` evaluated its postcondition with `Big_Integer` arithmetic and `Inv` performs 267 multiplications per case; since [ADR 0044](../adr/0044-field-contracts-at-proof-only-level.md) the model, the lemmas and the contracts that mention them are at the proof-only assertion level, proved for all inputs and never compiled, and the 467 cases take under a second. The type predicate of `Element` stays executable.

## 6. What stays trusted, and the limits

- Fermat's little theorem for `Inv`, and the exponent arithmetic of the chain (checked by the generator, not proved in SPARK).
- GNATprove's model of `Ada.Numerics.Big_Numbers.Big_Integers` and of the conversions from modular types; the SMT solvers; the compiler, including its 128-bit arithmetic.
- The target is 64-bit: `Unsigned_128` is required ([ADR 0012](../adr/0012-p256-limb-representation.md)).
- Constant time is a discipline, scoped to assertion-free builds ([ADR 0006](../adr/0006-constant-time-discipline-and-scope.md)); loop bounds and table indices are compile-time constants, every selection is masked, `From_Bytes` may branch on its Boolean result because encodings are public data. Nothing measures timing.
- Performance: since [ADR 0069](../adr/0069-p256-montgomery-multiplication.md) `Mul` is upstream's Montgomery multiplication, sixteen 128-bit products and four reduction steps of shifts and additions: about 50 ns on the author's laptop at `-O3`, against 230 ns for the Solinas form it replaced and 13 ns for upstream's generic code. `Inv` costs 267 multiplications. A specialised squaring remains available behind the same contracts.
