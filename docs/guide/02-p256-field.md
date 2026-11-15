# Chapter 2: the base field of P-256

Package `P256_Field` (`src/p256_field.ads`, `src/p256_field.adb`). It gives the arithmetic of the field of the signature circuit, F_p: addition, subtraction, multiplication in the Montgomery form, inversion, the 32-byte encoding, and the laws of the field that the protocol code uses.

Specification: draft-irtf-cfrg-longfellow-00, Table 1 (p256, FieldID 0x01), Section 7.2.1 (the encoding), Section 3.4.3 (rejection of non-canonical values). Curve constants: RFC 5903 Section 3.1, identical to SEC 2 v2.0 Section 2.4.2. Decisions: [ADR 0012](../adr/0012-p256-limb-representation.md) (limbs), [ADR 0014](../adr/0014-p256-functional-specification-and-ghost-model.md) to [ADR 0017](../adr/0017-p256-test-anchors.md) (the ghost model, canonical form, inversion, test anchors), [ADR 0069](../adr/0069-p256-montgomery-multiplication.md) (the Montgomery form and upstream's multiplication), [ADR 0070](../adr/0070-sumcheck-and-ligero-kernels-as-upstream.md) (scalar limbs and the ring laws), [ADR 0076](../adr/0076-field-operations-without-call-and-finalisation-overhead.md) (bodies without `Big_Integer` terms), [ADR 0077](../adr/0077-p256-montgomery-round-as-cios.md) (the CIOS round).

Before reading: arithmetic modulo a prime and the base field of P-256, in the primer's [A2.2](00-primer-cryptography.md#a22-arithmetic-modulo-a-prime); chapter 1, whose Ada constructs this chapter does not explain again.

## 1. The mathematics

### 1.1 The prime and why this field

The ECDSA signatures on mDoc credentials are over the NIST curve P-256, whose points have coordinates in F_p with

    p = 2^256 - 2^224 + 2^192 + 2^96 - 1
      = FFFFFFFF 00000001 00000000 00000000 00000000 FFFFFFFF FFFFFFFF FFFFFFFF (hex)

(Table 1 of the specification prints it in decimal; RFC 5903 Section 3.1 in hex). The circuits that verify an ECDSA signature inside the zero-knowledge proof ([A10.1](00-primer-cryptography.md#a101-ecdsa-on-p-256)) compute in this field, so the verifier and prover need its arithmetic. It is the *base* field, in which the curve equation y^2 = x^3 - 3x + b lives; it is not the *scalar* field of order n in which signature scalars live (chapter 9). The specification is inconsistent on this point in two places (Section 3.4.3 and Appendix B.3.2 say "scalar field"), but the prime it prints is p.

The shape of p is a Solinas prime: a sum of a few signed powers of two, all multiples of 2^32. The reduction does not use that shape: it is upstream's generic Montgomery round (Section 1.5), which uses one property of p, p = -1 modulo 2^64. Unlike GF(2^128), where addition was xor and there were no carries, F_p is the integers modulo p: addition carries, multiplication produces a 512-bit integer, and every result has to be brought back below p.

### 1.2 Representation and canonical form

An element is an integer in 0 .. p - 1, stored as four 64-bit limbs in little-endian limb order: `L0` is the least significant word, so the value of the limbs L = `Limbs (E)` is

    To_Int (L) = L(0) + L(1) * 2^64 + L(2) * 2^128 + L(3) * 2^192.

Every integer below 2^256 has exactly one such representation, and p < 2^256, so elements have exactly one representation each: this is *canonical form*. Keeping every element canonical makes equality a limb comparison. Serialisation is not a copy of the stored limbs: in the Montgomery form below, the limbs store x R mod p, and `To_Bytes` first converts out of that form, then writes the canonical integer x (Section 2.3). The package enforces it with a type predicate ([ADR 0015](../adr/0015-p256-canonical-form-and-conditional-subtraction.md)): no `Element` can exist whose value is p or more.

**The Montgomery form** ([ADR 0069](../adr/0069-p256-montgomery-multiplication.md)). The element of value x does not store x. It stores x R mod p, with R = 2^256. The stored integer is still canonical, so the two paragraphs above hold for it: one representation per element, equality as a limb comparison. What changes is the meaning of the limbs. Zero stores 0; One stores R mod p = 2^256 - p; the sum of two stored integers is the stored integer of the sum, since (x R + y R) mod p = (x + y) R mod p. Only the product and the boundaries need care: the bytes, the constants and the parsers convert in and out (Sections 2.3 and 3.8).

Serialisation (Section 7.2.1) writes the 32 bytes of the integer least significant byte first, so limb i occupies bytes 8i .. 8i + 7. An encoding whose integer is p or more is not the encoding of any element and is rejected, as upstream's Rust reference implementation does; the specification's sampling rule (Section 3.4.3) assumes the same canonical range.

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

Since p = -1 mod W, the multiplier of p in each round is the low word r of T itself, and T + r p is computed as T + a_i B is: four 128-bit multiply-accumulates with the limbs of p, t_j + r p_j + c, then the carry into the two words above. This is upstream's generic CIOS step ([ADR 0077](../adr/0077-p256-montgomery-round-as-cios.md)). Upstream also has a step that adds r p by shifted copies of r, using the special form of the prime, without a multiplication (`p256_reduction_step`); on the proving machine it is slower than the four multiply-accumulates, and the package does not use it (ADR 0077).

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
      1. row      : T + a_i B, four multiply-accumulates in place (Mac_Row)
      2. reduce   : r the low word; T + r p, the same step with the limbs of p
      3. down     : drop the low word, now zero
    then          : one conditional subtraction of p from the low five words

This is upstream's CIOS step ([ADR 0077](../adr/0077-p256-montgomery-round-as-cios.md)). Since p = -1 mod 2^64, the multiplier of p is the low word itself.

Each round is one procedure (`Round`) with a postcondition on the integer value, and the loop over the four rounds carries the invariant T W^i = a_0..i-1 b + Q p (Section 3.6).

### 2.5 The inversion chain

Write X_k for E^(2^k - 1). As in Chapter 1, X_(a+b) = (X_a)^(2^b) * X_b, so X_2, X_3, X_6, X_12, X_15, X_30 and X_32 = E^(2^32 - 1) are reached with seven multiplications. The exponent p - 2, read as eight 32-bit words, is `ffffffff 00000001 00000000 00000000 00000000 ffffffff ffffffff fffffffd`; starting from R = X_32 (the first word), each further word is appended by 32 squarings followed by a multiplication: by E for `00000001`, by nothing for the three zero words (96 squarings), by X_32 for each `ffffffff`, and for the last word `fffffffd` (thirty ones, then `01`) by X_30 after 30 squarings and by E after 2 more. In total 255 squarings and 12 multiplications, a fixed sequence; the vector generator replays the chain on exponents and checks that it equals p - 2.

## 3. The Ada/SPARK implementation

This section follows `p256_field.ads` and `p256_field.adb` and explains each construct the first time it appears; chapter 1 covered modular types, expression functions, `Ghost`, `Global`, `Post`, `Subprogram_Variant` and loop invariants. The ghost model, the lemmas, the assertions and every contract that mentions the model are at the level `Proof_Only` ([B4.2](00-primer-spark.md#b42-assertion-levels-which-contracts-ever-run), [ADR 0044](../adr/0044-field-contracts-at-proof-only-level.md)): proved for all inputs, never compiled. The type predicate and the contracts that do not mention the model stay executable. The excerpts below leave out the level where it does not matter to the reading.

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

`Ada.Numerics.Big_Numbers.Big_Integers` provides arbitrary-precision integers, which GNATprove understands as mathematical integers (register row T4). `Unsigned_Conversions` is a *generic package*: a template parameterised by a type, here instantiated for `Unsigned_64` to obtain the conversion of a word to its integer value. `Two_64` is written as `Conv (Unsigned_64'Last) + 1` rather than `2 ** 64` because the provers evaluate the conversion of a literal but treat exponentiation as opaque; this detail decided the feasibility experiment behind [ADR 0014](../adr/0014-p256-functional-specification-and-ghost-model.md).

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

`Weight (N)` is 2^(64 N), `Partial (L, N)` the value of the first N words, `To_Int` the value of the whole array, and `P` the prime, defined from its limbs so that no 256-bit literal appears anywhere. Every contract of the package on the arithmetic is a statement about `To_Int`; the few limb-wise ones (`Select_Limbs`, the byte conversions) compare limbs and bytes directly. `Pre` is a *precondition*: GNATprove proves it at every call and assumes it inside the body.

### 3.3 Lemmas

A *lemma* in SPARK is a ghost procedure whose postcondition states a fact and whose body proves it, usually by a sequence of `pragma Assert` ([B3.4](00-primer-spark.md#b34-lemmas-theorems-the-provers-use)). Calling the lemma makes the fact available at the call site. The project accepts no lemma with a null body: that would be an axiom ([ADR 0014](../adr/0014-p256-functional-specification-and-ghost-model.md)). The package has these:

- `Lemma_To_Int_Bounds` (and `Lemma_Partial_Bounds`, by recursion on N): 0 <= `To_Int (L)` < 2^(64 Length). A recursive lemma carries a `Subprogram_Variant` like a recursive function.
- `Lemma_Split`: a 128-bit value equals its low half plus 2^64 times its high half. Proved from `X / 2 ** 64` and `X mod 2 ** 64`, which the provers connect both to the shift and mask forms and to the integer model.
- `Lemma_Mul_Split`: the 128-bit product of two words neither wraps nor exceeds (2^64 - 1)^2, and its value is the product of the values. This is the one place where a nonlinear bound is proved; the provers manage it from the bounds of the factors.
- `Lemma_Add_Step` and `Lemma_Sub_Step`: one word of addition with carry, or subtraction with borrow, extends the prefix identity from K words to K + 1. The addition and subtraction procedures call them once per iteration, so the loop invariant is the lemma's postcondition.
- `Lemma_To_Int_Eq`: two limb arrays that are equal element by element have the same `To_Int`. Stated with a precondition `for all I => A (I) = B (I)` rather than `A = B`, and proved by writing `Partial (A, 4)` and `Partial (B, 4)` out over the four limbs. The fact looks trivial, and it is, but the provers reach it from an array equality only through array extensionality, which they applied in some cold runs and not in others; the element-wise statement is proved every time. It closes `Mont_Mul` and `Mul` (3.6), and the accepted branch of `From_Bytes` (3.8).
- `Lemma_R_Inv`, `Lemma_R2`, `Lemma_P1`, `Lemma_Mac`, `Lemma_Mac_Step`, `Lemma_Two`, `Lemma_Mac_Close`, `Lemma_Down`, `Lemma_Six_Split`, `Lemma_Mont_Final`, `Lemma_To_Mont`, `Lemma_Mod_Multiple`: the multiplication lemmas, described in 3.6 and 3.8.

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

*The row.* `Mac_Row (T, X, B, S)` makes S = T + X B on six words, in place. Each of its four steps is one 128-bit multiply-accumulate, t_j + x b_j + c, which never wraps: (2^64 - 1) + (2^64 - 1)^2 + (2^64 - 1) = 2^128 - 1 (`Lemma_Mac`). `Lemma_Mac_Step` extends the prefix identity by one word, as `Lemma_Add_Step` does for the addition. The carry then goes into the two words above with `Add_Words`, and `Lemma_Mac_Close` puts the six words together; the bound on T + X B makes the last carry zero. The body holds no `Big_Integer` term: the identity is in the lemmas (ADR 0076).

*The round.* `Round (T, X, B, R)` takes a six-word accumulator below 2p, and its postcondition is

```ada
     Post => (Proof_Only => To_Int (T) < 2 * P
              and then To_Int (T) * Two_64
                       = To_Int (T'Old) + Conv (X) * To_Int (B) + Conv (R) * P);
```

The body is three calls: `Mac_Row` adds X B, `Mac_Row` adds r p with the limbs of p, and `Down` drops the low word. The proof states, at each call, why the value stays below 2^384. The low word is then zero: with p = W P1 - 1 (`Lemma_P1`), the value is W times an integer, and `Lemma_Digit`, the uniqueness of a base-W digit, makes the low word 0. `Lemma_Div_Bound` carries the bound below 2p from T W to T.

*The rounds.* `Mont_Mul` loops over the four words of A with a ghost `Q : Big_Integer` and the invariant

```ada
   To_Int (T) < 2 * P and then To_Int (T) * Weight (I)
                               = Partial (A, I) * To_Int (B) + Q * P
```

After the loop, `Lemma_Six_Split` shows that word 5 is zero and word 4 at most one, and the conditional subtraction of Section 2.2 gives a result below p, equal to T or T - p. It is written branch by branch, with `Lemma_To_Int_Eq` for the selected array, as in `Add`. `Lemma_Mont_Final` closes. From T 2^256 = A B + Q p and 2^256 R_Inv = 1 + K p, the result is A B R_Inv plus a multiple of p, and lies in 0 .. p - 1, so `Lemma_Mod_Multiple` makes it A B R_Inv mod p. `Mul` returns `Of_Limbs (Mont_Mul (Limbs (A), Limbs (B)))`; `Square` is `Mul (E, E)`.

*Associativity.* `Lemma_Mul_Assoc` ([ADR 0066](../adr/0066-lagrange-tables-by-prefix-and-suffix.md), which needs it) meets the factor R_Inv twice on each side: both products are X Y Z R_Inv^2 mod p, by `Lemma_Mod_Mul` twice, and `Lemma_Inj` turns equal integers into equal elements.

*The other ring laws* (ADR 0070): commutativity, `One` as unit, distributivity over `Add` and `Sub`, and the laws of `Add`, `Neg` and `Sub` that the sumcheck kernels use. Each is proved the same way: the two sides have the same integer mod p, and `Lemma_Inj` makes them equal elements. `Field_P256` restates them with `Same` ([B4.4](00-primer-spark.md#b44-logical-equality-same)), through `Laws.Lemma_Same`, which needs nothing more than `X = Y` since the limbs are scalar components; chapter 3 Section 3.1 describes that package.

A ghost variable (`Q : Big_Integer with Ghost`) exists only for proof and is never compiled; square-bracket aggregates `[a, b, c]` are the Ada 2022 array notation; `A (0 .. 7)` is a *slice*, a contiguous part of an array. `Add_Words`, `Sub_Words`, `Mac_Row` and `Round` are `Inline`, so that the compiler sees their lengths and unrolls the loops.

### 3.7 Inv

`Square_N (E, N)` squares N times in a loop; `Inv` is the chain of Section 2.5 as thirteen constant declarations and a final `Mul`, with no loop over exponent bits and no `if`. Its only contract is `Global => null`: Silver, by decision ([ADR 0016](../adr/0016-p256-inversion.md)).

### 3.8 Encoding

`Limb_Of_8` assembles a word from eight bytes by shifts and `or`; `Bytes_Of_Limb` extracts them with `Byte_Of`, and its postcondition is the 64-bit round trip. `Limbs_Of_Bytes` and `Bytes_Of_Limbs` work on four slices of the 32-byte array, so the 256-bit round trip in the postcondition of `Bytes_Of_Limbs` composes from the 64-bit one. `From_Bytes` decodes, tests canonical form with `Sub_Limbs`, selects the limbs or zero through the masked selection, and stores `Mont_Mul (S, R2)`. `Lemma_R2` proves R2 R_Inv = 2^256 + K2 p for the constant R2 = 2^512 mod p, and `Lemma_To_Mont` turns that into (S R2 R_Inv) mod p = (S 2^256) mod p. The postcondition says which encodings are accepted, that a refused one gives `Zero`, and that an accepted one stores its integer times 2^256 mod p. Its first part, `Ok = Is_Canonical (...)` and the `Zero` of a refused encoding, is at the level `Runtime`, a cheap check compiled in every build, the release build included; the second part, about the integer, is at `Proof_Only`. Where `From_Bytes` decodes a secret value, the time of that check can reveal whether the value is canonical: these are the declared exceptions to the rule that `Runtime` checks are on public values ([chapter 4 Section 3.2, "Assertion levels"](04-transcript.md#assertion-levels-and-the-checks-kept-in-every-build), register row S4). `To_Canonical (E)` is `Mont_Mul (Limbs (E), [1, 0, 0, 0])`, the integer E R_Inv mod p below p, and `To_Bytes` encodes it. `From_Canonical (L)`, for constants and parsers, and `Of_Natural (X)` are `Mont_Mul` by R2 again.

## 4. What the proofs guarantee

The proof of the package, from a run of the partition `p256` ([B6.5](00-primer-spark.md#b65-partitions-and-the-whole)) on the proving machine:

- **commit** 4f1e104 (main), proof inputs `be44efe9bc9d` (`scripts/remote-check.sh --digest`);
- **toolchain** GNATprove 16.1.0 with gnat_native 16.1.0 (Alire); the prover configuration of `package Prove` in the project file, CVC5, Z3 and Alt-Ergo with `--steps=600000` and `--timeout=120` ([ADR 0020](../adr/0020-prover-configuration-step-budget.md));
- **command** `make prove-partition PARTITION=p256`;
- **run** 14 November 2026, on the proving machine, from a clean session: proved, not reused from an earlier proof.

| Check | `P256_Field` | Discharged by |
|-------|--------------|---------------|
| Data dependencies (`Global`) | 90 | flow analysis |
| Initialisation | 26 | flow analysis |
| Termination | 34 | flow analysis |
| Range checks | 22 | provers |
| Division checks (`/`, `mod`) | 90 | provers |
| Overflow checks | 33 | provers |
| Index checks | 46 | provers |
| Length checks | 2 | provers |
| Type predicates | 1735 | provers |
| Preconditions of the calls | 640 | provers |
| Assertions | 221 | provers |
| Loop invariants (base case and preservation) | 16 | provers |
| Postconditions | 77 | provers |
| Variants of the recursive functions | 3 | provers |
| **Total** | **3035** | all proved: none justified, none unproved, no `pragma Assume` |

Most of the checks the provers discharge are type predicates: every `Element` carries the canonical-form predicate (Section 3.1), checked wherever an element is built or passed.

How to read the table: [B6.4](00-primer-spark.md#b64-reading-the-summary-table). The summary GNATprove prints covers the three units of the partition, 3,078 checks; the table gives `P256_Field`. `Field_P256` and its laws, the other two, are counted in chapter 3.

Z3 and CVC5 share almost every check the provers discharge, and which of the two is credited with one varies from run to run, since the first to answer wins. Alt-Ergo closes a few polynomial normalisation steps and bridges between modular words and the integer model (ADR 0020).

The flow analysis prints no warning for the units of this chapter.

In plain terms, for every input, not on samples:

- no run-time error occurs anywhere in the package;
- every `Element` holds an integer in 0 .. p - 1, and `Is_Canonical` decides exactly that;
- `To_Int (Add (A, B)) = (To_Int (A) + To_Int (B)) mod p`, and likewise for `Sub` and `Neg`; `To_Int (Mul (A, B)) = To_Int (A) To_Int (B) 2^-256 mod p`, and likewise for `Square`, so that in the Montgomery form the elements add and multiply as the field does;
- the product is associative and commutative with `One` as unit and distributes over `Add` and `Sub`; the sum is associative and commutative with `Zero` as unit, `Neg` gives the opposite and `Sub (A, B)` is `Add (A, Neg (B))`;
- `From_Bytes` accepts an encoding exactly when its integer x is below p and then stores x 2^256 mod p, a refused encoding gives `Zero`; `To_Canonical` returns the integer back, below p, and `To_Bytes` encodes it;
- every subprogram terminates.

Reproduce with:

```bash
make prove-partition PARTITION=p256
python3 -I scripts/vc-count.py --partition p256 p256_field
```

The first command proves the partition and prints GNATprove's summary. The second checks that the files are those of a run of that partition and that its units add up to the summary, then prints the table from the files GNATprove writes for each unit (`obj/development/gnatprove/<unit>.spark`) and says whether any check is unproved or justified or any unit has a `pragma Assume`. Its line "discharged by the provers" is also the sum of the counts per subprogram of `obj/development/gnatprove/gnatprove.out` for the unit. The lessons of these proofs are in the verification approach, "Lessons of the proofs".

## 5. What is only tested

The proofs relate the code to the model and the model to the polynomial form of p. They do not say that `P_Limbs` is the prime of Table 1 (a wrong limb would move `P` and every proof would still succeed), nor that the byte order is the one of Section 7.2.1, nor that `Inv` inverts. The vectors cover these ([ADR 0017](../adr/0017-p256-test-anchors.md)), run by the harness `p256_kat` in the test build:

| File | Cases | External anchors |
|------|-------|------------------|
| `p256_add.txt` | 221 | add, sub, neg on b, Gx, Gy, p - 1 and the inverse of two (RFC 5903 Section 3.1) |
| `p256_mul.txt` | 139 | the intermediate products of Gy^2 = Gx^3 - 3 Gx + b, composed by the generator; (p - 1)^2 = 1; 2^128 * 2^128 = 2^256 mod p; one product per 32-bit word position of the 512-bit product |
| `p256_inv.txt` | 46 | inv 1, inv 2 = (p + 1) / 2, inv (p - 1), the inverses of Gx, Gy and b; `Inv (Zero) = Zero`; Fermat and Euclid references agree, and the harness re-checks E * Inv (E) = One |
| `p256_bytes.txt` | 61 | the encodings of b, Gx, Gy; p - 1 accepted, p, p + 1, 2^256 - 1 rejected; `To_Bytes` round trip |

Why the curve equation is an external anchor: b, Gx and Gy were published by NIST and are used by every P-256 implementation; the identity Gy^2 = Gx^3 - 3 Gx + b holds only for the right prime, the right reduction and the right byte order at once, and its three operands were produced by nobody involved in this code. The generator refuses to write the files if the identity fails for its own reference. It also replays the inversion chain on exponents and checks that it computes p - 2.

The Appendix B vectors of the specification are not field anchors: B.2 states a secp256k1 prime, and B.3.2 mislabels the field; both are logged as specification issues ([ADR 0002](../adr/0002-pin-the-specification.md)).

Reproduce with:

```bash
alr exec -- gprbuild -P tests/longfellow_spark_tests.gpr -p
tests/bin/p256_kat
```

The harness reads the four files by default, or the files given on its command line. Its last lines give the checks by section, each file and, in a file with more than one kind of line, each kind, then the total:

```text
checks by section:
  tests/vectors/p256_add.txt: passed 221, failed 0
    add: passed 78, failed 0
    sub: passed 73, failed 0
    neg: passed 70, failed 0
  tests/vectors/p256_mul.txt: passed 139, failed 0
    mul: passed 95, failed 0
    square: passed 44, failed 0
  tests/vectors/p256_inv.txt: passed 46, failed 0
  tests/vectors/p256_bytes.txt: passed 61, failed 0
passed 467, failed 0
```

The ghost model, the lemmas and the contracts that mention them are at the level `Proof_Only` and do not run in the test build; the type predicate of `Element` does, and what the harness checks of the arithmetic is its results against the vectors.

## 6. What stays trusted, and the limits

- Fermat's little theorem for `Inv`, and the exponent arithmetic of the chain, checked by the generator, not proved in SPARK (register row V3).
- GNATprove's model of `Ada.Numerics.Big_Numbers.Big_Integers` and of the conversions from modular types is the mathematical integers (T4). Every contract of the package that mentions the model, `To_Int` of the limbs, is a statement about it.
- The compiler and the builder, including the 128-bit arithmetic (T1), GNATprove (T2) and the SMT solvers (T3). The release build compiles the package without run-time checks and relies on the proof instead (T7).
- The contracts at the level `Proof_Only`, every contract that mentions the model ([ADR 0044](../adr/0044-field-contracts-at-proof-only-level.md)), are proved and never compiled, so that the compiled code has the properties GNATprove proved of the source is trusted (T8). The limb-wise contracts (`Select_Limbs`, `To_Bytes`) and the type predicate of `Element` are executable and run in the test build; the part of `From_Bytes` at the level `Runtime` runs in every build.
- The prime, the encoding and the sampling rule transcribe the pinned specification, which is trusted to describe the intended protocol (R1).
- The target is 64-bit: `Unsigned_128` is required ([ADR 0012](../adr/0012-p256-limb-representation.md), P3).
- Constant time is a discipline, scoped to the release build ([ADR 0006](../adr/0006-constant-time-discipline-and-scope.md), [A12.3](00-primer-cryptography.md#a123-the-observer-of-timing), S4): loop bounds and table indices are compile-time constants, every selection is masked. The `Runtime` part of the postcondition of `From_Bytes` runs in every build (Section 3.8). Nothing measures timing.
- `Mul` is upstream's Montgomery multiplication with the CIOS step, thirty-two 128-bit multiply-accumulates; `Inv` costs 267 multiplications. [The performance page](performance.md) compares their times with upstream's.
