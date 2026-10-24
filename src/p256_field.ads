--  P256_Field: arithmetic in the base field F_p of NIST P-256,
--  p = 2^256 - 2^224 + 2^192 + 2^96 - 1, used by the Longfellow ZK
--  ECDSA-related circuits.
--
--  Documentation: docs/guide/02-p256-field.md. Decisions implemented
--  here: ADR 0012 (four 64-bit limbs, Unsigned_128 products), 0069
--  (Montgomery form, the multiplication of upstream; it replaces the
--  direct representation and the Solinas reduction of ADR 0013), 0014
--  (ghost big-integer model, lemma policy), 0015 (canonical form
--  predicate, constant-time conditional subtraction), 0016 (Inv), 0017
--  (test anchors); frame: ADR 0002, 0003, 0006, 0020. Index:
--  docs/adr/README.md.
--
--  Proof status (Silver = absence of run-time errors, Gold = proved
--  functional contracts against the ghost model To_Int). All the
--  verification conditions of this package are discharged by GNATprove
--  with the project's proof switches (package Prove in
--  longfellow_spark.gpr, ADR 0020: the level 2 provers with a step
--  budget), with no justification and no pragma Assume; see
--  docs/guide/02-p256-field.md for the table.
--
--    Is_Canonical : Gold, equals To_Int (L) < P.
--    Add, Sub     : Gold, the stored integer is the sum or difference
--                   mod P, hence so is the element.
--    Neg          : Gold by composition over Sub.
--    Mul          : Gold, the stored integer is A B 2^-256 mod P, the
--                   Montgomery product of upstream (ADR 0069), hence
--                   the element is the product.
--    Square       : Gold by composition over Mul.
--    From_Bytes   : Gold, accepts exactly the canonical encodings and
--                   stores their value times 2^256 mod P; To_Bytes
--                   gives the value back (To_Canonical).
--    From_Canonical, To_Canonical, Of_Natural : Gold, the conversions
--                   into and out of the Montgomery form.
--    Inv          : Silver only (AoRTE), plus known-answer tests
--                   (tests/vectors/p256_inv.txt). Fermat correctness
--                   is out of SMT reach by design decision (ADR 0016).
--                   Inv is total: Inv (Zero) = Zero, consistent with
--                   GF2_128 (ADR 0008); the upstream Rust reference
--                   asserts on zero and the upstream C++ returns zero.
--
--  Pinned spec: IETF draft-google-cfrg-libzk-03 (23 September 2026),
--  Table 1 (p256, FieldID 0x01, the base field of NIST P-256), Section
--  7.2.1 (32 bytes, little-endian, canonical) and Section 3.4.3
--  (values >= p rejected). Curve constants for tests: RFC 5903
--  Section 3.1 (identical to SEC 2 v2.0 Section 2.4.2).
--
--  Representation (ADR 0069): the element of value x stores the
--  integer x 2^256 mod p, the Montgomery form, in four 64-bit limbs,
--  little-endian limb order, always canonical (below p, enforced by
--  the type predicate). The limbs are four scalar components, L0 to
--  L3 (ADR 0070); Limbs gives them as a word array. Equal elements
--  have equal limbs. Constants and
--  parsers outside the package go through From_Canonical and
--  To_Canonical, never through the limbs.
--  Partial sums are formed in Unsigned_128 so that no step wraps; the
--  ghost model To_Int maps word arrays to the integer they denote.
--
--  Assertion level (ADR 0044): the ghost model, the lemmas, the
--  assertions and loop invariants of the body and every contract that
--  mentions the model are at the level Proof_Only (Proof_Levels):
--  proved for all inputs by GNATprove, never compiled in any build.
--  The type predicate (Is_Canonical, a four-limb subtraction) and the
--  contracts that do not mention the model stay executable. What the
--  test build checks of the arithmetic is its result against the
--  vectors (tests/vectors/p256_*.txt).
--
--  Constant-time discipline (ADR 0006): no secret-dependent branching
--  or indexing in executable code; selections use arithmetic masks;
--  if-expressions appear only in contracts and ghost code; loop bounds
--  and table indices are compile-time constants. The guarantee is
--  scoped to builds with assertions disabled, where the remaining
--  executable contracts and the type predicate do not run.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Bytes;
with Proof_Levels;
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

package P256_Field is

   --  Word arrays of up to eight 64-bit words, least significant first.
   Max_Words : constant := 8;
   type Word_Array is array (Natural range <>) of Unsigned_64;

   subtype Limb_Index is Natural range 0 .. 3;
   subtype Limb_Array is Word_Array (Limb_Index);     --  256 bits
   subtype Five_Array is Word_Array (0 .. 4);         --  320 bits

   --  p = 2^256 - 2^224 + 2^192 + 2^96 - 1 as limbs (draft-03 Table 1;
   --  RFC 5903 Section 3.1).
   P_Limbs : constant Limb_Array :=
     [0 => 16#FFFF_FFFF_FFFF_FFFF#,
      1 => 16#0000_0000_FFFF_FFFF#,
      2 => 16#0000_0000_0000_0000#,
      3 => 16#FFFF_FFFF_0000_0001#];

   -------------------------------------------------------------------
   --  Ghost model: the integer denoted by a word array.
   -------------------------------------------------------------------

   package U64_Conv is new Unsigned_Conversions (Unsigned_64);
   package U128_Conv is new Unsigned_Conversions (Unsigned_128);

   function Conv (X : Unsigned_64) return Big_Integer is
     (U64_Conv.To_Big_Integer (X))
   with Ghost => Proof_Only, Global => null;

   function Conv128 (X : Unsigned_128) return Big_Integer is
     (U128_Conv.To_Big_Integer (X))
   with Ghost => Proof_Only, Global => null;

   Two_32 : constant Big_Integer := Conv (16#1_0000_0000#)
     with Ghost => Proof_Only;
   Two_64 : constant Big_Integer := Conv (Unsigned_64'Last) + 1
     with Ghost => Proof_Only;

   --  2^(64 N) for N in 0 .. 8.
   function Weight (N : Natural) return Big_Integer is
     (if N = 0 then To_Big_Integer (1) else Two_64 * Weight (N - 1))
   with Ghost => Proof_Only, Global => null,
        Pre => N <= Max_Words,
        Subprogram_Variant => (Decreases => N);

   --  Value of words 0 .. N - 1 (N = 0: empty sum).
   function Partial (L : Word_Array; N : Natural) return Big_Integer is
     (if N = 0 then To_Big_Integer (0)
      else Partial (L, N - 1) + Conv (L (N - 1)) * Weight (N - 1))
   with Ghost => Proof_Only, Global => null,
        Pre => L'First = 0
          and then (N = 0 or else N - 1 <= L'Last)
          and then N <= Max_Words,
        Subprogram_Variant => (Decreases => N);

   function To_Int (L : Word_Array) return Big_Integer is
     (Partial (L, L'Length))
   with Ghost => Proof_Only, Global => null,
        Pre => L'First = 0 and then L'Length <= Max_Words;

   Two_256 : constant Big_Integer := Weight (4) with Ghost => Proof_Only;
   P       : constant Big_Integer := To_Int (P_Limbs) with Ghost => Proof_Only;

   --  Every word array denotes a value in 0 .. 2^(64 Length) - 1.
   procedure Lemma_To_Int_Bounds (L : Word_Array) with
     Ghost => Proof_Only, Global => null,
     Pre  => L'First = 0 and then L'Length <= Max_Words,
     Post => To_Int (L) >= 0 and then To_Int (L) < Weight (L'Length);

   -------------------------------------------------------------------
   --  Word-level primitives, constant time, exact against the model.
   -------------------------------------------------------------------

   function Lo (X : Unsigned_128) return Unsigned_64 is
     (Unsigned_64 (X and 16#FFFF_FFFF_FFFF_FFFF#))
   with Global => null;

   function Hi (X : Unsigned_128) return Unsigned_64 is
     (Unsigned_64 (Shift_Right (X, 64)))
   with Global => null;

   --  A 128-bit value is its halves weighted by 2^64.
   procedure Lemma_Split (X : Unsigned_128) with
     Ghost => Proof_Only, Global => null,
     Post => Conv128 (X) = Conv (Lo (X)) + Conv (Hi (X)) * Two_64;

   --  A + B word by word; Carry is the bit of weight 2^(64 Length).
   procedure Add_Words
     (A, B : Word_Array; R : out Word_Array; Carry : out Unsigned_64)
   with
     Global => null,
     Inline,
     Pre  => A'First = 0 and then B'First = 0 and then R'First = 0
       and then A'Length = B'Length and then R'Length = A'Length
       and then A'Length in 1 .. Max_Words,
     Post => (Proof_Only => Carry <= 1
       and then To_Int (R) + Conv (Carry) * Weight (A'Length)
                = To_Int (A) + To_Int (B));

   --  A - B word by word; Borrow is 1 iff A < B, and the words denote
   --  A - B + Borrow * 2^(64 Length).
   procedure Sub_Words
     (A, B : Word_Array; R : out Word_Array; Borrow : out Unsigned_64)
   with
     Global => null,
     Inline,
     Pre  => A'First = 0 and then B'First = 0 and then R'First = 0
       and then A'Length = B'Length and then R'Length = A'Length
       and then A'Length in 1 .. Max_Words,
     Post => (Proof_Only => Borrow <= 1
       and then To_Int (R)
                = To_Int (A) - To_Int (B) + Conv (Borrow) * Weight (A'Length)
       and then (Borrow = 1) = (To_Int (A) < To_Int (B)));

   type Limbs_With_Carry is record
      Limbs : Limb_Array;
      Carry : Unsigned_64;   --  0 or 1
   end record;

   function Add_Limbs (A, B : Limb_Array) return Limbs_With_Carry with
     Global => null,
     Inline,
     Post   => (Proof_Only => Add_Limbs'Result.Carry <= 1
       and then To_Int (Add_Limbs'Result.Limbs)
                  + Conv (Add_Limbs'Result.Carry) * Two_256
                = To_Int (A) + To_Int (B));

   function Sub_Limbs (A, B : Limb_Array) return Limbs_With_Carry with
     Global => null,
     Inline,
     Post   => (Proof_Only => Sub_Limbs'Result.Carry <= 1
       and then To_Int (Sub_Limbs'Result.Limbs)
                = To_Int (A) - To_Int (B)
                  + Conv (Sub_Limbs'Result.Carry) * Two_256
       and then (Sub_Limbs'Result.Carry = 1) = (To_Int (A) < To_Int (B)));

   --  Limb-wise selection: B where Mask is all ones, A where it is zero.
   function Select_Limbs (A, B : Limb_Array; Mask : Unsigned_64)
     return Limb_Array
   with Global => null,
        Pre  => Mask = 0 or else Mask = Unsigned_64'Last,
        Post => Select_Limbs'Result = (if Mask = 0 then A else B);

   -------------------------------------------------------------------
   --  Field elements.
   -------------------------------------------------------------------

   --  Branch-free test L < p, computed by the borrow of L - p.
   function Is_Canonical (L : Limb_Array) return Boolean is
     (Sub_Limbs (L, P_Limbs).Carry = 1)
   with Global => null,
        Post => (Proof_Only => Is_Canonical'Result = (To_Int (L) < P));

   --  The canonical test on four scalar limbs, for the type predicate.
   --  Its body is hidden from the provers outside the subprograms that
   --  unhide it: elsewhere the predicate stays an opaque fact, carried
   --  by every element at no cost. The postcondition gives the case of
   --  a top limb below that of p, enough for Zero and One.
   function Canonical_Limbs (L0, L1, L2, L3 : Unsigned_64) return Boolean
   is (Is_Canonical ([L0, L1, L2, L3]))
   with Global => null,
        Post => (if L3 < 16#FFFF_FFFF_0000_0001# then Canonical_Limbs'Result),
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   --  The four limbs of an element, as four scalar components rather
   --  than an array (ADR 0070): the provers treat a record of scalars
   --  as a datatype, so that equal limbs give equal elements with no
   --  further fact, while an array component is a map over Natural.
   --  The memory layout is the same, four words, least significant
   --  first, as the limb_ array of upstream's Nat.
   type Element is record
      L0, L1, L2, L3 : Unsigned_64;
   end record
   with Dynamic_Predicate =>
     Canonical_Limbs (Element.L0, Element.L1, Element.L2, Element.L3);

   --  The limbs as a word array, for the arithmetic. The provers see
   --  the postcondition, limb by limb, not the aggregate of the body,
   --  which would weigh on every element in every proof.
   function Limbs (E : Element) return Limb_Array is
     ([E.L0, E.L1, E.L2, E.L3])
   with Global => null,
        Post => Limbs'Result (0) = E.L0 and then Limbs'Result (1) = E.L1
                and then Limbs'Result (2) = E.L2
                and then Limbs'Result (3) = E.L3,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   --  Zero stores 0, One stores 2^256 mod p = 2^256 - p.
   Zero : constant Element := (L0 => 0, L1 => 0, L2 => 0, L3 => 0);
   One  : constant Element :=
     (L0 => 16#0000_0000_0000_0001#, L1 => 16#FFFF_FFFF_0000_0000#,
      L2 => 16#FFFF_FFFF_FFFF_FFFF#, L3 => 16#0000_0000_FFFF_FFFE#);

   --  2^-256 mod p, the factor of the Montgomery product, and K with
   --  2^256 R_Inv = 1 + K p.
   RI_Limbs : constant Limb_Array :=
     [16#0000_0003_0000_0000#, 16#0000_0001_FFFF_FFFE#,
      16#FFFF_FFFD_0000_0002#, 16#FFFF_FFFE_0000_0003#]
   with Ghost => Proof_Only;
   K_Limbs : constant Limb_Array :=
     [16#0000_0000_0000_0001#, 16#0000_0001_0000_0000#,
      16#0000_0000_0000_0000#, 16#FFFF_FFFF_0000_0002#]
   with Ghost => Proof_Only;
   R_Inv : constant Big_Integer := To_Int (RI_Limbs) with Ghost => Proof_Only;

   procedure Lemma_R_Inv with
     Ghost => Proof_Only, Global => null,
     Post => Two_256 * R_Inv = 1 + To_Int (K_Limbs) * P;

   function Add (A, B : Element) return Element with
     Global => null,
     Post   => (Proof_Only => To_Int (Limbs (Add'Result))
               = (To_Int (Limbs (A)) + To_Int (Limbs (B))) mod P);

   function Sub (A, B : Element) return Element with
     Global => null,
     Post   => (Proof_Only => To_Int (Limbs (Sub'Result))
               = (To_Int (Limbs (A)) - To_Int (Limbs (B))) mod P);

   function Neg (A : Element) return Element is (Sub (Zero, A)) with
     Global => null,
     Post   =>
       (Proof_Only =>
          To_Int (Limbs (Neg'Result)) = (-To_Int (Limbs (A))) mod P);

   --  The Montgomery product: the stored integers multiply with the
   --  factor 2^-256, so that the elements multiply.
   function Mul (A, B : Element) return Element with
     Global => null,
     Post   => (Proof_Only => To_Int (Limbs (Mul'Result))
               = (To_Int (Limbs (A)) * To_Int (Limbs (B)) * R_Inv) mod P);

   --  The product is associative (ADR 0066), the law the Lagrange
   --  tables need; proved from the model.
   procedure Lemma_Mul_Assoc (A, B, C : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul (Mul (A, B), C) = Mul (A, Mul (B, C));

   --  The other ring laws the sumcheck kernels need (ADR 0070), proved
   --  from the model like associativity.
   procedure Lemma_Mul_Comm (A, B : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul (A, B) = Mul (B, A);

   procedure Lemma_Mul_One (A : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul (A, One) = A;

   procedure Lemma_Mul_Distrib (A, B, C : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul (A, Add (B, C)) = Add (Mul (A, B), Mul (A, C));

   procedure Lemma_Mul_Distrib_Sub (A, B, C : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul (A, Sub (B, C)) = Sub (Mul (A, B), Mul (A, C));

   procedure Lemma_Add_Assoc (A, B, C : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Add (Add (A, B), C) = Add (A, Add (B, C));

   procedure Lemma_Add_Comm (A, B : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Add (A, B) = Add (B, A);

   procedure Lemma_Add_Zero (A : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Add (A, Zero) = A;

   procedure Lemma_Add_Neg (A : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Add (A, Neg (A)) = Zero;

   procedure Lemma_Sub_Def (A, B : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Sub (A, B) = Add (A, Neg (B));

   function Square (E : Element) return Element is (Mul (E, E)) with
     Global => null,
     Post   => (Proof_Only => To_Int (Limbs (Square'Result))
               = (To_Int (Limbs (E)) * To_Int (Limbs (E)) * R_Inv) mod P);

   --  Multiplicative inverse by Fermat: E^(p - 2), computed with a
   --  fixed addition chain (255 squarings, 12 multiplications, no
   --  data-dependent control flow; the chain is checked against p - 2
   --  by the vector generator). Total function: Inv (Zero) = Zero.
   --  Silver only; E * Inv (E) = One is anchored by known-answer tests.
   function Inv (E : Element) return Element with
     Global => null;

   -------------------------------------------------------------------
   --  Encoding (draft-03 Section 7.2.1): 32 bytes, least significant
   --  byte first; limb I occupies bytes 8 I .. 8 I + 7.
   -------------------------------------------------------------------

   --  The byte type is the shared one of package Bytes (ADR 0028);
   --  these subtypes keep the stage 2 contracts unchanged.
   subtype Byte_Array is Bytes.Byte_Array;
   subtype Bytes_32 is Bytes.Bytes_32;
   subtype Bytes_8  is Bytes.Bytes_8;

   --  One limb from eight bytes, least significant first.
   function Limb_Of_8 (B : Bytes_8) return Unsigned_64 with
     Global => null;

   function Limbs_Of_Bytes (B : Bytes_32) return Limb_Array with
     Global => null;

   function Bytes_Of_Limbs (L : Limb_Array) return Bytes_32 with
     Global => null,
     Post   => Limbs_Of_Bytes (Bytes_Of_Limbs'Result) = L;

   --  The element of the integer of L, reduced mod p: its Montgomery
   --  form. For constants and parsers.
   function From_Canonical (L : Limb_Array) return Element with
     Global => null,
     Post   => (Proof_Only => To_Int (Limbs (From_Canonical'Result))
               = (To_Int (L) * Two_256) mod P);

   --  The canonical integer of E, below p.
   function To_Canonical (E : Element) return Limb_Array with
     Global => null,
     Post   => (Proof_Only => To_Int (To_Canonical'Result) < P
               and then To_Int (To_Canonical'Result)
                        = (To_Int (Limbs (E)) * R_Inv) mod P);

   --  Ok iff the encoding is canonical (value < p); then E denotes it.
   --  On rejection E is Zero.
   procedure From_Bytes (B : Bytes_32; E : out Element; Ok : out Boolean)
   with
     Global => null,
     Post   =>
       (Runtime    => Ok = Is_Canonical (Limbs_Of_Bytes (B))
                      and then (if not Ok then E = Zero),
        Proof_Only => (if Ok then To_Int (Limbs (E))
                         = (To_Int (Limbs_Of_Bytes (B)) * Two_256) mod P));

   function To_Bytes (E : Element) return Bytes_32 is
     (Bytes_Of_Limbs (To_Canonical (E)))
   with Global => null,
        Post   => Limbs_Of_Bytes (To_Bytes'Result) = To_Canonical (E);

   --  The element X for a natural X (stage 5: the Reed-Solomon
   --  evaluation point x of the Ligero code, reed_solomon_eval_point).
   function Of_Natural (X : Natural) return Element with
     Global => null,
     Post   => (Proof_Only => To_Int (Limbs (Of_Natural'Result))
               = (To_Big_Integer (X) * Two_256) mod P);

end P256_Field;
