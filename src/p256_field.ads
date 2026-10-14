--  P256_Field: arithmetic in the base field F_p of NIST P-256,
--  p = 2^256 - 2^224 + 2^192 + 2^96 - 1, used by the Longfellow ZK
--  ECDSA-related circuits.
--
--  Documentation: docs/guide/02-p256-field.md. Decisions implemented
--  here: ADR 0012 (four 64-bit limbs, Unsigned_128 products), 0013
--  (direct representation, Solinas reduction), 0014 (ghost big-integer
--  model, lemma policy), 0015 (canonical form predicate, constant-time
--  conditional subtraction), 0016 (Inv), 0017 (test anchors); frame:
--  ADR 0002, 0003, 0006, 0020. Index: docs/adr/README.md.
--
--  Proof status (Silver = absence of run-time errors, Gold = proved
--  functional contracts against the ghost model To_Int). Stage 2 of
--  Phase A is complete: all verification conditions of this package
--  (3653 checks) are discharged by GNATprove with the project's proof
--  switches (package Prove in longfellow_spark.gpr, ADR 0020: the
--  level 2 provers with a step budget), with no justification and no
--  pragma Assume; see docs/guide/02-p256-field.md for the table.
--
--    Is_Canonical : Gold, equals To_Int (L) < P.
--    Add, Sub     : Gold, result value is the sum or difference mod P.
--    Neg          : Gold by composition over Sub.
--    Mul          : Gold, result value is the product mod P, through
--                   the staged Solinas reduction of ADR 0013.
--    Square       : Gold by composition over Mul.
--    From_Bytes   : Gold, accepts exactly the canonical encodings and
--                   returns their value; To_Bytes round-trips.
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
--  Representation: four 64-bit limbs, little-endian limb order, always
--  in canonical form (value < p, enforced by the type predicate).
--  Partial sums are formed in Unsigned_128 so that no step wraps; the
--  ghost model To_Int maps word arrays to the integer they denote.
--
--  Constant-time discipline (ADR 0006): no secret-dependent branching
--  or indexing in executable code; selections use arithmetic masks;
--  if-expressions appear only in contracts and ghost code; loop bounds
--  and table indices are compile-time constants. The guarantee is
--  scoped to builds with assertions disabled; the ghost model executes
--  Big_Integer arithmetic when assertions are enabled.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Bytes;
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;

package P256_Field is

   --  Word arrays of up to eight 64-bit words, least significant first.
   Max_Words : constant := 8;
   type Word_Array is array (Natural range <>) of Unsigned_64;

   subtype Limb_Index is Natural range 0 .. 3;
   subtype Limb_Array is Word_Array (Limb_Index);     --  256 bits
   subtype Five_Array is Word_Array (0 .. 4);         --  320 bits
   subtype Wide_Array is Word_Array (0 .. 7);         --  512 bits

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
   with Ghost, Global => null;

   function Conv128 (X : Unsigned_128) return Big_Integer is
     (U128_Conv.To_Big_Integer (X))
   with Ghost, Global => null;

   Two_32 : constant Big_Integer := Conv (16#1_0000_0000#) with Ghost;
   Two_64 : constant Big_Integer := Conv (Unsigned_64'Last) + 1 with Ghost;

   --  2^(64 N) for N in 0 .. 8.
   function Weight (N : Natural) return Big_Integer is
     (if N = 0 then To_Big_Integer (1) else Two_64 * Weight (N - 1))
   with Ghost, Global => null,
        Pre => N <= Max_Words,
        Subprogram_Variant => (Decreases => N);

   --  Value of words 0 .. N - 1 (N = 0: empty sum).
   function Partial (L : Word_Array; N : Natural) return Big_Integer is
     (if N = 0 then To_Big_Integer (0)
      else Partial (L, N - 1) + Conv (L (N - 1)) * Weight (N - 1))
   with Ghost, Global => null,
        Pre => L'First = 0
          and then (N = 0 or else N - 1 <= L'Last)
          and then N <= Max_Words,
        Subprogram_Variant => (Decreases => N);

   function To_Int (L : Word_Array) return Big_Integer is
     (Partial (L, L'Length))
   with Ghost, Global => null,
        Pre => L'First = 0 and then L'Length <= Max_Words;

   Two_256 : constant Big_Integer := Weight (4) with Ghost;
   P       : constant Big_Integer := To_Int (P_Limbs) with Ghost;

   --  Every word array denotes a value in 0 .. 2^(64 Length) - 1.
   procedure Lemma_To_Int_Bounds (L : Word_Array) with
     Ghost, Global => null,
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
     Ghost, Global => null,
     Post => Conv128 (X) = Conv (Lo (X)) + Conv (Hi (X)) * Two_64;

   --  A + B word by word; Carry is the bit of weight 2^(64 Length).
   procedure Add_Words
     (A, B : Word_Array; R : out Word_Array; Carry : out Unsigned_64)
   with
     Global => null,
     Pre  => A'First = 0 and then B'First = 0 and then R'First = 0
       and then A'Length = B'Length and then R'Length = A'Length
       and then A'Length in 1 .. Max_Words,
     Post => Carry <= 1
       and then To_Int (R) + Conv (Carry) * Weight (A'Length)
                = To_Int (A) + To_Int (B);

   --  A - B word by word; Borrow is 1 iff A < B, and the words denote
   --  A - B + Borrow * 2^(64 Length).
   procedure Sub_Words
     (A, B : Word_Array; R : out Word_Array; Borrow : out Unsigned_64)
   with
     Global => null,
     Pre  => A'First = 0 and then B'First = 0 and then R'First = 0
       and then A'Length = B'Length and then R'Length = A'Length
       and then A'Length in 1 .. Max_Words,
     Post => Borrow <= 1
       and then To_Int (R)
                = To_Int (A) - To_Int (B) + Conv (Borrow) * Weight (A'Length)
       and then (Borrow = 1) = (To_Int (A) < To_Int (B));

   type Limbs_With_Carry is record
      Limbs : Limb_Array;
      Carry : Unsigned_64;   --  0 or 1
   end record;

   function Add_Limbs (A, B : Limb_Array) return Limbs_With_Carry with
     Global => null,
     Post   => Add_Limbs'Result.Carry <= 1
       and then To_Int (Add_Limbs'Result.Limbs)
                  + Conv (Add_Limbs'Result.Carry) * Two_256
                = To_Int (A) + To_Int (B);

   function Sub_Limbs (A, B : Limb_Array) return Limbs_With_Carry with
     Global => null,
     Post   => Sub_Limbs'Result.Carry <= 1
       and then To_Int (Sub_Limbs'Result.Limbs)
                = To_Int (A) - To_Int (B)
                  + Conv (Sub_Limbs'Result.Carry) * Two_256
       and then (Sub_Limbs'Result.Carry = 1) = (To_Int (A) < To_Int (B));

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
        Post => Is_Canonical'Result = (To_Int (L) < P);

   type Element is record
      Limbs : Limb_Array;
   end record
   with Dynamic_Predicate => Is_Canonical (Element.Limbs);

   Zero : constant Element := (Limbs => [others => 0]);
   One  : constant Element := (Limbs => [1, 0, 0, 0]);

   function Add (A, B : Element) return Element with
     Global => null,
     Post   => To_Int (Add'Result.Limbs)
               = (To_Int (A.Limbs) + To_Int (B.Limbs)) mod P;

   function Sub (A, B : Element) return Element with
     Global => null,
     Post   => To_Int (Sub'Result.Limbs)
               = (To_Int (A.Limbs) - To_Int (B.Limbs)) mod P;

   function Neg (A : Element) return Element is (Sub (Zero, A)) with
     Global => null,
     Post   => To_Int (Neg'Result.Limbs) = (-To_Int (A.Limbs)) mod P;

   function Mul (A, B : Element) return Element with
     Global => null,
     Post   => To_Int (Mul'Result.Limbs)
               = (To_Int (A.Limbs) * To_Int (B.Limbs)) mod P;

   function Square (E : Element) return Element is (Mul (E, E)) with
     Global => null,
     Post   => To_Int (Square'Result.Limbs)
               = (To_Int (E.Limbs) * To_Int (E.Limbs)) mod P;

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

   --  Ok iff the encoding is canonical (value < p); then E denotes it.
   --  On rejection E is Zero.
   procedure From_Bytes (B : Bytes_32; E : out Element; Ok : out Boolean)
   with
     Global => null,
     Post   => Ok = Is_Canonical (Limbs_Of_Bytes (B))
       and then (if Ok then E.Limbs = Limbs_Of_Bytes (B) else E = Zero);

   function To_Bytes (E : Element) return Bytes_32 is
     (Bytes_Of_Limbs (E.Limbs))
   with Global => null,
        Post   => Limbs_Of_Bytes (To_Bytes'Result) = E.Limbs;

end P256_Field;
