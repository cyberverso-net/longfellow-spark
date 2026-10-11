--  GF2_128: arithmetic over the binary field GF(2^128) used by the
--  Longfellow ZK sumcheck and Ligero layers.
--
--  Documentation: docs/guide/01-gf2_128.md (mathematics, algorithms, this
--  implementation walked through, what is proved, tested and trusted).
--  Decisions implemented here: ADR 0004 (element representation),
--  0005 (Mul_Ref as proof target), 0006 (constant-time scope),
--  0007 (Square), 0008 (Inv), with 0002 (pinned spec) and 0003 (proof
--  policy) as the frame; see docs/adr/README.md.
--
--  Proof status. SPARK assurance levels: Silver = absence of run-time
--  errors, Gold = proved functional contracts. Stage 1 of Phase A is
--  complete: every subprogram below is at least Silver, and the Gold
--  kernels are Add, Xtime, Mul and Square. All verification conditions
--  are discharged by GNATprove with the project's proof switches
--  (package Prove in longfellow_spark.gpr: the level 2 provers with a
--  step budget; 41 checks, CVC5 only).
--
--    Add     : Gold, functional Post proved (addition is limb-wise xor).
--    Xtime   : Gold, exact bit-level Post proved (multiplication by x
--              with reduction).
--    Mul     : Gold, Post proved against the ghost reference Mul_Ref
--              (MSB-first Horner over the bits of B). NOTE: the proof
--              establishes Mul = Mul_Ref for all inputs; that Mul_Ref
--              itself matches the pinned spec's convention is anchored
--              by known-answer tests (tests/vectors/gf2_128_mul.txt,
--              with anchors from the upstream subfield basis constants),
--              not by proof.
--    Square  : Gold by composition: thin wrapper over Mul, Post proved
--              against Mul_Ref (E, E, 128). The linear (Frobenius)
--              fast path is a later optimisation.
--    Inv     : Silver only (AoRTE), plus known-answer tests
--              (tests/vectors/gf2_128_inv.txt). Fermat correctness
--              (E * Inv (E) = 1) is out of SMT reach by design decision.
--              Inv is total: Inv (Zero) = Zero, which is what the Fermat
--              chain yields with no extra branch and matches the
--              upstream C++ (the upstream Rust reference asserts
--              instead). Callers that must reject zero do so themselves.
--
--  Pinned spec: IETF draft-google-cfrg-libzk-03 (23 September 2026),
--  Section 2.2.2: the field is GF(2)[x] / Q(x) with
--    Q(x) = x^128 + x^7 + x^2 + x + 1
--  and x is a generator of the multiplicative group. The spec also defines
--  a subfield GF(2^16) via g = x^((2^128 - 1) / (2^16 - 1)), basis
--  beta_i = g^i: the tower must be modelled explicitly (handoff v3).
--  Q(x) coincides with the GHASH/GCM polynomial, so x^128 reduces to the
--  low mask 2#1000_0111# (16#87#). CAUTION: GCM known-answer vectors are
--  reusable ONLY if the element encoding also matches; GCM uses reflected
--  bit order, the draft uses bit-injection basis coordinates. Verify the
--  encoding against the spec before importing any GCM vectors.
--
--  Constant-time discipline: no secret-dependent branching or indexing
--  in any executable statement of this package. Conditional xors are
--  realised with arithmetic masks (0 - bit); if-expressions appear only
--  in contracts and ghost code. SCOPE OF THE GUARANTEE (independent
--  review, P2): contracts and ghost code are compiled and EXECUTED when
--  assertions are enabled (-gnata / Alire validation profile), and
--  Mul_Ref then branches on the bits of B at run time. The constant-time
--  property therefore holds ONLY for builds with assertions disabled
--  (Assertion_Policy Ignore, e.g. the release profile). Never benchmark,
--  measure, or deploy this code with assertions enabled.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;

package GF2_128 is

   --  A field element as two 64-bit limbs, little-endian limb order:
   --  Limbs (0) holds bits 0 .. 63, Limbs (1) holds bits 64 .. 127.
   --  Bit I is the coefficient of x^I in the polynomial.

   type Limb_Index is range 0 .. 1;
   type Limb_Array is array (Limb_Index) of Unsigned_64;

   type Element is record
      Limbs : Limb_Array;
   end record;

   Zero : constant Element := (Limbs => (others => 0));
   One  : constant Element := (Limbs => (0 => 1, 1 => 0));

   --  x^128 = x^7 + x^2 + x + 1 mod Q(x)   (draft-03, Sec 2.2.2)
   Reduction_Low : constant Unsigned_64 := 16#87#;

   subtype Bit_Index_128 is Natural range 0 .. 127;
   subtype Bit_Count is Natural range 0 .. 128;

   --  Coefficient of x^I (bit I) of E.
   function Bit (E : Element; I : Bit_Index_128) return Boolean is
     ((Shift_Right (E.Limbs (Limb_Index (I / 64)), I mod 64) and 1) = 1)
   with Global => null;

   --  Field addition. In characteristic 2 this is exact xor and is its
   --  own inverse; no reduction is involved, so it is polynomial-agnostic.
   function Add (A, B : Element) return Element with
     Global => null,
     Post   =>
       (for all I in Limb_Index =>
          Add'Result.Limbs (I) = (A.Limbs (I) xor B.Limbs (I)));

   --  Convenience: subtraction equals addition in characteristic 2.
   function Sub (A, B : Element) return Element is (Add (A, B)) with
     Global => null;

   --  Multiplication by x with reduction mod Q(x): shift left by one,
   --  fold the outgoing bit 127 onto Reduction_Low.
   function Xtime (E : Element) return Element with
     Global => null,
     Post   =>
       Xtime'Result.Limbs (1) =
         (Shift_Left (E.Limbs (1), 1) or Shift_Right (E.Limbs (0), 63))
       and then
       Xtime'Result.Limbs (0) =
         (Shift_Left (E.Limbs (0), 1)
            xor (if Bit (E, 127) then Reduction_Low else 0));

   --  Ghost reference for multiplication: MSB-first Horner over the top
   --  N bits of B. Mul_Ref (A, B, 128) is the definitional product
   --  A * B mod Q(x): Horner evaluation IS polynomial multiplication.
   function Mul_Ref (A, B : Element; N : Bit_Count) return Element is
     (if N = 0 then
        Zero
      elsif Bit (B, 128 - N) then
        Add (Xtime (Mul_Ref (A, B, N - 1)), A)
      else
        Xtime (Mul_Ref (A, B, N - 1)))
   with
     Ghost,
     Global => null,
     Subprogram_Variant => (Decreases => N);

   --  Field multiplication, A * B mod Q(x).
   function Mul (A, B : Element) return Element with
     Global => null,
     Post   => Mul'Result = Mul_Ref (A, B, 128);

   --  Field squaring, E * E mod Q(x). Thin wrapper over Mul for now.
   function Square (E : Element) return Element with
     Global => null,
     Post   => Square'Result = Mul_Ref (E, E, 128);

   --  Multiplicative inverse by Fermat: E^(2^128 - 2), computed with a
   --  fixed addition chain (no data-dependent control flow), so it is
   --  constant time under the same scope as the rest of the package.
   --  Total function: Inv (Zero) = Zero (see the header). Silver only;
   --  E * Inv (E) = One is anchored by known-answer tests.
   function Inv (E : Element) return Element with
     Global => null;

end GF2_128;
