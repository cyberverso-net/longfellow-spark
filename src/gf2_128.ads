--  GF2_128: arithmetic over the binary field GF(2^128) used by the
--  Longfellow ZK sumcheck and Ligero layers.
--
--  Documentation: docs/guide/01-gf2_128.md (mathematics, algorithms, this
--  implementation walked through, what is proved, tested and trusted).
--  Decisions implemented here: ADR 0004 (element representation),
--  0005 (Mul_Ref as proof target), 0006 (constant-time scope),
--  0007 (Square), 0008 (Inv), 0024 (Sub and Neg for the field
--  signature), with 0002 (pinned spec), 0003 (proof policy) and 0020
--  (prover configuration) as the frame; see docs/adr/README.md.
--
--  Proof status. SPARK assurance levels: Silver = absence of run-time
--  errors, Gold = proved functional contracts. Stage 1 of Phase A is
--  complete: every subprogram below is at least Silver, and the Gold
--  kernels are Add, Xtime, Mul and Square. All verification conditions
--  are discharged by GNATprove with the project's proof switches
--  (package Prove in longfellow_spark.gpr, ADR 0020: the level 2
--  provers with a step budget; 41 checks).
--
--    Add     : Gold, functional Post proved (addition is limb-wise xor).
--    Sub, Neg: Gold, Sub = Add and Neg = identity (characteristic 2),
--              stated for the protocol code of stage 3 (ADR 0024).
--    Xtime   : Gold, exact bit-level Post proved (multiplication by x
--              with reduction).
--    Mul     : Gold, Post proved against the ghost reference Mul_Ref
--              (MSB-first Horner over the bits of B). Since milestone
--              M2 (ADR 0065) Mul is the carry-less multiplication of
--              upstream's generic.rs: three 64 by 64 products of
--              Clmul64 (Karatsuba) and two folds; the proof goes
--              through the 256-bit product, linear in B and equal to
--              Mul_Ref on each single bit. Mul_Serial is the former
--              bit-by-bit Mul, Gold against Mul_Ref, kept as the
--              reference the harness compares with. NOTE: the proof
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
--    Bit, Mul_Ref, Inject_Ref : Ghost, specification vocabulary only,
--              at the assertion level Proof_Only (ADR 0044) with the
--              postconditions of Xtime, Mul, Square and Inject and the
--              loop invariants that state them: proved for all inputs,
--              never compiled in any build. What the test build checks
--              of these operations is their result against the vectors.
--    Subfield_Coords, In_Subfield : Silver (Phase C, ADR 0051): the
--              fixed projection to the subfield coordinates; that it
--              inverts Inject on the subfield is tested on the masks
--              and on coordinates against the generator's independent
--              derivation (gf2_128_bytes.txt), not proved.
--    To_Bytes, From_Bytes : Gold (stage 4, ADR 0028): the 16-byte
--              little-endian encoding of draft Section 7.2.1, every
--              16-byte string accepted (Ok is always True); the value
--              read is Limbs_Of_Bytes (B) and To_Bytes round-trips.
--              The byte order is anchored on the draft by
--              tests/vectors/gf2_128_bytes.txt.
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
--  review, P2): the executable contracts are compiled and EXECUTED when
--  assertions are enabled (-gnata / Alire validation profile); Mul_Ref,
--  which branches on the bits of B, is proof-only since ADR 0044 and
--  never compiled, but the limb-wise postconditions still run. The
--  constant-time property therefore holds ONLY for builds with
--  assertions disabled (Assertion_Policy Ignore, e.g. the release
--  profile). Never benchmark, measure, or deploy this code with
--  assertions enabled.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Bytes;
with Proof_Levels;

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

   --  Coefficient of x^I (bit I) of E. Ghost: it is the vocabulary of
   --  the contracts and of Mul_Ref, and it is not compiled into the
   --  library when assertions are disabled, so no executable path
   --  branches on a bit of an element (its body compiles to a branch).
   function Bit (E : Element; I : Bit_Index_128) return Boolean is
     ((Shift_Right (E.Limbs (Limb_Index (I / 64)), I mod 64) and 1) = 1)
   with Ghost => Proof_Only, Global => null;

   --  Field addition. In characteristic 2 this is exact xor and is its
   --  own inverse; no reduction is involved, so it is polynomial-agnostic.
   function Add (A, B : Element) return Element with
     Global => null,
     Inline,
     Post   =>
       (for all I in Limb_Index =>
          Add'Result.Limbs (I) = (A.Limbs (I) xor B.Limbs (I)));

   --  Subtraction equals addition in characteristic 2 (every element is
   --  its own additive inverse). Declared with the postcondition the
   --  protocol code relies on through Field_Signature (ADR 0024).
   function Sub (A, B : Element) return Element with
     Global => null,
     Inline,
     Post   => Sub'Result = Add (A, B);

   --  Negation is the identity in characteristic 2.
   function Neg (A : Element) return Element with
     Global => null,
     Inline,
     Post   => Neg'Result = A;

   --  Multiplication by x with reduction mod Q(x): shift left by one,
   --  fold the outgoing bit 127 onto Reduction_Low.
   function Xtime (E : Element) return Element with
     Global => null,
     Post   =>
       (Proof_Only =>
          Xtime'Result.Limbs (1) =
            (Shift_Left (E.Limbs (1), 1) or Shift_Right (E.Limbs (0), 63))
          and then
          Xtime'Result.Limbs (0) =
            (Shift_Left (E.Limbs (0), 1)
               xor (if Bit (E, 127) then Reduction_Low else 0)));

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
     Ghost => Proof_Only,
     Global => null,
     Subprogram_Variant => (Decreases => N);

   --  Field multiplication, A * B mod Q(x).
   function Mul (A, B : Element) return Element with
     Global => null,
     Inline,
     Post   => (Proof_Only => Mul'Result = Mul_Ref (A, B, 128));

   --  The same product bit by bit: 128 steps of Xtime and a masked xor,
   --  the form of Mul before milestone M2, kept as the reference that
   --  the harness compares Mul with (ADR 0065).
   function Mul_Serial (A, B : Element) return Element with
     Global => null,
     Post   => (Proof_Only => Mul_Serial'Result = Mul_Ref (A, B, 128));

   --  The product is associative (ADR 0066), the law the Lagrange
   --  tables need; proved against Mul_Ref.
   procedure Lemma_Mul_Assoc (A, B, C : Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Mul (Mul (A, B), C) = Mul (A, Mul (B, C));

   --  The other laws of the product the sumcheck kernels need (ADR
   --  0070), proved against Mul_Ref: commutativity, One as the unit,
   --  and distributivity over Add.
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

   --  Field squaring, E * E mod Q(x). Thin wrapper over Mul for now.
   function Square (E : Element) return Element with
     Global => null,
     Post   => (Proof_Only => Square'Result = Mul_Ref (E, E, 128));

   --  Multiplicative inverse by Fermat: E^(2^128 - 2), computed with a
   --  fixed addition chain (no data-dependent control flow), so it is
   --  constant time under the same scope as the rest of the package.
   --  Total function: Inv (Zero) = Zero (see the header). Silver only;
   --  E * Inv (E) = One is anchored by known-answer tests.
   function Inv (E : Element) return Element with
     Global => null;


   --  Serialisation (draft-03 Section 7.2.1, stage 4): an element is
   --  the 128-bit integer whose bit i is the coefficient of x^i,
   --  written as 16 bytes least significant first, that is Limbs (0)
   --  little-endian then Limbs (1). The byte type is the shared one
   --  of package Bytes (ADR 0028). No encoding is rejected.

   subtype Bytes_8  is Bytes.Bytes_8;
   subtype Bytes_16 is Bytes.Bytes_16;

   --  One limb from eight bytes, least significant first.
   function Limb_Of_8 (B : Bytes_8) return Unsigned_64 with
     Global => null;

   function Limbs_Of_Bytes (B : Bytes_16) return Limb_Array with
     Global => null;

   function Bytes_Of_Limbs (L : Limb_Array) return Bytes_16 with
     Global => null,
     Post   => Limbs_Of_Bytes (Bytes_Of_Limbs'Result) = L;

   --  Ok is always True: every 16-byte string is an element.
   procedure From_Bytes (B : Bytes_16; E : out Element; Ok : out Boolean)
   with
     Global => null,
     Post   => Ok and then E.Limbs = Limbs_Of_Bytes (B);

   function To_Bytes (E : Element) return Bytes_16 is
     (Bytes_Of_Limbs (E.Limbs))
   with Global => null,
        Post   => Limbs_Of_Bytes (To_Bytes'Result) = E.Limbs;


   --  The subfield GF(2^16) (draft-03 Section 2.2.2, stage 5): basis
   --  beta_i = g^i, g = x^((2^128 - 1) / (2^16 - 1)), the sixteen
   --  constants of the upstream reference (docs/specs/rust/src/algebra/
   --  gf2_128.rs, SUBFIELD_BASIS at d5e6be7), anchored by the stage 1
   --  vectors (ADR 0009). Inject (X) is the element with coordinates
   --  the bits of X on that basis: the Reed-Solomon evaluation point x
   --  of the Ligero code (reed_solomon_eval_point) and the decoding of
   --  a 2-byte subfield element (Section 7.2.2). Gold, structural:
   --  Inject is the xor of the basis elements at the set bits of X,
   --  taken in order from bit 0 (Inject_Ref).

   subtype Basis_Index is Natural range 0 .. 15;
   type Basis_Array is array (Basis_Index) of Element;

   Subfield_Basis : constant Basis_Array :=
     [0 => (Limbs => [0 => 16#0000000000000001#, 1 => 16#0000000000000000#]),
      1 => (Limbs => [0 => 16#F1871E01B64FDA4C#, 1 => 16#5C5971877501D4B8#]),
      2 => (Limbs => [0 => 16#A6E310FB6E176EA8#, 1 => 16#8BB99658EAF2CAE0#]),
      3 => (Limbs => [0 => 16#3F8DE8A2F9FF7EED#, 1 => 16#B61E08DA12F9665C#]),
      4 => (Limbs => [0 => 16#9BA3282087A3F827#, 1 => 16#A76C2E634C6483AE#]),
      5 => (Limbs => [0 => 16#F7AF4E93629F689E#, 1 => 16#54944FF4A5269CED#]),
      6 => (Limbs => [0 => 16#D0765F1873309B88#, 1 => 16#5439ECFD75A950D8#]),
      7 => (Limbs => [0 => 16#E566F9FC3D9B58A2#, 1 => 16#49ECDFBE06777B02#]),
      8 => (Limbs => [0 => 16#19AF205497F8E2D0#, 1 => 16#97A401B733E66A93#]),
      9 => (Limbs => [0 => 16#60E4DBDCE9777814#, 1 => 16#789FD7793CE75238#]),
     10 => (Limbs => [0 => 16#C0F157187ADBC05B#, 1 => 16#AA440B2D4B546256#]),
     11 => (Limbs => [0 => 16#222F207D0D8AD9F9#, 1 => 16#79F2CADB70B6115D#]),
     12 => (Limbs => [0 => 16#F6D1F84FB66C52B8#, 1 => 16#AE72AF7894CE037D#]),
     13 => (Limbs => [0 => 16#4AF94EF056D28A30#, 1 => 16#D6F226D783D454DB#]),
     14 => (Limbs => [0 => 16#0F37A0A4D91B4220#, 1 => 16#057D918D494925FC#]),
     15 => (Limbs => [0 => 16#B683012350E55753#, 1 => 16#18D4BBB6833C5AE8#])];

   subtype Subfield_Value is Natural range 0 .. 2**16 - 1;

   --  The xor of Subfield_Basis (I) over the set bits I < N of X.
   function Inject_Ref (X : Subfield_Value; N : Natural) return Element is
     (if N = 0 then Zero
      elsif (X / 2 ** (N - 1)) mod 2 = 1
      then Add (Inject_Ref (X, N - 1), Subfield_Basis (N - 1))
      else Inject_Ref (X, N - 1))
   with Ghost => Proof_Only,
        Pre => N <= 16,
        Subprogram_Variant => (Decreases => N);

   function Inject (X : Subfield_Value) return Element with
     Global => null,
     Post   => (Proof_Only => Inject'Result = Inject_Ref (X, 16));

   --  The inverse of Inject on the subfield, as a fixed linear map
   --  (Phase C, ADR 0051): coordinate I of an element is the parity of
   --  the element's low limb masked by Subfield_Mask (I). The sixteen
   --  masks are a left inverse of the basis matrix on the bit positions
   --  0 .. 12 and 14 .. 16, computed from the basis by Gaussian
   --  elimination in tests/vectors/gen_gf2_128_vectors.py, which also
   --  checks Subfield_Coords (Inject (X)) = X on subfield elements and
   --  In_Subfield on elements outside it (gf2_128_bytes.txt). No linear
   --  system is solved at run time and the control flow does not
   --  depend on the element: the prover applies it to witnesses.
   subtype Mask_Index is Natural range 0 .. 15;
   type Mask_Array is array (Mask_Index) of Unsigned_64;

   Subfield_Mask : constant Mask_Array :=
     [16#09013#, 16#114B4#, 16#118EE#, 16#1D590#,
      16#19062#, 16#059A6#, 16#1472A#, 16#09372#,
      16#01484#, 16#108E4#, 16#193CA#, 16#18F54#,
      16#0DBD0#, 16#14BE6#, 16#1D12C#, 16#0C97E#];

   --  The parity of the set bits of V, by xor folding.
   function Parity (V : Unsigned_64) return Unsigned_64 with
     Global => null,
     Post   => Parity'Result <= 1;

   function Subfield_Coords (E : Element) return Subfield_Value with
     Global => null;

   --  E lies in GF(2^16): it is the injection of its coordinates.
   function In_Subfield (E : Element) return Boolean is
     (Inject (Subfield_Coords (E)) = E)
   with Global => null;

end GF2_128;
