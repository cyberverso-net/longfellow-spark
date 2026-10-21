--  Sumcheck_Algebra: the array vocabulary of the sumcheck protocol
--  (draft-03 Sections 6.1 to 6.4), the circuit types and their
--  evaluation (Section 6.3), generic over a field (ADR 0024).
--
--  Documentation: docs/guide/03-sumcheck.md. Decisions implemented
--  here: ADR 0022 (stage 3 scope and index names), 0023 (structural
--  Gold against ghost references), 0024 (field by formal package),
--  0025 (polynomials and Lagrange constants), 0026 (not here), 0027
--  (vectors); frame: ADR 0002, 0003, 0011, 0020.
--
--  Proof status, per instance (Sumcheck_Algebra_GF2_128 and
--  Sumcheck_Algebra_P256 are both library units and both proved).
--  Gold here is structural (ADR 0023): the postcondition says that the
--  executable code equals a ghost reference transcribing the formula
--  of the draft or of the upstream reference implementation, with the
--  operations in the order the reference applies them. SPARK does not
--  know the field laws of the formal "+", "-", "*": no contract below
--  uses commutativity, associativity or distributivity, and the
--  algebraic facts about these formulas (bindeq agrees with eq, the
--  Lagrange basis interpolates) are tested, not proved.
--
--    Eq               : Gold against Eq_Ref (product over the bits of
--                       X, least significant first, from One).
--    Eq2              : Gold by definition (expression function).
--    Bindeq           : Gold, pointwise against Bindeq_Ref, the
--                       recursive definition of Section 6.2.
--    Bind             : Gold, the formula of Section 6.1 with zero
--                       padding is the postcondition.
--    Lagrange_Basis   : Gold by definition, with the per-field
--                       denominator inverses (ADR 0025).
--    Eval_Quad        : Gold against Acc_Ref (quad sum per output wire
--                       in term order, k * w[h1] * w[h0]) and Z_Ref
--                       (the Z assertions of Section 6.3.3).
--    Eval_Circuit     : Gold, layer by layer through Eval_Quad on one
--                       flat wire buffer: the input segment is W, every
--                       layer segment is the quad sum of the next, and
--                       the status is "all Z assertions hold and every
--                       output wire is Zero".
--    Bind_G           : Gold, the per-term formula is the
--                       postcondition.
--    Eval_Bound_Quad  : Gold against EBQ_Ref (sum over terms in order).
--    Eval_Bound_Quad_T: Gold against EBQT_Ref (Phase D, M1): the same
--                       sum with eq read from the bindeq tables of
--                       Section 6.2, built once per layer, instead of
--                       computed bit by bit for every term. That the two
--                       sums agree is the tested fact that bindeq agrees
--                       with eq; Eval_Bound_Quad stays as the reference.
--
--  Errors are statuses (ADR 0022, D6): a Z assertion that fails or an
--  output wire that is not Zero makes OK False; nothing is raised.
--
--  Index names (ADR 0022): for layer J, NW_In (J) is the number of
--  input wires (the reference's layers[J].nw, the draft's NW[J + 1])
--  and Logw (J) the number of sumcheck rounds; NW_Out (J) is the
--  number of output wires (layers[J - 1].nw, or noutput for J = 0).
--  A term of layer J has G < NW_Out (J) and H0, H1 < NW_In (J).
--
--  The verifier handles public data; no constant-time requirement
--  applies here (ADR 0022). The only branches on element values are
--  the tests k = Zero on circuit constants.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Proof_Levels;
with Ada.Numerics.Big_Numbers.Big_Integers;
use  Ada.Numerics.Big_Numbers.Big_Integers;
with Field_Signature;

generic
   with package F is new Field_Signature (<>);
package Sumcheck_Algebra is

   subtype Element is F.Element;

   Zero       : Element renames F.Zero;
   One        : Element renames F.One;
   P2         : Element renames F.P2;
   L0_Den_Inv : Element renames F.L0_Den_Inv;
   L1_Den_Inv : Element renames F.L1_Den_Inv;
   L2_Den_Inv : Element renames F.L2_Den_Inv;

   --  The field operations, reached through wrappers that carry no
   --  postcondition. The wrappers are opaque to the provers: the
   --  contracts of the concrete field (Mul_Ref for GF(2^128), the
   --  integer model for P-256) never enter a protocol proof, which
   --  keeps every proof below a matter of congruence between the code
   --  and its ghost reference (ADR 0023) and makes the verification
   --  conditions the same for every instance. Equality is the
   --  predefined "=" of the element type.
   function "+" (A, B : Element) return Element with Global => null, Inline;
   function "-" (A, B : Element) return Element with Global => null, Inline;
   function "*" (A, B : Element) return Element with Global => null, Inline;
   function Neg (A : Element) return Element with Global => null, Inline;
   use type F.Element;

   --  Logical equality for the structural contracts (Field_Signature):
   --  Same (A, B) is equality of terms for the provers and the
   --  predefined "=" at run time. Every "equals the reference" below is
   --  stated with Same; the semantic tests of the code (k = Zero, a
   --  product = Zero, an output = Zero) keep the predefined "=".
   function Same (A, B : Element) return Boolean renames F.Same;

   --  Arrays of elements are indexed from 0; the index subtype stops
   --  one short of Natural'Last so that 'Length always fits Natural.
   subtype Index is Natural range 0 .. Natural'Last - 1;

   type Element_Array is array (Index range <>) of Element;

   --  Bounds. Max_Logw is MAX_LOGW of the reference (Section 6.6): at
   --  most 40 binding challenges per layer. Max_Wires, Max_Layers and
   --  Max_Terms bound the circuits this unit accepts so that wire
   --  offsets and term positions fit in Natural:
   --  (Max_Layers + 1) * Max_Wires < 2^31.
   Max_Logw   : constant := 40;
   Max_Wires  : constant := 2 ** 24;
   Max_Layers : constant := 64;
   Max_Terms  : constant := 2 ** 28;

   --  Largest number of challenges Bindeq expands (2^24 elements).
   Max_Bindeq_Log : constant := 24;

   subtype Logw_Type   is Natural range 0 .. Max_Logw;
   subtype Wire_Count  is Natural range 0 .. Max_Wires;
   subtype Wire_Index  is Natural range 0 .. Max_Wires - 1;
   subtype Layer_Last  is Natural range 0 .. Max_Layers - 1;
   subtype Term_Count  is Natural range 0 .. Max_Terms;
   subtype Term_Index  is Positive range 1 .. Max_Terms + 1;

   --  Bit B of X ((x_int >> b) & 1 in the reference). X is a wire index
   --  below 2^31, so bits 31 and above are 0. Deliberately opaque to the
   --  provers (a function with a body, no postcondition): Eq and its
   --  reference Eq_Ref call the same function, so their equality is a
   --  matter of congruence, and no bit-vector reasoning enters any
   --  proof. That this function reads bit B is a tested property.
   function Bit_Of (X : Natural; B : Natural) return Boolean with
     Global => null, Pre => B <= Max_Logw;

   --  2^N as a mathematical integer, for the sizes of Bindeq (ghost;
   --  the same pattern as Weight in P256_Field, ADR 0014).
   function Pow2 (N : Natural) return Big_Integer is
     (if N = 0 then To_Big_Integer (1) else 2 * Pow2 (N - 1))
   with Ghost, Global => null,
        Pre  => N <= Max_Bindeq_Log,
        Post => Pow2'Result >= 1,
        Subprogram_Variant => (Decreases => N);

   --  Element I of A under the zero-padding convention of Section 6.1
   --  (vector_ref in the reference).
   function Pad (A : Element_Array; I : Natural) return Element is
     (if I < A'Length then A (I) else Zero)
   with Global => null, Pre => A'First = 0;

   -------------------------------------------------------------------
   --  Section 6.2: eq and eq2.
   -------------------------------------------------------------------

   --  Reference for eq: the product over bits 0 .. N - 1 of X, from
   --  One, of R (b) when the bit is set and One - R (b) otherwise.
   function Eq_Ref (R : Element_Array; X : Natural; N : Natural)
                    return Element is
     (if N = 0 then One
      elsif Bit_Of (X, N - 1) then Eq_Ref (R, X, N - 1) * R (N - 1)
      else Eq_Ref (R, X, N - 1) * (One - R (N - 1)))
   with Ghost, Global => null,
        Pre => R'First = 0 and then N <= R'Length and then N <= Max_Logw,
        Subprogram_Variant => (Decreases => N);

   function Eq (R : Element_Array; X : Natural; N : Natural)
                return Element
   with Global => null,
        Pre  => R'First = 0 and then N <= R'Length and then N <= Max_Logw,
        Post => Same (Eq'Result, Eq_Ref (R, X, N));

   --  eq2 (x, logn, g0, g1, alpha) = eq (g0, x) + alpha * eq (g1, x).
   function Eq2 (X : Natural; N : Natural; G0, G1 : Element_Array;
                 Alpha : Element) return Element is
     (Eq (G0, X, N) + Alpha * Eq (G1, X, N))
   with Global => null,
        Pre => G0'First = 0 and then G1'First = 0
          and then N <= G0'Length and then N <= G1'Length
          and then N <= Max_Logw;

   -------------------------------------------------------------------
   --  Section 6.2: bindeq. Bindeq_Ref (C, K, I) is element I of
   --  bindeq (C (K .. C'Last)), read off the recursive definition:
   --  b (2 i) = (1 - c0) a (i), b (2 i + 1) = c0 a (i).
   -------------------------------------------------------------------

   function Bindeq_Ref (C : Element_Array; K : Natural; I : Natural)
                        return Element is
     (if K = C'Length then One
      elsif I mod 2 = 0 then (One - C (K)) * Bindeq_Ref (C, K + 1, I / 2)
      else C (K) * Bindeq_Ref (C, K + 1, I / 2))
   with Ghost, Global => null,
        Pre => C'First = 0 and then C'Length <= Max_Bindeq_Log
          and then K <= C'Length,
        Subprogram_Variant => (Increases => K);

   procedure Bindeq (C : Element_Array; B : out Element_Array) with
     Global => null,
     Pre  => C'First = 0 and then C'Length <= Max_Bindeq_Log
       and then B'First = 0
       and then To_Big_Integer (B'Length) = Pow2 (C'Length),
     Post => (for all I in B'Range => Same (B (I), Bindeq_Ref (C, 0, I)));

   -------------------------------------------------------------------
   --  Section 6.1: bind across the first dimension, with zero padding.
   -------------------------------------------------------------------

   procedure Bind (A : Element_Array; X : Element; B : out Element_Array)
   with
     Global => null,
     Pre  => A'First = 0 and then A'Length <= Max_Wires
       and then B'First = 0 and then B'Length = (A'Length + 1) / 2,
     Post => (for all I in B'Range =>
                Same (B (I),
                      (One - X) * Pad (A, 2 * I) + X * Pad (A, 2 * I + 1)));

   -------------------------------------------------------------------
   --  Section 6.4: the Lagrange basis on the points 0, 1, P2.
   -------------------------------------------------------------------

   type Basis is array (0 .. 2) of Element;

   function Lagrange_Basis (R : Element) return Basis is
     [0 => ((R - One) * (R - P2)) * L0_Den_Inv,
      1 => (R * (R - P2)) * L1_Den_Inv,
      2 => (R * (R - One)) * L2_Den_Inv]
   with Global => null;

   -------------------------------------------------------------------
   --  Section 6.3: circuits as data (ADR 0011). A term (g, h0, h1, k)
   --  with k /= Zero is Q [g, h1, h0] = k; with k = Zero it is a Z
   --  assertion, w (h1) * w (h0) = 0 (Section 6.3.3).
   -------------------------------------------------------------------

   type Term is record
      K      : Element;
      G      : Wire_Index;
      H0, H1 : Wire_Index;
   end record;

   type Term_Array is array (Term_Index range <>) of Term;

   --  Every term of T names an output wire below NV and input wires
   --  below NW.
   function Fits (T : Term_Array; NV, NW : Natural) return Boolean is
     (for all I in T'Range =>
        T (I).G < NV and then T (I).H0 < NW and then T (I).H1 < NW)
   with Global => null;

   --  Every input wire read by T, at offset Base in a buffer of length
   --  W_Len, lies inside the buffer.
   function In_Window (T : Term_Array; W_Len, Base : Natural)
                       return Boolean is
     (Base <= W_Len
      and then (for all I in T'Range =>
                  T (I).H0 < W_Len - Base and then T (I).H1 < W_Len - Base))
   with Global => null;

   --  A layer owns Terms (First .. Last) of the circuit's term list,
   --  reads NW_In input wires and binds them in Logw rounds.
   type Layer is record
      Logw  : Logw_Type;
      NW_In : Wire_Count;
      First : Term_Index;
      Last  : Term_Count;
   end record;

   type Layer_Array is array (Natural range <>) of Layer;

   --  Layers 0 .. Last_Layer (NL = Last_Layer + 1 of them) and NT
   --  terms in one flat list; layer 0 produces the outputs, the last
   --  layer reads the inputs. Raw_Circuit is the representation;
   --  Circuit, below, is the subtype that carries the well-formedness
   --  predicate (a predicate cannot sit on the record itself when its
   --  function takes the record as argument).
   type Raw_Circuit (Last_Layer : Layer_Last; NT : Term_Count) is record
      Noutput : Wire_Count;
      Ninput  : Wire_Count;
      Npublic : Wire_Count;
      Layers  : Layer_Array (0 .. Last_Layer);
      Terms   : Term_Array (1 .. NT);
   end record;

   --  Number of output wires of layer J (ADR 0022).
   function NW_Out (C : Raw_Circuit; J : Natural) return Wire_Count is
     (if J = 0 then C.Noutput else C.Layers (J - 1).NW_In)
   with Global => null, Pre => J <= C.Last_Layer;

   --  Well-formedness (ADR 0011, ADR 0022): the layers partition the
   --  term list in order; every term names wires in range; a layer's
   --  input wires fit in Logw bits; the last layer reads the inputs.
   function Well_Formed (C : Raw_Circuit) return Boolean is
     (C.Npublic <= C.Ninput
      and then C.Layers (0).First = 1
      and then C.Layers (C.Last_Layer).Last = C.NT
      and then (for all J in 1 .. C.Last_Layer =>
                  C.Layers (J).First = C.Layers (J - 1).Last + 1)
      and then (for all J in 0 .. C.Last_Layer =>
                  C.Layers (J).Last + 1 >= C.Layers (J).First
                  and then C.Layers (J).Last <= C.NT)
      and then (for all J in 0 .. C.Last_Layer =>
                  Unsigned_64 (C.Layers (J).NW_In)
                    <= Shift_Left (1, C.Layers (J).Logw))
      and then C.Layers (C.Last_Layer).NW_In = C.Ninput
      and then (for all J in 0 .. C.Last_Layer =>
                  Fits (C.Terms (C.Layers (J).First .. C.Layers (J).Last),
                        (if J = 0 then C.Noutput
                         else C.Layers (J - 1).NW_In),
                        C.Layers (J).NW_In)))
   with Global => null;

   subtype Circuit is Raw_Circuit
     with Dynamic_Predicate => Well_Formed (Circuit);

   --  The terms of layer J.
   function Layer_Terms (C : Circuit; J : Natural) return Term_Array is
     (C.Terms (C.Layers (J).First .. C.Layers (J).Last))
   with Global => null, Pre => J <= C.Last_Layer;

   -------------------------------------------------------------------
   --  Section 6.3.2 and 6.3.3: evaluation of one layer.
   --
   --  W is a buffer and Base an offset into it: the layer's input wire
   --  h is W (Base + h). Eval_Circuit keeps every layer in one buffer
   --  and passes the offset of the next layer; a plain call uses
   --  Base = 0.
   -------------------------------------------------------------------

   --  Element I of W, Zero beyond its end; the references below and the
   --  postcondition of Eval_Circuit are total in the index so that they
   --  need no bounds (the precondition on Wires'Length makes every index
   --  they use fall inside the buffer).
   function W_At (W : Element_Array; I : Natural) return Element is
     (if I < W'Length then W (I) else Zero)
   with Ghost, Global => null, Pre => W'First = 0;

   --  Accumulated value of output wire G after the first N terms: for
   --  each term with g = G and k /= Zero, k * w (h1) * w (h0) is added,
   --  in that association (eval_quad in the reference).
   function Acc_Ref (W : Element_Array; Base : Natural; T : Term_Array;
                     N : Natural; G : Natural) return Element is
     (if N = 0 then Zero
      elsif T (T'First + N - 1).G = G and then T (T'First + N - 1).K /= Zero
      then Acc_Ref (W, Base, T, N - 1, G)
             + ((T (T'First + N - 1).K
                   * W_At (W, Base + T (T'First + N - 1).H1))
                * W_At (W, Base + T (T'First + N - 1).H0))
      else Acc_Ref (W, Base, T, N - 1, G))
   with Ghost, Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => W'First = 0 and then N <= T'Length
          and then Base <= Natural'Last - Max_Wires,
        Subprogram_Variant => (Decreases => N);

   --  Every Z assertion among the first N terms holds: for each term
   --  with k = Zero, w (h1) * w (h0) = Zero.
   function Z_Ref (W : Element_Array; Base : Natural; T : Term_Array;
                   N : Natural) return Boolean is
     (N = 0
      or else (Z_Ref (W, Base, T, N - 1)
               and then (T (T'First + N - 1).K /= Zero
                         or else W_At (W, Base + T (T'First + N - 1).H1)
                                   * W_At (W, Base + T (T'First + N - 1).H0)
                                 = Zero)))
   with Ghost, Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => W'First = 0 and then N <= T'Length
          and then Base <= Natural'Last - Max_Wires,
        Subprogram_Variant => (Decreases => N);

   procedure Eval_Quad (W : Element_Array; Base : Natural; T : Term_Array;
                        V : out Element_Array; OK : out Boolean)
   with
     Global => null,
     Pre  => W'First = 0 and then V'First = 0
       and then W'Length <= Natural'Last - Max_Wires
       and then In_Window (T, W'Length, Base)
       and then (for all I in T'Range => T (I).G < V'Length),
     Post => OK = Z_Ref (W, Base, T, T'Length)
       and then (for all G in V'Range =>
                   Same (V (G), Acc_Ref (W, Base, T, T'Length, G)));

   -------------------------------------------------------------------
   --  Section 6.3: evaluation of the whole circuit into one buffer.
   --
   --  Segment J of the buffer holds V [J], the wires computed by layer
   --  J (segment NL is the input W): Seg_Size (C, J) elements from
   --  offset Off (C, J). Total_Wires (C) is the buffer length.
   -------------------------------------------------------------------

   function Seg_Size (C : Circuit; J : Natural) return Wire_Count is
     (if J = 0 then C.Noutput else C.Layers (J - 1).NW_In)
   with Global => null, Pre => J <= C.Last_Layer + 1;

   function Off (C : Circuit; J : Natural) return Natural is
     (if J = 0 then 0 else Off (C, J - 1) + Seg_Size (C, J - 1))
   with Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => J <= C.Last_Layer + 2,
        Post => Off'Result <= J * Max_Wires,
        Subprogram_Variant => (Decreases => J);

   function Total_Wires (C : Circuit) return Natural is
     (Off (C, C.Last_Layer + 2))
   with Global => null;

   --  Segment J equals the quad sum of segment J + 1 (Section 6.3.2).
   function Layer_Holds (C : Circuit; Wires : Element_Array; J : Natural)
                         return Boolean is
     (for all G in 0 .. Seg_Size (C, J) - 1 =>
        Same (W_At (Wires, Off (C, J) + G),
              Acc_Ref (Wires, Off (C, J + 1), Layer_Terms (C, J),
                       Layer_Terms (C, J)'Length, G)))
   with Ghost, Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => Wires'First = 0 and then J <= C.Last_Layer;

   --  The Z assertions of layer J hold on segment J + 1 (Section 6.3.3).
   function Layer_Z (C : Circuit; Wires : Element_Array; J : Natural)
                     return Boolean is
     (Z_Ref (Wires, Off (C, J + 1), Layer_Terms (C, J),
             Layer_Terms (C, J)'Length))
   with Ghost, Global => null,
        Pre => Wires'First = 0 and then J <= C.Last_Layer;

   procedure Eval_Circuit (C : Circuit; W : Element_Array;
                           Wires : in out Element_Array; OK : out Boolean)
   with
     Global => null,
     Pre  => W'First = 0 and then W'Length = C.Ninput
       and then Wires'First = 0 and then Wires'Length = Total_Wires (C),
     Post => (for all I in 0 .. C.Ninput - 1 =>
                Same (W_At (Wires, Off (C, C.Last_Layer + 1) + I), W (I)))
       and then (for all J in 0 .. C.Last_Layer => Layer_Holds (C, Wires, J))
       and then OK = ((for all J in 0 .. C.Last_Layer => Layer_Z (C, Wires, J))
                      and then (for all G in 0 .. C.Noutput - 1 =>
                                  W_At (Wires, G) = Zero));

   -------------------------------------------------------------------
   --  bind_g and eval_bound_quad of the reference (sumcheck/common.rs):
   --  binding the output index of every term with the two claim
   --  challenge vectors, and the fully bound quad.
   -------------------------------------------------------------------

   --  The coefficient of a term once g is bound: beta * eq2 (g) for a
   --  Z term, k * eq2 (g) otherwise.
   function Bound_K (Tm : Term; Logv : Natural; G0, G1 : Element_Array;
                     Alpha, Beta : Element) return Element is
     (if Tm.K = Zero then Beta * Eq2 (Tm.G, Logv, G0, G1, Alpha)
      else Tm.K * Eq2 (Tm.G, Logv, G0, G1, Alpha))
   with Global => null,
        Pre => G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= Max_Logw;

   procedure Bind_G (T : in out Term_Array; Logv : Natural;
                     G0, G1 : Element_Array; Alpha, Beta : Element)
   with
     Global => null,
     Pre  => G0'First = 0 and then G1'First = 0
       and then Logv <= G0'Length and then Logv <= G1'Length
       and then Logv <= Max_Logw,
     Post => (for all I in T'Range =>
                Same (T (I).K, Bound_K (T'Old (I), Logv, G0, G1, Alpha, Beta))
                and then T (I).G = 0
                and then T (I).H0 = T'Old (I).H0
                and then T (I).H1 = T'Old (I).H1);

   --  Sum over the first N terms of
   --  bound_k * eq (HC0, h0, Logw) * eq (HC1, h1, Logw), in that order.
   function EBQ_Ref (T : Term_Array; N : Natural; Logv : Natural;
                     G0, G1 : Element_Array; HC0, HC1 : Element_Array;
                     Logw : Natural; Alpha, Beta : Element) return Element
   is
     (if N = 0 then Zero
      else EBQ_Ref (T, N - 1, Logv, G0, G1, HC0, HC1, Logw, Alpha, Beta)
             + ((Bound_K (T (T'First + N - 1), Logv, G0, G1, Alpha, Beta)
                   * Eq (HC0, T (T'First + N - 1).H0, Logw))
                * Eq (HC1, T (T'First + N - 1).H1, Logw)))
   with Ghost, Global => null,
        Pre => N <= T'Length
          and then G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= Max_Logw
          and then HC0'First = 0 and then HC1'First = 0
          and then Logw <= HC0'Length and then Logw <= HC1'Length
          and then Logw <= Max_Logw,
        Subprogram_Variant => (Decreases => N);

   -------------------------------------------------------------------
   --  The bound quad by tables (Phase D, M1). The value of eq at X on
   --  the first L challenges of C, read from bindeq of Section 6.2
   --  (Zero beyond the table), and eq2 the same way.
   -------------------------------------------------------------------

   --  2^L, the length of a bindeq table, computed by doubling (the
   --  provers do not bound 2**L for a variable L); as Pow2 states it.
   function Table_Len (L : Natural) return Positive with
     Global => null,
     Pre    => L <= Max_Bindeq_Log,
     Post   => To_Big_Integer (Table_Len'Result) = Pow2 (L)
               and then Table_Len'Result <= 2**Max_Bindeq_Log;

   function Beq (C : Element_Array; L : Natural; X : Natural) return Element
   is
     (if X < Table_Len (L) then Bindeq_Ref (C (0 .. L - 1), 0, X) else Zero)
   with Ghost => Proof_Only, Global => null,
        Pre => C'First = 0 and then L <= C'Length
               and then L <= Max_Bindeq_Log;

   function Beq2 (X : Natural; L : Natural; G0, G1 : Element_Array;
                  Alpha : Element) return Element
   is
     (if X < Table_Len (L)
      then Bindeq_Ref (G0 (0 .. L - 1), 0, X)
           + Alpha * Bindeq_Ref (G1 (0 .. L - 1), 0, X)
      else Zero)
   with Ghost => Proof_Only, Global => null,
        Pre => G0'First = 0 and then G1'First = 0
               and then L <= G0'Length and then L <= G1'Length
               and then L <= Max_Bindeq_Log;

   --  The eq2 table: E (X) = bindeq (G0) (X) + alpha bindeq (G1) (X) for
   --  every X below 2^L, built on the heap.
   procedure Eq2_Table
     (L      : Natural;
      G0, G1 : Element_Array;
      Alpha  : Element;
      E      : out Element_Array)
   with
     Global => null,
     Pre  => G0'First = 0 and then G1'First = 0
       and then L <= G0'Length and then L <= G1'Length
       and then L <= Max_Bindeq_Log
       and then E'First = 0 and then E'Last = Table_Len (L) - 1,
     Post => (Proof_Only =>
                (for all X in E'Range =>
                   Same (E (X), Beq2 (X, L, G0, G1, Alpha))));

   --  Bound_K with the tables.
   function Bound_KT (Tm : Term; Logv : Natural; G0, G1 : Element_Array;
                      Alpha, Beta : Element) return Element
   is
     (if Tm.K = Zero then Beta * Beq2 (Tm.G, Logv, G0, G1, Alpha)
      else Tm.K * Beq2 (Tm.G, Logv, G0, G1, Alpha))
   with Ghost => Proof_Only, Global => null,
        Pre => G0'First = 0 and then G1'First = 0
               and then Logv <= G0'Length and then Logv <= G1'Length
               and then Logv <= Max_Bindeq_Log;

   function EBQT_Ref (T : Term_Array; N : Natural; Logv : Natural;
                      G0, G1 : Element_Array; HC0, HC1 : Element_Array;
                      Logw : Natural; Alpha, Beta : Element) return Element
   is
     (if N = 0 then Zero
      else EBQT_Ref (T, N - 1, Logv, G0, G1, HC0, HC1, Logw, Alpha, Beta)
             + ((Bound_KT (T (T'First + N - 1), Logv, G0, G1, Alpha, Beta)
                   * Beq (HC0, Logw, T (T'First + N - 1).H0))
                * Beq (HC1, Logw, T (T'First + N - 1).H1)))
   with Ghost => Proof_Only, Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => N <= T'Length
          and then G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= Max_Bindeq_Log
          and then HC0'First = 0 and then HC1'First = 0
          and then Logw <= HC0'Length and then Logw <= HC1'Length
          and then Logw <= Max_Bindeq_Log,
        Subprogram_Variant => (Decreases => N);

   --  eval_bound_quad with the tables: E = bindeq (G0) + alpha bindeq (G1)
   --  over 2^Logv entries and bindeq of HC0 and HC1 over 2^Logw, built
   --  once on the heap; three multiplications per term.
   procedure Eval_Bound_Quad_T
     (T        : Term_Array;
      Logv     : Natural;
      G0, G1   : Element_Array;
      HC0, HC1 : Element_Array;
      Logw     : Natural;
      Alpha, Beta : Element;
      Result   : out Element)
   with
     Global => null,
     Pre  => G0'First = 0 and then G1'First = 0
       and then Logv <= G0'Length and then Logv <= G1'Length
       and then Logv <= Max_Bindeq_Log
       and then HC0'First = 0 and then HC1'First = 0
       and then Logw <= HC0'Length and then Logw <= HC1'Length
       and then Logw <= Max_Bindeq_Log,
     Post => (Proof_Only =>
                Same (Result,
                      EBQT_Ref (T, T'Length, Logv, G0, G1, HC0, HC1, Logw,
                                Alpha, Beta)));

   function Eval_Bound_Quad (T : Term_Array; Logv : Natural;
                             G0, G1 : Element_Array;
                             HC0, HC1 : Element_Array; Logw : Natural;
                             Alpha, Beta : Element) return Element
   with
     Global => null,
     Pre  => G0'First = 0 and then G1'First = 0
       and then Logv <= G0'Length and then Logv <= G1'Length
       and then Logv <= Max_Logw
       and then HC0'First = 0 and then HC1'First = 0
       and then Logw <= HC0'Length and then Logw <= HC1'Length
       and then Logw <= Max_Logw,
     Post => Same (Eval_Bound_Quad'Result,
                   EBQ_Ref (T, T'Length, Logv, G0, G1, HC0, HC1, Logw,
                            Alpha, Beta));

end Sumcheck_Algebra;
