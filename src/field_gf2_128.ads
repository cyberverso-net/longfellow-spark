--  Field_GF2_128: GF(2^128) as a Field_Signature instance (ADR 0024,
--  ADR 0025).
--
--  P2 is the third sumcheck evaluation point of draft-03 Section 6.4,
--  inj (2) of Section 2.2.2: the second element beta_1 of the subfield
--  basis, the same upstream constant that anchors the stage 1 vectors
--  (google/longfellow-zk d5e6be7, docs/specs/rust/src/algebra/
--  gf2_128.rs, SUBFIELD_BASIS [1]).
--
--  In characteristic 2 subtraction is addition, so the Lagrange
--  denominators are d0 = P2, d1 = 1 + P2, d2 = P2 (1 + P2). The
--  inverses below are computed by tests/vectors/gen_sumcheck_vectors.py
--  (extended Euclid in GF(2)[x], checked by d * inv (d) = 1) and
--  re-checked by the harness sumcheck_kat with Mul at every run.

pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Bytes;
with GF2_128;
with Field_Signature;
with Proof_Levels;

package Field_GF2_128 is

   use type GF2_128.Element;

   --  Logical equality for contracts (see Field_Signature). The body
   --  is the predefined "=", outside SPARK; the provers treat Same as
   --  equality of terms (annotation Logical_Equal).
   function Same (A, B : GF2_128.Element) return Boolean with
     Ghost, Global => null, Annotate => (GNATprove, Logical_Equal);

   P2 : constant GF2_128.Element :=
     (Limbs => [0 => 16#F1871E01B64FDA4C#, 1 => 16#5C5971877501D4B8#]);

   --  1 / P2
   L0_Den_Inv : constant GF2_128.Element :=
     (Limbs => [0 => 16#252A689FEFCCF959#, 1 => 16#FB6E50F87BFCABD9#]);

   --  1 / (1 + P2)
   L1_Den_Inv : constant GF2_128.Element :=
     (Limbs => [0 => 16#9E82A474CF1D1D21#, 1 => 16#8AFD39472A529157#]);

   --  1 / (P2 (1 + P2))
   L2_Den_Inv : constant GF2_128.Element :=
     (Limbs => [0 => 16#BBA8CCEB20D1E478#, 1 => 16#719369BF51AE3A8E#]);

   --  Inv checked at run time (ADR 0037): Ok exactly when R * D = One,
   --  which the body computes and compares; nothing is assumed of Inv.
   procedure Checked_Inv
     (D : GF2_128.Element; R : out GF2_128.Element; Ok : out Boolean)
   with Global => null,
        Post   => (if Ok then GF2_128.Mul (R, D) = GF2_128.One);

   --  reed_solomon_eval_point of the reference: the injection of x
   --  through the subfield basis.
   function Eval_Point (X : Natural) return GF2_128.Element is
     (GF2_128.Inject (X))
   with Pre => X < 2**16;

   --  Section 7.2.2: two bytes little-endian, the coordinates on the
   --  basis. Every string is an element.
   procedure From_Subfield_Bytes
     (B : Bytes.Byte_Array; E : out GF2_128.Element; Ok : out Boolean)
   with Global => null,
        Pre    => B'Length = 2,
        Post   => Ok;

   --  The two bytes, little-endian, of the coordinates of E on the
   --  basis (Section 7.2.2), through the fixed map of GF2_128.
   function To_Subfield_Bytes (E : GF2_128.Element) return Bytes.Byte_Array
   with Global => null,
        Post   => To_Subfield_Bytes'Result'First = 0
                  and then To_Subfield_Bytes'Result'Length = 2;

   --  The associativity of the product (ADR 0066), stated with Same.
   procedure Lemma_Mul_Assoc (A, B, C : GF2_128.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (GF2_128.Mul (GF2_128.Mul (A, B), C),
                     GF2_128.Mul (A, GF2_128.Mul (B, C)));

   --  The other ring laws (ADR 0070), stated with Same.
   procedure Lemma_Mul_Comm (A, B : GF2_128.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (GF2_128.Mul (A, B), GF2_128.Mul (B, A));

   procedure Lemma_Mul_One (A : GF2_128.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (GF2_128.Mul (A, GF2_128.One), A);

   procedure Lemma_Mul_Distrib (A, B, C : GF2_128.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (GF2_128.Mul (A, GF2_128.Add (B, C)),
                     GF2_128.Add (GF2_128.Mul (A, B), GF2_128.Mul (A, C)));

   procedure Lemma_Mul_Distrib_Sub (A, B, C : GF2_128.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (GF2_128.Mul (A, GF2_128.Sub (B, C)),
                     GF2_128.Sub (GF2_128.Mul (A, B), GF2_128.Mul (A, C)));

   procedure Lemma_Add_Assoc (A, B, C : GF2_128.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (GF2_128.Add (GF2_128.Add (A, B), C),
                     GF2_128.Add (A, GF2_128.Add (B, C)));

   procedure Lemma_Add_Comm (A, B : GF2_128.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (GF2_128.Add (A, B), GF2_128.Add (B, A));

   procedure Lemma_Add_Zero (A : GF2_128.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (GF2_128.Add (A, GF2_128.Zero), A);

   procedure Lemma_Add_Neg (A : GF2_128.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (GF2_128.Add (A, GF2_128.Neg (A)), GF2_128.Zero);

   procedure Lemma_Sub_Def (A, B : GF2_128.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (GF2_128.Sub (A, B), GF2_128.Add (A, GF2_128.Neg (B)));

   package Sig is new Field_Signature
     (Element    => GF2_128.Element,
      Zero       => GF2_128.Zero,
      One        => GF2_128.One,
      P2         => P2,
      "+"        => GF2_128.Add,
      "-"        => GF2_128.Sub,
      "*"        => GF2_128.Mul,
      Neg        => GF2_128.Neg,
      L0_Den_Inv => L0_Den_Inv,
      L1_Den_Inv => L1_Den_Inv,
      L2_Den_Inv => L2_Den_Inv,
      Same       => Same,
      Lemma_Mul_Assoc => Lemma_Mul_Assoc,
      Lemma_Mul_Comm  => Lemma_Mul_Comm,
      Lemma_Mul_One   => Lemma_Mul_One,
      Lemma_Mul_Distrib     => Lemma_Mul_Distrib,
      Lemma_Mul_Distrib_Sub => Lemma_Mul_Distrib_Sub,
      Lemma_Add_Assoc => Lemma_Add_Assoc,
      Lemma_Add_Comm  => Lemma_Add_Comm,
      Lemma_Add_Zero  => Lemma_Add_Zero,
      Lemma_Add_Neg   => Lemma_Add_Neg,
      Lemma_Sub_Def   => Lemma_Sub_Def,
      Serialized_Size  => 16,
      To_Bytes         => GF2_128.To_Bytes,
      From_Bytes       => GF2_128.From_Bytes,
      Sampling_Rejects => False,
      Checked_Inv      => Checked_Inv,
      Eval_Point       => Eval_Point,
      Max_Eval_Point   => 2**16 - 1,
      Subfield_Size    => 2,
      From_Subfield_Bytes => From_Subfield_Bytes,
      To_Subfield_Bytes   => To_Subfield_Bytes);

end Field_GF2_128;
