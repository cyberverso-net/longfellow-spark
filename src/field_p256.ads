--  Field_P256: the P-256 base field as a Field_Signature instance
--  (ADR 0024, ADR 0025).
--
--  P2 = 2, the third sumcheck evaluation point for fields of odd
--  characteristic (draft-03 Section 6.4). The Lagrange denominators
--  are d0 = (0 - 1) (0 - 2) = 2, d1 = (1 - 0) (1 - 2) = -1 and
--  d2 = (2 - 0) (2 - 1) = 2, so the inverses are (p + 1) / 2, p - 1
--  and (p + 1) / 2. They are computed by
--  tests/vectors/gen_sumcheck_vectors.py (checked by d * inv (d) = 1)
--  and re-checked by the harness sumcheck_kat with Mul at every run.
--  Limbs are little-endian, as in P256_Field.

pragma SPARK_Mode (On);

with Bytes;
with P256_Field;
with Field_Signature;
with Proof_Levels;

package Field_P256 is

   use type P256_Field.Element;

   --  Logical equality for contracts (see Field_Signature). The body
   --  is the predefined "=", outside SPARK; the provers treat Same as
   --  equality of terms (annotation Logical_Equal).
   function Same (A, B : P256_Field.Element) return Boolean with
     Ghost, Global => null, Annotate => (GNATprove, Logical_Equal);

   --  The constants are written as their canonical integers and put in
   --  the Montgomery form of P256_Field at elaboration (ADR 0069).
   P2 : constant P256_Field.Element := P256_Field.Of_Natural (2);

   --  (p + 1) / 2 = 1 / 2
   Half : constant P256_Field.Element :=
     P256_Field.From_Canonical
       ([16#0000000000000000#, 16#0000000080000000#,
         16#8000000000000000#, 16#7FFFFFFF80000000#]);

   --  p - 1 = -1 = 1 / (-1)
   Minus_One : constant P256_Field.Element :=
     P256_Field.From_Canonical
       ([16#FFFFFFFFFFFFFFFE#, 16#00000000FFFFFFFF#,
         16#0000000000000000#, 16#FFFFFFFF00000001#]);

   --  Inv checked at run time (ADR 0037): Ok exactly when R * D = One,
   --  which the body computes and compares; nothing is assumed of Inv.
   procedure Checked_Inv
     (D : P256_Field.Element; R : out P256_Field.Element; Ok : out Boolean)
   with Global => null,
        Post   => (if Ok then P256_Field.Mul (R, D) = P256_Field.One);

   --  reed_solomon_eval_point of the reference: the integer x.
   function Eval_Point (X : Natural) return P256_Field.Element is
     (P256_Field.Of_Natural (X));

   --  The subfield of P-256 is P-256 itself: the encoding of 7.2.1.
   procedure From_Subfield_Bytes
     (B : Bytes.Byte_Array; E : out P256_Field.Element; Ok : out Boolean)
   with Global => null,
        Pre    => B'Length = 32;

   --  P-256 is its own subfield: the encoding of 7.2.1.
   function To_Subfield_Bytes (E : P256_Field.Element) return Bytes.Byte_Array
   is (P256_Field.To_Bytes (E))
   with Global => null;

   --  The associativity of the product (ADR 0066), stated with Same.
   procedure Lemma_Mul_Assoc (A, B, C : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (P256_Field.Mul (P256_Field.Mul (A, B), C),
                     P256_Field.Mul (A, P256_Field.Mul (B, C)));

   --  The other ring laws (ADR 0070), stated with Same.
   procedure Lemma_Mul_Comm (X, Y : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (P256_Field.Mul (X, Y), P256_Field.Mul (Y, X));

   procedure Lemma_Mul_One (A : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (P256_Field.Mul (A, P256_Field.One), A);

   procedure Lemma_Mul_Distrib (A, B, C : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (P256_Field.Mul (A, P256_Field.Add (B, C)),
                     P256_Field.Add (P256_Field.Mul (A, B),
                                     P256_Field.Mul (A, C)));

   procedure Lemma_Mul_Distrib_Sub (A, B, C : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (P256_Field.Mul (A, P256_Field.Sub (B, C)),
                     P256_Field.Sub (P256_Field.Mul (A, B),
                                     P256_Field.Mul (A, C)));

   procedure Lemma_Add_Assoc (A, B, C : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (P256_Field.Add (P256_Field.Add (A, B), C),
                     P256_Field.Add (A, P256_Field.Add (B, C)));

   procedure Lemma_Add_Comm (X, Y : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (P256_Field.Add (X, Y), P256_Field.Add (Y, X));

   procedure Lemma_Add_Zero (A : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (P256_Field.Add (A, P256_Field.Zero), A);

   procedure Lemma_Add_Neg (A : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (P256_Field.Add (A, P256_Field.Neg (A)), P256_Field.Zero);

   procedure Lemma_Sub_Def (A, B : P256_Field.Element) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Same (P256_Field.Sub (A, B),
                     P256_Field.Add (A, P256_Field.Neg (B)));

   package Sig is new Field_Signature
     (Element    => P256_Field.Element,
      Zero       => P256_Field.Zero,
      One        => P256_Field.One,
      P2         => P2,
      "+"        => P256_Field.Add,
      "-"        => P256_Field.Sub,
      "*"        => P256_Field.Mul,
      Neg        => P256_Field.Neg,
      L0_Den_Inv => Half,
      L1_Den_Inv => Minus_One,
      L2_Den_Inv => Half,
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
      Serialized_Size  => 32,
      To_Bytes         => P256_Field.To_Bytes,
      From_Bytes       => P256_Field.From_Bytes,
      Sampling_Rejects => True,
      Checked_Inv      => Checked_Inv,
      Eval_Point       => Eval_Point,
      Max_Eval_Point   => Natural'Last - 1,
      Subfield_Size    => 32,
      From_Subfield_Bytes => From_Subfield_Bytes,
      To_Subfield_Bytes   => To_Subfield_Bytes);

end Field_P256;
