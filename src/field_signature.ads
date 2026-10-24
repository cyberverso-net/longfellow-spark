--  Field_Signature: what the protocol code needs from a field.
--
--  A signature package (ADR 0024): a generic with formal parameters
--  only and nothing declared inside. Its instances carry no code;
--  they exist so that a protocol unit can take a whole field, type
--  and operations and constants together, as one formal package
--  parameter (`with package F is new Field_Signature (<>)`) instead
--  of a dozen formal subprograms at every instantiation.
--
--  GF2_128 and P256_Field each satisfy it through a thin wrapper
--  (Field_GF2_128, Field_P256) that names their operations and the
--  constants of ADR 0025. GNATprove analyses the instances of the
--  protocol units, not the generics, so every proof of protocol code
--  is made once per field with the actual contracts visible.
--
--  Equality is the predefined "=" of the formal private type. Neg is
--  listed separately from "-" because the reference implementation
--  uses the negation of One (mone) as a coefficient.
--
--  Same is the logical equality of the element type, for contracts
--  only: a ghost function that GNATprove interprets, through the
--  annotation Logical_Equal on the actual, as equality of terms, so
--  that two elements proved Same can be substituted for each other
--  under any function (congruence). The predefined "=" of a record
--  with an array component is encoded as a pointwise predicate, which
--  gives no congruence through an opaque function; the structural
--  proofs of the protocol code (ADR 0023) need congruence and state
--  their equalities with Same. The actual's body returns the
--  predefined "=" and is outside SPARK, so that it executes in the
--  test build and is assumed, not checked, by the provers; what is
--  proved with Same implies the predefined equality.
--
--  Serialisation and sampling (stage 4, ADR 0028). Serialized_Size is
--  the byte length of an element (draft Section 7.2.1), To_Bytes its
--  canonical little-endian encoding and From_Bytes the inverse: Ok
--  exactly when the bytes are a canonical encoding (below p for P-256,
--  always for GF(2^128)). Sampling_Rejects says whether the sampler of
--  Section 3.4.3 can reject a draw: the generic glue of the transcript
--  draws Serialized_Size bytes and repeats until From_Bytes accepts,
--  and its termination is proved exactly when Sampling_Rejects is
--  False (ADR 0030). The actuals take the field's fixed byte subtype
--  (Bytes_32, Bytes_16); callers pass arrays of Serialized_Size bytes
--  indexed from 0.
--
--  The three constants L0_Den_Inv, L1_Den_Inv and L2_Den_Inv are the
--  inverses of the Lagrange denominators on the evaluation points
--  0, 1, P2 (ADR 0025): d0 = (0 - 1) (0 - P2), d1 = (1 - 0) (1 - P2),
--  d2 = (P2 - 0) (P2 - 1). They are computed by the vector generator,
--  checked there by d * inv (d) = 1, and re-checked at run time by the
--  harness with the library's multiplication; the verifier never
--  calls Inv.
--
--  The laws of a commutative ring, as ghost lemmas stated with Same.
--  Each field proves them for its own operations.
--    Lemma_Mul_Assoc       (A * B) * C = A * (B * C) (ADR 0066), for
--                          the Lagrange tables of the verifier;
--    Lemma_Mul_Comm        A * B = B * A;
--    Lemma_Mul_One         A * One = A;
--    Lemma_Mul_Distrib     A * (B + C) = A * B + A * C;
--    Lemma_Mul_Distrib_Sub A * (B - C) = A * B - A * C;
--    Lemma_Add_Assoc       (A + B) + C = A + (B + C);
--    Lemma_Add_Comm        A + B = B + A;
--    Lemma_Add_Zero        A + Zero = A;
--    Lemma_Add_Neg         A + Neg (A) = Zero;
--    Lemma_Sub_Def         A - B = A + Neg (B).
--  All but the first are for the kernels of the sumcheck in upstream's
--  form (ADR 0070).

pragma SPARK_Mode (On);

with Bytes;
with Proof_Levels;

--  A signature package references none of its formals itself.
pragma Warnings (Off, "is not referenced");

generic
   type Element is private;
   Zero, One, P2 : Element;
   with function "+" (A, B : Element) return Element;
   with function "-" (A, B : Element) return Element;
   with function "*" (A, B : Element) return Element;
   with function Neg (A : Element) return Element;
   L0_Den_Inv, L1_Den_Inv, L2_Den_Inv : Element;
   with function Same (A, B : Element) return Boolean with Ghost;
   with procedure Lemma_Mul_Assoc (A, B, C : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Mul_Comm (A, B : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Mul_One (A : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Mul_Distrib (A, B, C : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Mul_Distrib_Sub (A, B, C : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Add_Assoc (A, B, C : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Add_Comm (A, B : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Add_Zero (A : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Add_Neg (A : Element)
     with Ghost => Proof_Only;
   with procedure Lemma_Sub_Def (A, B : Element)
     with Ghost => Proof_Only;
   Serialized_Size : Positive;
   with function To_Bytes (E : Element) return Bytes.Byte_Array;
   with procedure From_Bytes
     (B : Bytes.Byte_Array; E : out Element; Ok : out Boolean);
   Sampling_Rejects : Boolean;
   --  Stage 5 (ADR 0036, 0037): a checked inverse, the Reed-Solomon
   --  evaluation point of column X, and the decoding of a subfield
   --  element of Subfield_Size bytes (draft Section 7.2.2; the field
   --  itself for P-256, 2 bytes on the basis for GF(2^128)).
   with procedure Checked_Inv (D : Element; R : out Element; Ok : out Boolean);
   with function Eval_Point (X : Natural) return Element;
   Max_Eval_Point : Natural;
   Subfield_Size : Positive;
   with procedure From_Subfield_Bytes
     (B : Bytes.Byte_Array; E : out Element; Ok : out Boolean);
   --  The Subfield_Size bytes of an element of the subfield (Section
   --  7.2.2), the inverse of From_Subfield_Bytes there; the prover's
   --  writer uses it on the subfield rows of the tableau (Phase C, ADR
   --  0051). On an element outside the subfield the result is
   --  unspecified; the prover checks membership first.
   with function To_Subfield_Bytes (E : Element) return Bytes.Byte_Array;
package Field_Signature is
end Field_Signature;
