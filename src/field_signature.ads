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
--  The three constants L0_Den_Inv, L1_Den_Inv and L2_Den_Inv are the
--  inverses of the Lagrange denominators on the evaluation points
--  0, 1, P2 (ADR 0025): d0 = (0 - 1) (0 - P2), d1 = (1 - 0) (1 - P2),
--  d2 = (P2 - 0) (P2 - 1). They are computed by the vector generator,
--  checked there by d * inv (d) = 1, and re-checked at run time by the
--  harness with the library's multiplication; the verifier never
--  calls Inv.

pragma SPARK_Mode (On);

generic
   type Element is private;
   Zero, One, P2 : Element;
   with function "+" (A, B : Element) return Element;
   with function "-" (A, B : Element) return Element;
   with function "*" (A, B : Element) return Element;
   with function Neg (A : Element) return Element;
   L0_Den_Inv, L1_Den_Inv, L2_Den_Inv : Element;
package Field_Signature is
end Field_Signature;
