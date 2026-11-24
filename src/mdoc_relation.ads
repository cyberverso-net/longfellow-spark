--  Mdoc_Relation: the relations the two circuits of the version 7
--  pair are meant to establish, written at the level of bytes and
--  words, for the milestone Certified circuits (ADR 0091). A relation
--  says, of the public inputs X and the private inputs W of one
--  circuit, what must be true of them when the circuit accepts. The
--  checker of the milestone will prove, for the registered circuit,
--  that an evaluation that accepts implies the relation; that proof
--  is not here.
--
--  The children:
--
--    Mdoc_Relation.Hash : the hash circuit, over GF(2^128) (block 1)
--    Mdoc_Relation.Sig  : the signature circuit, over P-256 (block 6)
--
--  Documentation: docs/guide/10-certified-circuits.md, Section 1.
--
--  Ghost. The release build ignores the package and its children; a
--  build with assertions enabled (-gnata) compiles and executes them,
--  so that the tests evaluate a relation on the inputs of a proof.
--  Nothing outside the tests and the proofs refers to them.
--
--  Proof status: this unit has no code of its own.

pragma SPARK_Mode (On);

package Mdoc_Relation with Ghost is
end Mdoc_Relation;
