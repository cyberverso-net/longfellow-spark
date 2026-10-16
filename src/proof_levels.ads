--  Proof_Levels: the assertion level Proof_Only of the project. It
--  depends on the predefined level Static, so that, like SPARKlib's
--  own SPARKlib_Full, it can never be enabled at run time in any build
--  profile: ghost code and contracts at this level are proved by
--  GNATprove for all inputs and are never compiled. Used where a
--  contract is too costly to execute in the assertion-enabled test
--  build: the structural references of stage 5 (Lagrange, the Ligero
--  reader and verifier, ADR 0038) and, since the consolidation after
--  Phase A, the functional contracts and ghost models of the two
--  fields (ADR 0044: on P-256 every multiplication carried a big-
--  integer postcondition). The units that use it say so in their
--  headers; what the test build checks of them is their output against
--  the vectors (ADR 0040, ADR 0044).

pragma Assertion_Level (Proof_Only, Depends => [Static]);

package Proof_Levels is
end Proof_Levels;
