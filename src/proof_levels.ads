--  Proof_Levels: the assertion level Proof_Only of the project. It
--  depends on the predefined level Static, so that, like SPARKlib's
--  own SPARKlib_Full, it can never be enabled at run time in any build
--  profile: ghost code and contracts at this level are proved by
--  GNATprove for all inputs and are never compiled. Used where a
--  contract is too costly to execute in the assertion-enabled test
--  build: the functional contracts and ghost models of the fields
--  (ADR 0044: on P-256 every multiplication carried a big-integer
--  postcondition), the structural references of Lagrange and of the
--  Ligero reader and verifier (ADR 0038), and the costly references of
--  the circuit, sumcheck, prover and mDoc units. The units that use it
--  say so in their headers; what the test build checks of them is
--  their output against the vectors (ADR 0040, ADR 0044). That the
--  compiled code agrees with the source GNATprove proved is trusted
--  (register row T8). This unit has no check of its own.
--
--  Documentation: docs/guide/00-primer-spark.md, B4.2 (assertion
--  levels); docs/guide/01-gf2_128.md, Section 3.

pragma Assertion_Level (Proof_Only, Depends => [Static]);

package Proof_Levels is
end Proof_Levels;
