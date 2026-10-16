--  Proof_Levels: the assertion level Proof_Only of the project. It
--  depends on the predefined level Static, so that, like SPARKlib's
--  own SPARKlib_Full, it can never be enabled at run time in any build
--  profile: ghost code and contracts at this level are proved by
--  GNATprove for all inputs and are never compiled. Used where a
--  structural reference is too costly to execute in the assertion-
--  enabled test build (Lagrange, stage 5: on P-256 every multiplication
--  carries a big-integer postcondition, and a recursive reference in a
--  loop invariant multiplies the count by the loop length). The units
--  that use it say so in their headers; what the test build checks of
--  them is their output against the vectors (ADR 0038, ADR 0040).

pragma Assertion_Level (Proof_Only, Depends => [Static]);

package Proof_Levels is
end Proof_Levels;
