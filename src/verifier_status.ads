--  Verifier_Status: the one status enumeration of the Ligero verifier,
--  its readers and the complete verifier (ADR 0039): one value per
--  cause the code can produce, and never an exception.
--
--    Ok                     accepted.
--    Public_Input_Length    the public inputs are not the circuit's.
--    Public_Input_Not_One   the circuit has public inputs and the first
--                           is not 1 (OneWire of upstream's Lean proofs,
--                           ADR 0064; stricter than upstream).
--    Queried_Columns_Length the opened columns are not NROW * NREQ.
--    Polynomial_Lengths     a response polynomial, the nonces or the
--                           path capacity do not match the geometry.
--    Exhausted              the transcript's generator passed its bound
--                           (ADR 0028); the challenges are not usable.
--    Merkle_Failed          the opened columns are not in the root.
--    Matrix_Failed          the Reed-Solomon tables could not be built:
--                           a denominator without a checked inverse
--                           (ADR 0037) or an evaluation point beyond
--                           the field's range.
--    LDT_Failed             the low-degree test (4.5, verify_ldt).
--    Linear_Failed          the linear test's evaluations (verify_dot).
--    Linear_Sum_Failed      the linear test's sum check (verify_dot).
--    Quadratic_Failed       the quadratic test (verify_quad).
--    Proof_Encoding         the proof string: a non-canonical element,
--                           a run-length violation, a count that does
--                           not fit, bytes missing or trailing.
--
--  Documentation: docs/guide/05-ligero.md. Index: docs/adr/README.md.

pragma SPARK_Mode (On);

package Verifier_Status is

   type Status is
     (Ok,
      Public_Input_Length,
      Public_Input_Not_One,
      Queried_Columns_Length,
      Polynomial_Lengths,
      Exhausted,
      Merkle_Failed,
      Matrix_Failed,
      LDT_Failed,
      Linear_Failed,
      Linear_Sum_Failed,
      Quadratic_Failed,
      Proof_Encoding);

end Verifier_Status;
