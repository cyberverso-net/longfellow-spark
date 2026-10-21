--  Prover_Status: the outcome of the prover's validation of its inputs
--  (Phase C, ADR 0049). One value per cause, no exceptions, as
--  Verifier_Status and Circuit_Status.
--
--    Ok               the inputs are admissible and the proof was made
--    Input_Length     the inputs are not ninput elements
--    Input_Not_One    the circuit has public inputs and the first is
--                     not 1 (OneWire, ADR 0064)
--    Not_Satisfied    an output of layer 0 is not zero or a Z assertion
--                     fails: the inputs do not satisfy the circuit
--    Not_In_Subfield  on GF(2^128), a private input below the subfield
--                     boundary that does not lie in GF(2^16) (the
--                     reference prover panics there); unreachable on
--                     P-256, its own subfield
--    Config_Invalid   the Ligero configuration violates Section 4.2.1
--                     or its geometry does not fit this implementation
--
--  Documentation: docs/guide/07-prover.md. Proof status: an
--  enumeration, nothing to prove.

pragma SPARK_Mode (On);

package Prover_Status is

   type Status is
     (Ok,
      Input_Length,
      Input_Not_One,
      Not_Satisfied,
      Not_In_Subfield,
      Config_Invalid,
      Exhausted);
   --  Exhausted: the transcript's generator passed its bound while the
   --  prover drew the Ligero challenges or chose the columns (ADR
   --  0028), as the verifier's status of the same name; no proof is
   --  produced. Added at block 5 (ADR 0049).

end Prover_Status;
