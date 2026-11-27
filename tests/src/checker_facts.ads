--  Checker_Facts: the digest of a circuit's facts as scripts/census.py
--  computes it (ADR 0093), from the checker's own computation: for each
--  layer from the last, Layer_Coefficients gives its slots and their
--  coefficients and Next_Layer the meanings of its wires; the facts are
--  written in census.py's order and bytes and digested with SHA-256.
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. For a
--  certificate the walk accepted.

pragma SPARK_Mode (Off);

with Bytes;
with Circuit_Certificates;
with Sumcheck_Algebra;
with Packed_Circuits;
with Circuit_Checker;

generic
   with package SA is new Sumcheck_Algebra (<>);
   with package PC is new Packed_Circuits (SA);
   with package CK is new Circuit_Checker (SA, PC, others => <>);
   --  The instance's Max_Layer_Slots.
   Pool_Size : Positive;
   --  The field's bytes of an element, as in the circuit file.
   with function To_Bytes (E : SA.Element) return Bytes.Byte_Array;
package Checker_Facts is

   function Facts_Digest
     (P : PC.Packed_Circuit; K : Circuit_Certificates.Certificate)
      return Bytes.Bytes_32;

end Checker_Facts;
