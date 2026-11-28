--  Circuit_Check: the checker on two files, a circuit and its
--  certificate (ADR 0093). It reads the circuit with the verifier's
--  reader in its packed form, reads the certificate, compares the
--  certificate's circuit identifier with the circuit's, and walks.
--
--  The comparison of the identifiers is a guard against passing the
--  wrong file, no part of the theorem: the link between certificate and
--  circuit that the statement rests on is the structure the walk checks
--  (Circuit_Checker.Accepts) and the digests of register row T9.
--
--  Documentation: docs/guide/10-certified-circuits.md, Section 3.
--  Decisions: ADR 0093.
--
--  Proof status (per instance): Silver, no run-time error on any bytes.
--  The walk's own statement is Circuit_Checker's.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, circuits and
--  their certificates are public data (register row S4).

pragma SPARK_Mode (On);

with Bytes; use Bytes;
with Circuit_Status;
with Circuit_Certificates;
with Sumcheck_Algebra;
with Packed_Circuits;
with Circuit_Reader;
with Circuit_Checker;

generic
   with package SA is new Sumcheck_Algebra (<>);
   with package PC is new Packed_Circuits (SA);
   with package CR is new Circuit_Reader (SA, PC, others => <>);
   with package CK is new Circuit_Checker (SA, PC, others => <>);
package Circuit_Check is

   package CC renames Circuit_Certificates;

   --  Where the check stopped.
   type Outcome is
     (Accepted,             --  the walk accepts
      Circuit_Refused,      --  the circuit file is refused by its reader
      Certificate_Refused,  --  the certificate is refused by its reader
      Wrong_Circuit,        --  the certificate names another circuit
      Walk_Refused);        --  the walk refuses the certificate

   --  The statuses of the steps that ran; a step that did not run has
   --  its first refusal (Bad_Magic, Cert_Mismatch), not to be read.
   type Result is record
      Outcome     : Circuit_Check.Outcome;
      Circuit     : Circuit_Status.Status;  --  the circuit reader's
      Certificate : CC.Status;              --  the certificate reader's
      Walk        : CK.Status;              --  the walk's
      Id          : Bytes_32;               --  the circuit's identifier,
                                            --  as its header gives it
                                            --  (zeros when it is refused)
   end record;

   procedure Check
     (Circuit_File     : Byte_Array;
      Certificate_File : Byte_Array;
      R                : out Result)
   with
     Global => null,
     Pre    => Circuit_File'First = 0 and then Certificate_File'First = 0,
     Post   => (R.Outcome = Accepted) = CK."=" (R.Walk, CK.Accepted);

end Circuit_Check;
