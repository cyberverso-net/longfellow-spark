--  Mdoc_Status: the outcome of the mDoc layer (Phase D, block 5, ADR
--  0058), one value per cause and never an exception, as Prover_Status
--  and Verifier_Status. The layer drives two provers, or two
--  verifiers, on one transcript; when one of them reports a status of
--  its own, the layer says which one (Hash_Failed, Sig_Failed) and
--  hands that status back beside its own (the parameter Detail of
--  Mdoc_Prover.Prove and Mdoc_Verifier.Verify).
--
--    Ok                   the proof was made, or accepted.
--    Transcript_Too_Long  the session transcript exceeds
--                         Device_Auth.Max_Session_Transcript bytes.
--    Attribute_Invalid    a requested attribute does not fit the
--                         layout of the circuit version (the encoded
--                         identifier or the value too long,
--                         Mdoc_Inputs.Fits).
--    Input_Count          the public inputs built from the request
--                         are not as many as the circuit has
--                         (upstream's AttributeNumberMismatch): the
--                         request names a number of attributes the
--                         circuit was not compiled for.
--    E2_Not_In_Field      the device authentication digest is not
--                         below the prime of P-256, so it is no field
--                         element (upstream's builder panics there).
--    Hash_Failed          the prover or the verifier of the hash
--                         circuit reported Detail.
--    Sig_Failed           the same for the signature circuit. On the
--                         verifier's side, Proof_Encoding in Detail
--                         also covers the mDoc proof itself: fewer
--                         than 96 bytes (Hash_Failed), or bytes after
--                         the signature proof (Sig_Failed).
--
--  Documentation: docs/guide/09-mdoc.md. Proof status: an
--  enumeration, nothing to prove.

pragma SPARK_Mode (On);

package Mdoc_Status is

   type Status is
     (Ok,
      Transcript_Too_Long,
      Attribute_Invalid,
      Input_Count,
      E2_Not_In_Field,
      Hash_Failed,
      Sig_Failed);

end Mdoc_Status;
