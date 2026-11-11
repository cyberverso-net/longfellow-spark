--  Mdoc_Status: the outcome of the mDoc layer (Phase D, blocks 5 and
--  6, ADR 0058, ADR 0086), one value per cause and never an exception,
--  as Prover_Status and Verifier_Status. The layer drives two provers, or two
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
--  From the document (block 6, Mdoc_Prover.Prove_Mdoc):
--
--    Parse_Failed         the credential did not parse; the parser's
--                         status is handed back beside this one.
--    Attribute_Not_Found  a requested attribute is not an item of the
--                         document (upstream's AttributeNotFound).
--    Attribute_Too_Long   the item does not pad into two SHA-256
--                         blocks (above 119 bytes; upstream's
--                         AttributeTooLong refuses 256 and above).
--    Item_Order_Unsupported
--                         at version 6, the item's elementValue entry
--                         does not follow its elementIdentifier entry,
--                         the one order the version 6 circuit frames
--                         (#150; upstream's builder has no such status
--                         and its circuit refuses the proof).
--    Signature_Not_Canonical
--                         a signature value s of the document is not
--                         below the group order, which the ECDSA
--                         witness requires (upstream stops there).
--
--  From the profile (#79, ADR 0089, Mdoc_Spec.Select_Profile, the
--  entry points Mdoc_Prover.Prove_Profile and
--  Mdoc_Verifier.Verify_Profile):
--
--    Profile_Unknown      the name is not the combined identifier of a
--                         row of the supported profile.
--    Profile_Mismatch     the circuits given are not the row's (their
--                         identifiers), or do not fit its Ligero
--                         configurations, or a buffer is not of the
--                         row's length.
--    Attribute_Count      the request does not hold the row's number of
--                         attributes (one, for both rows: two to four
--                         are refused until an archive is pinned).
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
      Sig_Failed,
      Parse_Failed,
      Attribute_Not_Found,
      Attribute_Too_Long,
      Item_Order_Unsupported,
      Signature_Not_Canonical,
      Profile_Unknown,
      Profile_Mismatch,
      Attribute_Count);

end Mdoc_Status;
