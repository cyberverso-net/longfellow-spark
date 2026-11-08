--  Device_Auth: the digest the device signed, e2, from the session
--  transcript and the document type (longfellow-zk/longfellow-zk
--  d5e6be7, rust/applications/mdoc_zk/circuits/src/cbor/mdoc.rs,
--  compute_transcript_hash; Phase D, block 5, ADR 0058).
--
--  In ISO 18013-5 the holder's device signs, with the key the
--  credential carries, the structure
--
--    DeviceAuthentication = [ "DeviceAuthentication", SessionTranscript,
--                             docType, deviceNameSpaces ]
--
--  inside the COSE Sig_structure of a COSE_Sign1 with the protected
--  header {1: -7} (ES256) and no external data:
--
--    Sig_structure = [ "Signature1", protected, external_aad, payload ]
--
--  where the payload is the DeviceAuthentication array wrapped in a
--  byte string under CBOR tag 24. e2 is SHA-256 of the Sig_structure.
--  The signature circuit verifies the device's ECDSA signature on e2,
--  so e2 is a public input of that circuit (Mdoc_Inputs.Sig_Inputs):
--  the verifier computes it from the session transcript and the
--  document type it knows, and so does the prover of this block, since
--  the witness files carry no digest; the prover of block 6 takes it
--  from the parsed credential, which is the same value by construction.
--
--  The bytes, in the order they reach SHA-256:
--
--    84 6A "Signature1" 43 A1 01 26 40      the fixed head: an array of
--                                           four, the text "Signature1",
--                                           the protected header as a
--                                           byte string of three bytes
--                                           (a map {1: -7}), an empty
--                                           byte string
--    byte-string head of the payload length
--    D8 18                                  tag 24
--    byte-string head of the array's length
--    84 74 "DeviceAuthentication"           an array of four, the text
--    the session transcript bytes as given  (already CBOR)
--    text-string head of the document type, the document type
--    D8 18 41 A0                            tag 24 of an empty map
--
--  The session transcript is bounded at Max_Session_Transcript bytes,
--  65,000, which upstream's pull request 223 proposes for its C++
--  entry point (not merged at d5e6be7; to be re-read with issue #122).
--  The bound is a precondition here and a status of the layer
--  (Mdoc_Status.Transcript_Too_Long); the command-line tools check it
--  before calling. The document type is bounded at Max_Doc_Type bytes,
--  65,535, the longest length a CBOR head of three bytes carries:
--  upstream takes any length, and this bound exists so that the
--  lengths added below are proved not to overflow; a document type of
--  ISO 18013-5 is a few dozen bytes (ADR 0058 records both bounds).
--
--  Documentation: docs/guide/09-mdoc.md.
--
--  Proof status. Silver. That the digest is the one upstream computes
--  is tested against the Python transcription of the layout
--  (tests/vectors/mdoc_layer.txt, gen_mdoc_layer_vectors.py) and
--  against the signature circuit's public inputs in upstream's witness
--  files, which hold e2 as the fourth element.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE. The session
--  transcript and the document type are the relying party's public
--  data.

pragma SPARK_Mode (On);

with Bytes; use Bytes;

package Device_Auth is

   Max_Session_Transcript : constant := 65_000;
   Max_Doc_Type           : constant := 65_535;

   function Digest (Session, Doc_Type : Byte_Array) return Bytes_32 with
     Global => null,
     Pre    => Session'Length <= Max_Session_Transcript
               and then Doc_Type'Length <= Max_Doc_Type;

end Device_Auth;
