--  Mdoc_Prover: the prover of an mDoc proof of age, run_mdoc_prover_inner
--  of the reference from the witnesses on (longfellow-zk/longfellow-zk
--  d5e6be7, rust/applications/mdoc_zk/runtime/src/prover.rs; Phase D,
--  block 5, ADR 0058), on the two phases of Zk_Prover (ADR 0085).
--  Generic over the two prover chains, one per field, so that the
--  library instance (Mdoc_Prover_Lib, the test source Simple_Rng) is
--  proved and the command line instantiates it again with the
--  operating system's source, as the single-circuit prover does.
--
--  The flow, in the reference's order:
--
--    1. The session transcript opens the transcript (Transcript.Reset
--       with its bytes as the label: Transcript::new (transcript)).
--    2. Commit the hash circuit on its private inputs: the root goes
--       to the transcript (Zk_Prover.Commit).
--    3. Commit the signature circuit the same way.
--    4. Draw av: 16 bytes from the transcript, the 128-bit value
--       little-endian (tp.u128 ()).
--    5. The six tags from the three messages, av and mac_ap
--       (Mdoc_Mac.Legacy_Tags).
--    6. The public inputs of the hash circuit from the attributes, the
--       date, the tags and av; those of the signature circuit from the
--       issuer's key, e2 (Device_Auth) and the same tags and av
--       (Mdoc_Inputs).
--    7. Prove the hash circuit on its public inputs (Prove_Committed:
--       the statement, the sumcheck, the Ligero proof).
--    8. Prove the signature circuit the same way.
--    9. The proof: the tags, the hash proof, the signature proof
--       (Mdoc_Proof).
--
--  Steps 2 and 3 come before step 4 so that av depends on both
--  commitments: a prover that could choose its tags after seeing av
--  could bind two unrelated witnesses. In this block the private
--  inputs, mac_ap and the three messages come from upstream's witness
--  files (Mdoc_Inputs.Witness_Parts); block 6 builds them from the
--  credential (Prove_Mdoc: the parse, the two witnesses, then Prove;
--  ADR 0086). The checks that do not need the transcript come first:
--  the transcript's bound, the attributes against the version's
--  layout, the counts of the public inputs against the circuits'.
--
--  Prove_Profile is the entry point of the supported profile (ADR
--  0089): the profile checked first, then Prove_Mdoc with the row's
--  values; the claims of chapter 9 Section 6 are scoped to it, and
--  Prove and Prove_Mdoc stay for reference work.
--
--  Documentation: docs/guide/09-mdoc.md.
--
--  Proof status (per instance). Silver with the ownership checks on
--  the two commitments and the two proof buffers; the statuses as
--  stated in the postconditions. Completeness (upstream's verifier and
--  Mdoc_Verifier accept the proof) is tested: the round trip of the
--  cli step on both archives, from the witness files and from the
--  documents, and the cross-check with upstream's verifier (chapter 9).
--
--  Constant-time discipline (ADR 0051, ADR 0086): the witness, mac_ap
--  and the messages are secret and go to units that keep the discipline
--  (Zk_Prover, Mdoc_Mac); the public inputs, av, the tags and the proof
--  are public. This unit adds no branch on a secret. Prove_Mdoc calls
--  the parse of the credential (Mdoc_Parse), which ADR 0086 declares
--  outside the discipline: its time depends on the credential's
--  structure and on the bytes of its text strings, not on its
--  signatures, digests or coordinates; the discipline applies to the
--  values once extracted, in the witness builders.
--
--  The pads. Prove_Profile, Prove_Mdoc and Prove take the one-time pads
--  of the MAC (Ap, mac_ap) from their caller, who draws them fresh,
--  secret and uniform for each proof: the tags hide the bound values
--  only under such pads, and pads used under two challenges reveal
--  them (chapter 9 Section 1.3; ADR 0089, the caller's obligations).
--  longfellow_prove_mdoc draws them for each proof; drawing them here
--  is deferred to Phase E (#156).

pragma SPARK_Mode (On);

with Interfaces;       use type Interfaces.Unsigned_8;
with Bytes;            use Bytes;
with Ligero_Geometry;  use Ligero_Geometry;
with Prover_Status;
with Mdoc_Status;
with GF2_128;
with Mdoc_Mac;
with Mdoc_Inputs;      use Mdoc_Inputs;
with Cbor_Parse;
with Mdoc_Parse;
with Mdoc_Witness;
with Mdoc_Spec;
with Mdoc_Proof;
with Device_Auth;
with P256_Field;
with Ligero_Prover;
with Zk_Prover;
with Ligero_Verifier_GF2_128;
with Ligero_Verifier_P256;
with Packed_HQuad_GF2_128;
with Packed_HQuad_P256;
with Packed_Circuits_GF2_128;
with Packed_Circuits_P256;
with Proof_Levels;

generic
   with package LPRH is new Ligero_Prover
     (LV => Ligero_Verifier_GF2_128, others => <>);
   with package ZKH is new Zk_Prover
     (LPR => LPRH, PH => Packed_HQuad_GF2_128, others => <>);
   with package LPRS is new Ligero_Prover
     (LV => Ligero_Verifier_P256, others => <>);
   with package ZKS is new Zk_Prover
     (LPR => LPRS, PH => Packed_HQuad_P256, others => <>);
package Mdoc_Prover is

   pragma Suppress (Predicate_Check);

   use type Mdoc_Status.Status;
   use type Prover_Status.Status;
   use type Mdoc_Parse.Status;
   use type GF2_128.Element;
   use type P256_Field.Element;

   package PCH renames Packed_Circuits_GF2_128;
   package PCS renames Packed_Circuits_P256;

   subtype Hash_Circuit is ZKH.Packed_Circuit;
   subtype Sig_Circuit is ZKS.Packed_Circuit;
   subtype Hash_Elements is ZKH.Element_Array;
   subtype Sig_Elements is ZKS.Element_Array;

   --  The identifier, the subfield boundary (both from the circuit
   --  file's header) and the Ligero configuration (from the
   --  specification) of one circuit.
   type Circuit_Info is record
      Id  : Bytes_32;
      Sfb : Natural;
      Cfg : Config;
   end record;

   --  What the prover asks of a circuit, as Zk_Prover does: the
   --  executable part, checked by the command line where the circuit
   --  enters the program (ADR 0072), and the loader's postcondition at
   --  level Proof_Only.
   function Hash_Ok (P : Hash_Circuit; Cfg : Config) return Boolean is
     (PCH.Indices_Ok (P) and then PCH.Layers_Ok (P)
      and then SAH.Shape_Ok (PCH.Shape_Of (P))
      and then ZKH.Config_Fits (Cfg, ZKH.Shape_Of (P))
      and then P.Ninput >= 1)
   with Global => null;

   function Sig_Ok (P : Sig_Circuit; Cfg : Config) return Boolean is
     (PCS.Indices_Ok (P) and then PCS.Layers_Ok (P)
      and then SAP.Shape_Ok (PCS.Shape_Of (P))
      and then ZKS.Config_Fits (Cfg, ZKS.Shape_Of (P))
      and then P.Ninput >= 1)
   with Global => null;

   function Hash_Valid (P : Hash_Circuit) return Boolean is
     (PCH.Valid (P) and then SAH.Well_Formed (PCH.Expand (P)))
   with Ghost => Proof_Only, Global => null;

   function Sig_Valid (P : Sig_Circuit) return Boolean is
     (PCS.Valid (P) and then SAP.Well_Formed (PCS.Expand (P)))
   with Ghost => Proof_Only, Global => null;

   --  A bound on each proof, so that the length of the whole has no
   --  overflow; the real proofs are below 2^18 bytes.
   Max_Part : constant := 2**28;

   function Parts_Fit
     (Hash_P : Hash_Circuit; HI : Circuit_Info;
      Sig_P  : Sig_Circuit;  SI : Circuit_Info) return Boolean
   is
     (ZKH.Max_Proof_Len (HI.Cfg, ZKH.Shape_Of (Hash_P), HI.Sfb) <= Max_Part
      and then
      ZKS.Max_Proof_Len (SI.Cfg, ZKS.Shape_Of (Sig_P), SI.Sfb) <= Max_Part)
   with Global => null,
        Pre => Hash_Ok (Hash_P, HI.Cfg) and then Sig_Ok (Sig_P, SI.Cfg);

   --  The bytes an mDoc proof may take: the tags and the two proofs at
   --  their longest.
   function Max_Len
     (Hash_P : Hash_Circuit; HI : Circuit_Info;
      Sig_P  : Sig_Circuit;  SI : Circuit_Info) return Positive
   is
     (Mdoc_Proof.Tags_Len
      + ZKH.Max_Proof_Len (HI.Cfg, ZKH.Shape_Of (Hash_P), HI.Sfb)
      + ZKS.Max_Proof_Len (SI.Cfg, ZKS.Shape_Of (Sig_P), SI.Sfb))
   with Global => null,
        Pre => Hash_Ok (Hash_P, HI.Cfg) and then Sig_Ok (Sig_P, SI.Cfg)
               and then Parts_Fit (Hash_P, HI, Sig_P, SI);

   --  Hash_Priv and Sig_Priv are the private inputs of the two circuits
   --  (ninput - npublic each; the count is checked by Commit); Ap and M
   --  are mac_ap and the three messages the tags bind; Pk_X and Pk_Y the
   --  issuer's public key; Session the session transcript bytes; Attrs
   --  the requested attributes with their values as the relying party
   --  states them; Now the date; Doc_Type the document type. B (0 ..
   --  Len - 1) holds the mDoc proof when St is Ok; otherwise Len is 0,
   --  B is zero, and Detail is the status of the failing prover when St
   --  says one failed. The global state is synthesised: the transcript
   --  and the randomness sources behind the two chains.
   procedure Prove
     (Version    : Version_Number;
      Hash_P     : Hash_Circuit;
      HI         : Circuit_Info;
      Sig_P      : Sig_Circuit;
      SI         : Circuit_Info;
      Hash_Priv  : Hash_Elements;
      Sig_Priv   : Sig_Elements;
      Ap         : Mdoc_Mac.Pads;
      M          : Mdoc_Mac.Messages;
      Pk_X, Pk_Y : P256_Field.Element;
      Session    : Byte_Array;
      Attrs      : Attribute_List;
      Now        : Byte_Array;
      Doc_Type   : Byte_Array;
      B          : out Byte_Array;
      Len        : out Natural;
      St         : out Mdoc_Status.Status;
      Detail     : out Prover_Status.Status)
   with
     Always_Terminates => False,
     Pre               =>
       (Runtime    =>
          Hash_Ok (Hash_P, HI.Cfg) and then Sig_Ok (Sig_P, SI.Cfg)
          and then Parts_Fit (Hash_P, HI, Sig_P, SI)
          and then Hash_Priv'First = 0 and then Sig_Priv'First = 0
          and then Attrs'Length <= Max_Attributes
          and then Now'Length <= Now_Len
          and then Doc_Type'Length <= Device_Auth.Max_Doc_Type
          and then B'First = 0
          and then B'Length = Max_Len (Hash_P, HI, Sig_P, SI),
        Proof_Only => Hash_Valid (Hash_P) and then Sig_Valid (Sig_P)),
     Post              =>
       (if St = Mdoc_Status.Ok then Len in Mdoc_Proof.Tags_Len + 2 .. B'Length
        else Len = 0)
       and then (St in Mdoc_Status.Hash_Failed | Mdoc_Status.Sig_Failed)
                = (Detail /= Prover_Status.Ok)
       and then St not in Mdoc_Status.Parse_Failed
                        | Mdoc_Status.Attribute_Not_Found
                        | Mdoc_Status.Attribute_Too_Long
                        | Mdoc_Status.Item_Order_Unsupported
                        | Mdoc_Status.Validity_Form_Unsupported
                        | Mdoc_Status.Device_Key_Form_Unsupported
                        | Mdoc_Status.Random_Form_Unsupported
                        | Mdoc_Status.Signature_Not_Canonical
                        | Mdoc_Status.Profile_Unknown
                        | Mdoc_Status.Profile_Mismatch
                        | Mdoc_Status.Attribute_Count;

   --  The proof from the credential (block 6, ADR 0086): Mdoc is the
   --  document as the holder presents it; it is parsed (Mdoc_Parse),
   --  the two witnesses are built from the parse and the pads Ap
   --  (Mdoc_Witness) into Hash_W and Sig_W, the caller's buffers of the
   --  layout's counts, and Prove runs on them with the same request.
   --  St is Parse_Failed when the parse refuses the document, with the
   --  parser's status in Parse_St and the CBOR reader's in Cbor_St;
   --  Attribute_Not_Found, Attribute_Too_Long, Item_Order_Unsupported,
   --  Validity_Form_Unsupported, Device_Key_Form_Unsupported,
   --  Random_Form_Unsupported and Signature_Not_Canonical are the
   --  builders' refusals; otherwise St,
   --  Len, B and Detail are Prove's. On a refusal before the proof (a
   --  session transcript above the bound, the parse, the builders) the
   --  three buffers are zero (postcondition): nothing of the credential
   --  stays in them. On a proof, or a refusal of the proof itself, the
   --  witnesses are in the caller's buffers, secret: the caller clears
   --  them.
   procedure Prove_Mdoc
     (Version    : Version_Number;
      Hash_P     : Hash_Circuit;
      HI         : Circuit_Info;
      Sig_P      : Sig_Circuit;
      SI         : Circuit_Info;
      Mdoc       : Byte_Array;
      Ap         : Mdoc_Mac.Pads;
      Pk_X, Pk_Y : P256_Field.Element;
      Session    : Byte_Array;
      Attrs      : Attribute_List;
      Now        : Byte_Array;
      Doc_Type   : Byte_Array;
      Hash_W     : out Hash_Elements;
      Sig_W      : out Sig_Elements;
      B          : out Byte_Array;
      Len        : out Natural;
      St         : out Mdoc_Status.Status;
      Detail     : out Prover_Status.Status;
      Parse_St   : out Mdoc_Parse.Status;
      Cbor_St    : out Cbor_Parse.Status)
   with
     Always_Terminates => False,
     Pre               =>
       (Runtime    =>
          Version in 6 .. 7
          and then Hash_Ok (Hash_P, HI.Cfg) and then Sig_Ok (Sig_P, SI.Cfg)
          and then Parts_Fit (Hash_P, HI, Sig_P, SI)
          and then Attrs'Length <= Max_Attributes
          and then Now'Length <= Now_Len
          and then Doc_Type'Length <= Device_Auth.Max_Doc_Type
          and then Hash_W'First = 0
          and then Hash_W'Length
                   = Mdoc_Witness.Hash_Count (Version, Attrs'Length)
          and then Sig_W'First = 0
          and then Sig_W'Length = Mdoc_Witness.Sig_Count
          and then B'First = 0
          and then B'Length = Max_Len (Hash_P, HI, Sig_P, SI),
        Proof_Only => Hash_Valid (Hash_P) and then Sig_Valid (Sig_P)),
     Post              =>
       (if St = Mdoc_Status.Ok then Len in Mdoc_Proof.Tags_Len + 2 .. B'Length
        else Len = 0)
       and then (St in Mdoc_Status.Hash_Failed | Mdoc_Status.Sig_Failed)
                = (Detail /= Prover_Status.Ok)
       and then (St = Mdoc_Status.Parse_Failed) = (Parse_St /= Mdoc_Parse.Ok)
       and then (if Session'Length > Device_Auth.Max_Session_Transcript
                 then St = Mdoc_Status.Transcript_Too_Long)
       and then (if Session'Length > Device_Auth.Max_Session_Transcript
                    or else St in Mdoc_Status.Parse_Failed
                                | Mdoc_Status.Attribute_Not_Found
                                | Mdoc_Status.Attribute_Too_Long
                                | Mdoc_Status.Item_Order_Unsupported
                                | Mdoc_Status.Validity_Form_Unsupported
                                | Mdoc_Status.Device_Key_Form_Unsupported
                                | Mdoc_Status.Random_Form_Unsupported
                                | Mdoc_Status.Signature_Not_Canonical
                 then (for all I in Hash_W'Range => Hash_W (I) = GF2_128.Zero)
                      and then
                      (for all I in Sig_W'Range =>
                         Sig_W (I) = P256_Field.Zero))
       and then St not in Mdoc_Status.Profile_Unknown
                        | Mdoc_Status.Profile_Mismatch
                        | Mdoc_Status.Attribute_Count;

   --  The prover's entry point of the supported profile (ADR 0089,
   --  #79): Profile is the profile's name, the combined identifier of a
   --  row of Mdoc_Spec; Hash_Id, Hash_Sfb, Sig_Id and Sig_Sfb the
   --  identifiers and subfield boundaries of the two circuits given
   --  (from their files' headers). The profile is checked first
   --  (Mdoc_Spec.Select_Profile: Profile_Unknown, Profile_Mismatch,
   --  Attribute_Count); then that the circuits fit the row's Ligero
   --  configurations and that the three buffers have the row's lengths
   --  (Profile_Mismatch otherwise); then Prove_Mdoc runs with the row's
   --  version and configurations. On every refusal, of the profile, of
   --  the request, of the witness or of the proof, the three buffers
   --  are zero. On success the two witnesses hold the credential's
   --  secrets: the caller wipes them once the proof is written. The claims of chapter 9 Section 6 are scoped
   --  to this entry point; Prove and Prove_Mdoc stay for reference work.
   procedure Prove_Profile
     (Profile    : Bytes_32;
      Hash_P     : Hash_Circuit;
      Hash_Id    : Bytes_32;
      Hash_Sfb   : Natural;
      Sig_P      : Sig_Circuit;
      Sig_Id     : Bytes_32;
      Sig_Sfb    : Natural;
      Mdoc       : Byte_Array;
      Ap         : Mdoc_Mac.Pads;
      Pk_X, Pk_Y : P256_Field.Element;
      Session    : Byte_Array;
      Attrs      : Attribute_List;
      Now        : Byte_Array;
      Doc_Type   : Byte_Array;
      Hash_W     : out Hash_Elements;
      Sig_W      : out Sig_Elements;
      B          : out Byte_Array;
      Len        : out Natural;
      St         : out Mdoc_Status.Status;
      Detail     : out Prover_Status.Status;
      Parse_St   : out Mdoc_Parse.Status;
      Cbor_St    : out Cbor_Parse.Status)
   with
     Always_Terminates => False,
     Pre               =>
       (Runtime    =>
          Attrs'Length <= Max_Attributes
          and then Now'Length <= Now_Len
          and then Doc_Type'Length <= Device_Auth.Max_Doc_Type,
        Proof_Only => Hash_Valid (Hash_P) and then Sig_Valid (Sig_P)),
     Post              =>
       (if St = Mdoc_Status.Ok then Len in Mdoc_Proof.Tags_Len + 2 .. B'Length
        else Len = 0)
       and then (St in Mdoc_Status.Hash_Failed | Mdoc_Status.Sig_Failed)
                = (Detail /= Prover_Status.Ok)
       and then (St = Mdoc_Status.Parse_Failed) = (Parse_St /= Mdoc_Parse.Ok)
       and then (if St /= Mdoc_Status.Ok
                 then (for all I in Hash_W'Range => Hash_W (I) = GF2_128.Zero)
                      and then
                      (for all I in Sig_W'Range =>
                         Sig_W (I) = P256_Field.Zero)
                      and then (for all I in B'Range => B (I) = 0));

end Mdoc_Prover;
