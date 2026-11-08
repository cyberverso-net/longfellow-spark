--  Mdoc_Verifier: the verifier of an mDoc proof of age,
--  run_mdoc_verifier_inner of the reference (longfellow-zk/longfellow-zk
--  d5e6be7, rust/applications/mdoc_zk/runtime/src/verifier.rs; Phase D,
--  block 5, ADR 0058), on the two phases of Zk_Verifier (ADR 0085) over
--  the library instances of the two fields.
--
--  The flow, in the reference's order: the tags are read from the
--  front of the proof (Mdoc_Proof); the session transcript opens the
--  transcript; the hash proof is read at offset 96 and its root
--  written (Zk_Verifier.Receive), then the signature proof after it,
--  which must end where the buffer ends; av is drawn, 16 bytes; the
--  public inputs of the hash circuit are built from the attributes,
--  the date, the tags and av, and the hash proof is verified
--  (Verify_Received); e2 is computed from the session transcript and
--  the document type (Device_Auth), the public inputs of the signature
--  circuit are built from the issuer's key, e2, the tags and av, and
--  the signature proof is verified. A relying party that accepts has
--  checked both circuits on the same tags and the same av, hence on
--  the same credential.
--
--  What the verifier does not check, and the relying party does: that
--  the issuer's key is a trusted issuer's; the freshness of the nonce
--  inside the session transcript; the date it gives as now; what the
--  circuits compute (the trusted base register, R2).
--
--  Documentation: docs/guide/09-mdoc.md.
--
--  Proof status. Silver with the ownership checks on the two proofs
--  received; the statuses as stated. Soundness is the protocol's
--  theorem; that the verdict is upstream's is tested on upstream's
--  example proofs of both archives, which this verifier accepts, and
--  on the altered copies, which it refuses (the cli step).
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0037.
--  Public data only.

pragma SPARK_Mode (On);

with Bytes;            use Bytes;
with Ligero_Geometry;  use Ligero_Geometry;
with Transcript;
with Verifier_Status;
with Mdoc_Status;
with Mdoc_Inputs;      use Mdoc_Inputs;
with Device_Auth;
with P256_Field;
with Packed_Circuits_GF2_128;
with Packed_Circuits_P256;
with Zk_Verifier_GF2_128;
with Zk_Verifier_P256;
with Proof_Levels;

package Mdoc_Verifier is

   pragma Suppress (Predicate_Check);

   use type Mdoc_Status.Status;
   use type Verifier_Status.Status;

   package ZVH renames Zk_Verifier_GF2_128;
   package ZVS renames Zk_Verifier_P256;
   package PCH renames Packed_Circuits_GF2_128;
   package PCS renames Packed_Circuits_P256;

   subtype Hash_Circuit is ZVH.Packed_Circuit;
   subtype Sig_Circuit is ZVS.Packed_Circuit;

   --  The identifier (from the circuit file's header) and the Ligero
   --  configuration (from the specification) of one circuit.
   type Circuit_Info is record
      Id  : Bytes_32;
      Cfg : Config;
   end record;

   --  The loader's postcondition, what the verifier asks of a circuit
   --  at level Proof_Only (as Zk_Verifier.Verify).
   function Hash_Valid (P : Hash_Circuit) return Boolean is
     (PCH.Valid (P) and then SAH.Well_Formed (PCH.Expand (P)))
   with Ghost => Proof_Only, Global => null;

   function Sig_Valid (P : Sig_Circuit) return Boolean is
     (PCS.Valid (P) and then SAP.Well_Formed (PCS.Expand (P)))
   with Ghost => Proof_Only, Global => null;

   --  B is the mDoc proof; the other parameters as Mdoc_Prover.Prove.
   --  Ok when both proofs are accepted; otherwise the status, with
   --  Detail the status of the failing verifier when St says one
   --  failed (Proof_Encoding there also for fewer than 96 bytes, under
   --  Hash_Failed, and for bytes after the signature proof, under
   --  Sig_Failed).
   procedure Verify
     (Version    : Version_Number;
      Hash_P     : Hash_Circuit;
      HI         : Circuit_Info;
      Sig_P      : Sig_Circuit;
      SI         : Circuit_Info;
      Pk_X, Pk_Y : P256_Field.Element;
      Session    : Byte_Array;
      Attrs      : Attribute_List;
      Now        : Byte_Array;
      Doc_Type   : Byte_Array;
      B          : Byte_Array;
      St         : out Mdoc_Status.Status;
      Detail     : out Verifier_Status.Status)
   with
     Global            => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Always_Terminates => False,
     Pre               =>
       (Runtime    =>
          Valid (HI.Cfg) and then Valid (SI.Cfg)
          and then Attrs'Length <= Max_Attributes
          and then Now'Length <= Now_Len
          and then Doc_Type'Length <= Device_Auth.Max_Doc_Type
          and then B'First = 0,
        Proof_Only => Hash_Valid (Hash_P) and then Sig_Valid (Sig_P)),
     Post              =>
       (St in Mdoc_Status.Hash_Failed | Mdoc_Status.Sig_Failed)
       = (Detail /= Verifier_Status.Ok);

end Mdoc_Verifier;
