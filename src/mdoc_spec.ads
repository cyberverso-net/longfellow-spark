--  Mdoc_Spec: the table of the circuit pairs this project holds, as
--  upstream's table of specifications names them (longfellow-zk/
--  longfellow-zk d5e6be7, rust/applications/mdoc_zk/runtime/src/
--  zk_spec.rs, ZK_SPECS; Phase D, block 5, ADR 0058). A specification
--  is a circuit version, a number of attributes, the combined
--  identifier of the archive, which is SHA-256 of the signature
--  circuit's identifier followed by the hash circuit's (the archive is
--  named after it; test_circuit_ids_match_zkspecs of upstream checks
--  it), and the Ligero configuration of each circuit. Upstream lists
--  twelve prior specifications (versions 5, 6 and 7, one to four
--  attributes) and four current ones (version 8); chapter 9 reproduces
--  the table. This project holds the two archives of ADR 0055 and
--  0059, version 7 and version 6 with one attribute, whose LFC2
--  payloads are under tests/vectors/upstream/mdoc/ and in the pinned
--  list of the command line (ADR 0074): two rows.
--
--  The command-line tools select a row by the combined identifier the
--  caller gives, load the two circuits of the archive, and check that
--  the identifiers the loader returns are the row's and that their
--  combined hash is the row's. The two rows are the supported profile
--  of ADR 0089 (#79): Select_Profile is the check the library's two
--  entry points begin with, the profile's name, the circuits'
--  identifiers and the number of attributes, one for both rows.
--
--  Documentation: docs/guide/09-mdoc.md.
--
--  Proof status. Silver; Lookup returns a row whose combined
--  identifier is the one asked for, and Select_Profile, when it
--  accepts, a row whose identifiers and number of attributes are the
--  ones given (Gold, trivially); Spec states that both rows are of
--  version 6 or 7 and one attribute. That the rows
--  are upstream's is tested: the harness mdoc_kat checks each row
--  against tests/vectors/mdoc_layer.txt, written from zk_spec.rs by
--  gen_mdoc_layer_vectors.py, and checks Combined_Of on the two
--  identifiers of each row.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE. Public data.

pragma SPARK_Mode (On);

with Bytes;           use Bytes;
with Ligero_Geometry; use Ligero_Geometry;
with Mdoc_Status;

package Mdoc_Spec is

   use type Mdoc_Status.Status;

   --  The circuit versions with the legacy layout of the public inputs
   --  and the tags (Mdoc_Inputs, Mdoc_Mac). Version 8 has another
   --  layout and no archive at d5e6be7.
   subtype Version_Number is Positive range 5 .. 7;

   type Specification is record
      Version        : Version_Number;
      Num_Attributes : Positive;
      Combined       : Bytes_32;
      Hash_Id        : Bytes_32;
      Sig_Id         : Bytes_32;
      Hash_Cfg       : Config;
      Sig_Cfg        : Config;
   end record;

   type Spec_Index is range 1 .. 2;

   function Spec (I : Spec_Index) return Specification with
     Global => null,
     Post   => Valid (Spec'Result.Hash_Cfg)
               and then Valid (Spec'Result.Sig_Cfg)
               and then Spec'Result.Version in 6 .. 7
               and then Spec'Result.Num_Attributes = 1;

   --  The row whose combined identifier is Combined, if any.
   procedure Lookup
     (Combined : Bytes_32; Found : out Boolean; I : out Spec_Index)
   with
     Global => null,
     Post   => (if Found then Spec (I).Combined = Combined);

   --  The supported profile (ADR 0089): the row named Combined, if the
   --  two circuits are the row's (their identifiers) and the request
   --  holds the row's number of attributes. St is Ok, Profile_Unknown,
   --  Profile_Mismatch or Attribute_Count, checked in that order; the
   --  two entry points (Mdoc_Prover.Prove_Profile,
   --  Mdoc_Verifier.Verify_Profile) begin with it.
   procedure Select_Profile
     (Combined         : Bytes_32;
      Hash_Id, Sig_Id  : Bytes_32;
      Nattrs           : Natural;
      I                : out Spec_Index;
      St               : out Mdoc_Status.Status)
   with
     Global => null,
     Post   => St in Mdoc_Status.Ok | Mdoc_Status.Profile_Unknown
                    | Mdoc_Status.Profile_Mismatch
                    | Mdoc_Status.Attribute_Count
               and then
               (if St = Mdoc_Status.Ok then
                  Spec (I).Combined = Combined
                  and then Spec (I).Hash_Id = Hash_Id
                  and then Spec (I).Sig_Id = Sig_Id
                  and then Spec (I).Num_Attributes = Nattrs);

   --  SHA-256 of the signature circuit's identifier followed by the
   --  hash circuit's: the name of the archive.
   function Combined_Of (Sig_Id, Hash_Id : Bytes_32) return Bytes_32 with
     Global => null;

end Mdoc_Spec;
