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
--  combined hash is the row's: the first step of what issue #79 asks
--  for, one identified profile selected and checked.
--
--  Documentation: docs/guide/09-mdoc.md.
--
--  Proof status. Silver; Lookup returns a row whose combined
--  identifier is the one asked for (Gold, trivially). That the rows
--  are upstream's is tested: the harness mdoc_kat checks each row
--  against tests/vectors/mdoc_layer.txt, written from zk_spec.rs by
--  gen_mdoc_layer_vectors.py, and checks Combined_Of on the two
--  identifiers of each row.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE. Public data.

pragma SPARK_Mode (On);

with Bytes;           use Bytes;
with Ligero_Geometry; use Ligero_Geometry;

package Mdoc_Spec is

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
               and then Valid (Spec'Result.Sig_Cfg);

   --  The row whose combined identifier is Combined, if any.
   procedure Lookup
     (Combined : Bytes_32; Found : out Boolean; I : out Spec_Index)
   with
     Global => null,
     Post   => (if Found then Spec (I).Combined = Combined);

   --  SHA-256 of the signature circuit's identifier followed by the
   --  hash circuit's: the name of the archive.
   function Combined_Of (Sig_Id, Hash_Id : Bytes_32) return Bytes_32 with
     Global => null;

end Mdoc_Spec;
