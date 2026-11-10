--  Mdoc_Cli: what the two mDoc command-line programs share (Phase D,
--  block 5, ADR 0058): the command line of a request (the
--  specification, the issuer's key, the session transcript, the date,
--  the document type, the attributes), the files, the hex, and the
--  loading of the two circuits of a specification with the checks the
--  library asks of them. Outside the proof perimeter (SPARK_Mode Off):
--  file input and output, the command line; every computation is in
--  the library.
--
--  The circuits: --spec names an archive by its combined identifier
--  (Mdoc_Spec); the two LFC2 payloads are read from --circuits DIR
--  (default tests/vectors/upstream/mdoc/) as <id>_hash.lfc2 and
--  <id>_sig.lfc2, loaded in their packed form through Pinned_Circuits
--  (ADR 0074; --check-circuit-id recomputes the identifiers), and
--  their identifiers must be the row's and combine to the row's
--  identifier (Mdoc_Spec.Combined_Of): the status combined_hash
--  otherwise.
--
--  The prover's input: --mdoc FILE the credential as the holder
--  presents it (the library parses it and builds both witnesses,
--  Mdoc_Prover.Prove_Mdoc), or --hash-witness and --sig-witness
--  upstream's two witness files; one form or the other.
--
--  The request: --pkx and --pky the issuer's key as hex integers (an
--  optional 0x, up to 64 digits), --transcript the session transcript
--  as hex or --transcript-file its bytes, --now the date, --doc-type
--  the document type, --attr ID:CBORHEX one requested attribute (the
--  identifier as text, its value as the CBOR bytes), repeatable. The
--  session transcript is bounded at Device_Auth.Max_Session_Transcript
--  bytes, which is also a status of the library (transcript_too_long).
--
--  Exit statuses, as the other programs: 0 done, 1 a status of the
--  library or of these checks (printed on standard output in lower
--  case), 2 a usage or file error (the message on standard error).

pragma SPARK_Mode (Off);

with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with P256_Field;
with Circuit_Reader_GF2_128;
with Circuit_Reader_P256;
with Mdoc_Spec;
with Mdoc_Inputs;

package Mdoc_Cli is

   --  Exit status 2, the message on standard error.
   Usage_Error : exception;

   --  Exit status 1, the message on standard output.
   Refused : exception;

   type String_Access is access String;
   type Byte_Array_Access is access Byte_Array;

   procedure Free (B : in out Byte_Array_Access);

   --  The largest file a program reads: a circuit, a witness, a proof
   --  or a session transcript. The proofs are below 400 kB and the
   --  witnesses below 3 MB; a circuit payload is below 2 MB. A larger
   --  file is a usage error before anything is allocated.
   Max_File_Bytes : constant := 16 * 1024 * 1024;

   function Read_File (Path : String) return Byte_Array_Access;
   procedure Write_File (Path : String; B : Byte_Array);

   function Hex_Bytes (S : String) return Byte_Array;
   function Hex_Of (B : Byte_Array) return String;
   function To_Bytes (S : String) return Byte_Array;
   function Lower (S : String) return String;

   --  A coordinate of the issuer's key: hex, an optional 0x, at most
   --  64 digits, below p.
   function Coordinate (S : String) return P256_Field.Element;

   type Request is record
      Spec         : Mdoc_Spec.Spec_Index := Mdoc_Spec.Spec_Index'First;
      Dir          : String_Access;
      Full_Id      : Boolean := False;
      Pk_X, Pk_Y   : P256_Field.Element := P256_Field.Zero;
      Session      : Byte_Array_Access;
      Now          : Byte_Array_Access;
      Doc_Type     : Byte_Array_Access;
      Attrs        : Mdoc_Inputs.Attribute_List
                       (1 .. Mdoc_Inputs.Max_Attributes);
      Nattrs       : Natural := 0;
      --  The prover's: the credential, or the two witness files.
      Mdoc_Path    : String_Access;
      Hash_Witness : String_Access;
      Sig_Witness  : String_Access;
      Out_Path     : String_Access;
      Seeded       : Boolean := False;
      Seed         : Unsigned_64 := 0;
      --  The verifier's.
      Proof_Path   : String_Access;
   end record;

   --  The command line into R; Prover says which program's. --help
   --  prints the usage and raises Usage_Error with an empty message.
   procedure Parse_Arguments (R : out Request; Prover : Boolean);

   --  The two circuits of the specification, loaded and checked as the
   --  header says; Refused on a status.
   procedure Load_Circuits
     (R      : Request;
      Hash_C : out Circuit_Reader_GF2_128.Packed_Access;
      Hash_H : out Circuit_Reader_GF2_128.Header;
      Sig_C  : out Circuit_Reader_P256.Packed_Access;
      Sig_H  : out Circuit_Reader_P256.Header);

end Mdoc_Cli;
