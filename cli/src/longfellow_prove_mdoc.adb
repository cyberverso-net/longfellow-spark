--  longfellow_prove_mdoc: the command-line prover of an mDoc proof of
--  age, from the credential or from upstream's witness files (Phase D,
--  blocks 5 and 6, ADR 0058, ADR 0086). Outside the proof perimeter
--  (SPARK_Mode Off): it parses the command line (Mdoc_Cli), loads the
--  two circuits of the specification, draws the pads mac_ap from the
--  randomness source, and hands everything to the SPARK library.
--
--  With --mdoc FILE the file is the credential as the holder presents
--  it; the library parses it and builds both witnesses
--  (Mdoc_Prover.Prove_Mdoc) in two buffers this program allocates on
--  the heap (1.3 MB for the hash circuit) and clears afterwards: the
--  witnesses are secret. The parse and the witness builders are the
--  library's; what this program checks is what their preconditions
--  ask: the specification's version is 6 or 7. At version 6 an item
--  whose elementValue entry does not follow its elementIdentifier entry
--  is refused by the builder (item_order_unsupported) before any
--  commitment, where upstream's builder would let the circuit refuse
--  the proof.
--
--  With --hash-witness and --sig-witness the two files are read (the
--  circuit's inputs as little-endian field elements, 16 bytes each
--  for the hash circuit and 32 for the signature circuit, public ones
--  first, ADR 0059), their private parts taken, mac_ap and the three
--  messages the tags bind read from the ends of the hash witness
--  (Mdoc_Inputs.Witness_Parts), and the fresh pads placed in both
--  witnesses (Mdoc_Inputs.Place_Pads: the pads are one-time, and a
--  proof under the file's pads beside upstream's own would give the
--  bound values away), then Mdoc_Prover.Prove. The public parts of
--  the files are not used: they hold the tags and av of upstream's
--  own run, and a new proof draws its own.
--
--  Randomness: the operating system's generator unless --seed N is
--  given, which selects Simple_Rng and makes the proof reproducible,
--  and predictable: a test option, never the default (ADR 0050).
--
--  Exit status: 0 when the proof is written; 1 on a status (printed in
--  lower case: the layer's, with the prover's beside it when one
--  prover failed, or the parser's and the CBOR reader's beside
--  parse_failed; or spec_unknown, combined_hash, config_invalid,
--  version_unsupported, witness_layout, transcript_too_long); 2 on a
--  usage or file error.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Exceptions;
with Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Bytes;            use Bytes;
with GF2_128;
with P256_Field;
with Prover_Status;
with Mdoc_Status;
with Mdoc_Spec;
with Mdoc_Mac;
with Mdoc_Inputs;
with Mdoc_Parse;
with Cbor_Parse;
with Mdoc_Witness;
with Circuit_Reader_GF2_128;
with Circuit_Reader_P256;
with Cli_Random;
with Mdoc_Cli;         use Mdoc_Cli;
with Mdoc_Prover_Cli;

procedure Longfellow_Prove_Mdoc is

   package TIO renames Ada.Text_IO;
   package CL renames Ada.Command_Line;
   package MP renames Mdoc_Prover_Cli;

   use type Mdoc_Status.Status;
   use type Prover_Status.Status;
   use type Cbor_Parse.Status;

   type Hash_Inputs_Access is access MP.Hash_Elements;
   type Sig_Inputs_Access is access MP.Sig_Elements;
   procedure Free is
     new Ada.Unchecked_Deallocation (MP.Hash_Elements, Hash_Inputs_Access);
   procedure Free is
     new Ada.Unchecked_Deallocation (MP.Sig_Elements, Sig_Inputs_Access);

   R      : Request;
   Hash_C : Circuit_Reader_GF2_128.Packed_Access;
   Hash_H : Circuit_Reader_GF2_128.Header;
   Sig_C  : Circuit_Reader_P256.Packed_Access;
   Sig_H  : Circuit_Reader_P256.Header;

   --  The private inputs of a witness file: the elements after the
   --  first Npublic, each of Size bytes.
   function Hash_Private (Path : String; Ninput, Npublic : Natural)
                          return Hash_Inputs_Access
   is
      B  : Byte_Array_Access := Read_File (Path);
      P  : Hash_Inputs_Access;
      Ok : Boolean;
   begin
      if B'Length /= 16 * Ninput then
         raise Usage_Error with "hash witness: expected" & Ninput'Image
           & " elements of 16 bytes";
      end if;
      P := new MP.Hash_Elements (0 .. Ninput - Npublic - 1);
      for I in P'Range loop
         GF2_128.From_Bytes
           (B (16 * (Npublic + I) .. 16 * (Npublic + I) + 15), P (I), Ok);
      end loop;
      Free (B);
      return P;
   end Hash_Private;

   function Sig_Private (Path : String; Ninput, Npublic : Natural)
                         return Sig_Inputs_Access
   is
      B  : Byte_Array_Access := Read_File (Path);
      P  : Sig_Inputs_Access;
      Ok : Boolean;
   begin
      if B'Length /= 32 * Ninput then
         raise Usage_Error with "sig witness: expected" & Ninput'Image
           & " elements of 32 bytes";
      end if;
      P := new MP.Sig_Elements (0 .. Ninput - Npublic - 1);
      for I in P'Range loop
         P256_Field.From_Bytes
           (B (32 * (Npublic + I) .. 32 * (Npublic + I) + 31), P (I), Ok);
         if not Ok then
            raise Usage_Error with "sig witness: element" & I'Image
              & " is not below p";
         end if;
      end loop;
      Free (B);
      return P;
   end Sig_Private;

begin
   Parse_Arguments (R, Prover => True);
   Load_Circuits (R, Hash_C, Hash_H, Sig_C, Sig_H);
   declare
      S  : constant Mdoc_Spec.Specification := Mdoc_Spec.Spec (R.Spec);
      HI : constant MP.Circuit_Info :=
        (Id => Hash_H.Id, Sfb => Hash_H.Subfield_Boundary, Cfg => S.Hash_Cfg);
      SI : constant MP.Circuit_Info :=
        (Id => Sig_H.Id, Sfb => Sig_H.Subfield_Boundary, Cfg => S.Sig_Cfg);
   begin
      --  The rest of the executable precondition: the configurations
      --  fit the circuits and the proofs fit the bound.
      if not (MP.Hash_Ok (Hash_C.all, HI.Cfg)
              and then MP.Sig_Ok (Sig_C.all, SI.Cfg)
              and then MP.Parts_Fit (Hash_C.all, HI, Sig_C.all, SI))
      then
         raise Refused with "config_invalid";
      end if;
      if R.Mdoc_Path /= null and then S.Version not in 6 .. 7 then
         raise Refused with "version_unsupported";
      end if;
      declare
         Ap       : Mdoc_Mac.Pads;
         M        : Mdoc_Mac.Messages;
         Ok       : Boolean;
         Max      : constant Positive :=
           MP.Max_Len (Hash_C.all, HI, Sig_C.all, SI);
         Out_B    : Byte_Array_Access := new Byte_Array (0 .. Max - 1);
         Len      : Natural;
         St       : Mdoc_Status.Status;
         Detail   : Prover_Status.Status;
         Parse_St : Mdoc_Parse.Status := Mdoc_Parse.Ok;
         Cbor_St  : Cbor_Parse.Status := Cbor_Parse.Ok;
         Priv_H   : Hash_Inputs_Access;
         Priv_S   : Sig_Inputs_Access;
      begin
         if R.Mdoc_Path = null then
            Priv_H := Hash_Private (R.Hash_Witness.all,
                                    Hash_C.Ninput, Hash_C.Npublic);
            Priv_S := Sig_Private (R.Sig_Witness.all,
                                   Sig_C.Ninput, Sig_C.Npublic);
            Mdoc_Inputs.Witness_Parts (Priv_H.all, Ap, M, Ok);
            if not Ok
              or else Priv_S'Length < Mdoc_Inputs.Sig_Tail_Elements
              or else not Mdoc_Inputs.Sig_Pads_Match (Priv_S.all, Ap)
            then
               raise Refused with "witness_layout";
            end if;
         end if;
         if R.Seeded then
            Cli_Random.Set_Seed (R.Seed);
         end if;
         --  Fresh one-time pads.
         declare
            Fresh : Bytes_16;
         begin
            for I in Mdoc_Mac.Message_Index loop
               for H in Mdoc_Mac.Half_Index loop
                  Cli_Random.Fill (Fresh);
                  GF2_128.From_Bytes (Fresh, Ap (I) (H), Ok);
               end loop;
            end loop;
         end;
         if R.Mdoc_Path /= null then
            --  From the credential: the witnesses are built into these
            --  two buffers, of the layout's counts.
            declare
               Mdoc : Byte_Array_Access := Read_File (R.Mdoc_Path.all);
            begin
               Priv_H := new MP.Hash_Elements
                 (0 .. Mdoc_Witness.Hash_Count (S.Version, R.Nattrs) - 1);
               Priv_S := new MP.Sig_Elements (0 .. Mdoc_Witness.Sig_Count - 1);
               MP.Prove_Mdoc (S.Version, Hash_C.all, HI, Sig_C.all, SI,
                              Mdoc.all, Ap, R.Pk_X, R.Pk_Y,
                              R.Session.all, R.Attrs (1 .. R.Nattrs),
                              R.Now.all, R.Doc_Type.all,
                              Priv_H.all, Priv_S.all, Out_B.all, Len,
                              St, Detail, Parse_St, Cbor_St);
               Free (Mdoc);
            end;
         else
            --  From the files: the fresh pads in place of the file's,
            --  in both witnesses.
            Mdoc_Inputs.Place_Pads (Priv_H.all, Priv_S.all, Ap);
            MP.Prove (S.Version, Hash_C.all, HI, Sig_C.all, SI,
                      Priv_H.all, Priv_S.all, Ap, M, R.Pk_X, R.Pk_Y,
                      R.Session.all, R.Attrs (1 .. R.Nattrs), R.Now.all,
                      R.Doc_Type.all, Out_B.all, Len, St, Detail);
         end if;
         --  The witnesses are secret: cleared before they are freed.
         Priv_H.all := [others => GF2_128.Zero];
         Priv_S.all := [others => P256_Field.Zero];
         Free (Priv_H);
         Free (Priv_S);
         Circuit_Reader_GF2_128.Free_Packed (Hash_C);
         Circuit_Reader_P256.Free_Packed (Sig_C);
         if St /= Mdoc_Status.Ok then
            TIO.Put_Line
              (Lower (St'Image)
               & (if Detail /= Prover_Status.Ok then " " & Lower (Detail'Image)
                  else "")
               & (if St = Mdoc_Status.Parse_Failed
                  then " " & Lower (Parse_St'Image)
                       & (if Cbor_St /= Cbor_Parse.Ok
                          then " " & Lower (Cbor_St'Image) else "")
                  else ""));
            CL.Set_Exit_Status (1);
            return;
         end if;
         Write_File (R.Out_Path.all, Out_B (0 .. Len - 1));
         Free (Out_B);
         TIO.Put_Line ("ok:" & Len'Image & " bytes written to "
                       & R.Out_Path.all);
         CL.Set_Exit_Status (0);
      end;
   end;
exception
   when E : Refused =>
      TIO.Put_Line (Ada.Exceptions.Exception_Message (E));
      CL.Set_Exit_Status (1);
   when E : Usage_Error =>
      if Ada.Exceptions.Exception_Message (E) /= "" then
         TIO.Put_Line (TIO.Standard_Error,
                       "longfellow_prove_mdoc: "
                       & Ada.Exceptions.Exception_Message (E));
         CL.Set_Exit_Status (2);
      end if;
   when E : Program_Error =>
      TIO.Put_Line (TIO.Standard_Error,
                    "longfellow_prove_mdoc: "
                    & Ada.Exceptions.Exception_Message (E));
      CL.Set_Exit_Status (2);
end Longfellow_Prove_Mdoc;
