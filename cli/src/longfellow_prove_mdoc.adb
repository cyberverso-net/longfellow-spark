--  longfellow_prove_mdoc: the command-line prover of an mDoc proof of
--  age from upstream's witness files (Phase D, block 5, ADR 0058).
--  Outside the proof perimeter (SPARK_Mode Off): it parses the command
--  line (Mdoc_Cli), loads the two circuits of the specification, reads
--  the two witness files (the circuit's inputs as little-endian field
--  elements, 16 bytes each for the hash circuit and 32 for the
--  signature circuit, public ones first, ADR 0059), takes their
--  private parts, reads mac_ap and the three messages the tags bind
--  from the ends of the hash witness (Mdoc_Inputs.Witness_Parts), and
--  draws fresh pads mac_ap from the randomness source and places them
--  in both witnesses (Mdoc_Inputs.Place_Pads: the pads are one-time, and
--  a proof under the file's pads beside upstream's own would give the
--  bound values away), and hands everything to Mdoc_Prover.Prove, which
--  is the SPARK library. The public parts of the files are not used:
--  they hold the tags and av of upstream's own run, and a new proof
--  draws its own.
--
--  Randomness: the operating system's generator unless --seed N is
--  given, which selects Simple_Rng and makes the proof reproducible,
--  and predictable: a test option, never the default (ADR 0050).
--
--  Exit status: 0 when the proof is written; 1 on a status (printed in
--  lower case: the layer's, with the prover's beside it when one
--  prover failed, or spec_unknown, combined_hash, config_invalid,
--  witness_layout, transcript_too_long); 2 on a usage or file error.

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
      declare
         Priv_H : Hash_Inputs_Access :=
           Hash_Private (R.Hash_Witness.all, Hash_C.Ninput, Hash_C.Npublic);
         Priv_S : Sig_Inputs_Access :=
           Sig_Private (R.Sig_Witness.all, Sig_C.Ninput, Sig_C.Npublic);
         Ap     : Mdoc_Mac.Pads;
         M      : Mdoc_Mac.Messages;
         Ok     : Boolean;
         Max    : constant Positive :=
           MP.Max_Len (Hash_C.all, HI, Sig_C.all, SI);
         Out_B  : Byte_Array_Access := new Byte_Array (0 .. Max - 1);
         Len    : Natural;
         St     : Mdoc_Status.Status;
         Detail : Prover_Status.Status;
      begin
         Mdoc_Inputs.Witness_Parts (Priv_H.all, Ap, M, Ok);
         if not Ok
           or else Priv_S'Length < Mdoc_Inputs.Sig_Tail_Elements
           or else not Mdoc_Inputs.Sig_Pads_Match (Priv_S.all, Ap)
         then
            raise Refused with "witness_layout";
         end if;
         if R.Seeded then
            Cli_Random.Set_Seed (R.Seed);
         end if;
         --  Fresh one-time pads, in place of the file's, in both
         --  witnesses.
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
         Mdoc_Inputs.Place_Pads (Priv_H.all, Priv_S.all, Ap);
         MP.Prove (S.Version, Hash_C.all, HI, Sig_C.all, SI,
                   Priv_H.all, Priv_S.all, Ap, M, R.Pk_X, R.Pk_Y,
                   R.Session.all, R.Attrs (1 .. R.Nattrs), R.Now.all,
                   R.Doc_Type.all, Out_B.all, Len, St, Detail);
         Free (Priv_H);
         Free (Priv_S);
         Circuit_Reader_GF2_128.Free_Packed (Hash_C);
         Circuit_Reader_P256.Free_Packed (Sig_C);
         if St /= Mdoc_Status.Ok then
            TIO.Put_Line
              (Lower (St'Image)
               & (if Detail /= Prover_Status.Ok then " " & Lower (Detail'Image)
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
