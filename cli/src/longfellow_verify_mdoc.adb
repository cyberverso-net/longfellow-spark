--  longfellow_verify_mdoc: the command-line verifier of an mDoc proof of
--  age (Phase D, block 5, ADR 0058). Outside the proof perimeter
--  (SPARK_Mode Off): it parses the command line (Mdoc_Cli), loads the
--  two circuits of the specification, reads the proof file and hands
--  everything to Mdoc_Verifier.Verify, which is the SPARK library. The
--  relying party's data is the request: the issuer's key, the session
--  transcript, the date, the document type and the attributes with
--  the values it asks for.
--
--  Exit status: 0 when the proof is accepted (ok); 1 when it is
--  refused (the layer's status, with the verifier's beside it when one
--  verifier failed) or the circuits are not accepted (spec_unknown,
--  combined_hash, the loader's statuses, transcript_too_long); 2 on a
--  usage or file error.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Exceptions;
with Ada.Text_IO;
with Ligero_Geometry;
with Verifier_Status;
with Mdoc_Status;
with Mdoc_Spec;
with Circuit_Reader_GF2_128;
with Circuit_Reader_P256;
with Mdoc_Cli;         use Mdoc_Cli;
with Mdoc_Verifier;

procedure Longfellow_Verify_Mdoc is

   package TIO renames Ada.Text_IO;
   package CL renames Ada.Command_Line;

   use type Mdoc_Status.Status;
   use type Verifier_Status.Status;

   R      : Request;
   Hash_C : Circuit_Reader_GF2_128.Packed_Access;
   Hash_H : Circuit_Reader_GF2_128.Header;
   Sig_C  : Circuit_Reader_P256.Packed_Access;
   Sig_H  : Circuit_Reader_P256.Header;

begin
   Parse_Arguments (R, Prover => False);
   Load_Circuits (R, Hash_C, Hash_H, Sig_C, Sig_H);
   declare
      S      : constant Mdoc_Spec.Specification := Mdoc_Spec.Spec (R.Spec);
      HI     : constant Mdoc_Verifier.Circuit_Info :=
        (Id => Hash_H.Id, Cfg => S.Hash_Cfg);
      SI     : constant Mdoc_Verifier.Circuit_Info :=
        (Id => Sig_H.Id, Cfg => S.Sig_Cfg);
      P      : Byte_Array_Access := Read_File (R.Proof_Path.all);
      St     : Mdoc_Status.Status;
      Detail : Verifier_Status.Status;
   begin
      if not (Ligero_Geometry.Valid (HI.Cfg)
              and then Ligero_Geometry.Valid (SI.Cfg))
      then
         raise Refused with "config_invalid";
      end if;
      --  The entry point of the supported profile (ADR 0089): it checks
      --  the profile again and refuses anything that is not one of its
      --  rows, two to four attributes included.
      Mdoc_Verifier.Verify_Profile
        (S.Combined, Hash_C.all, HI.Id, Sig_C.all, SI.Id,
         R.Pk_X, R.Pk_Y, R.Session.all, R.Attrs (1 .. R.Nattrs),
         R.Now.all, R.Doc_Type.all, P.all, St, Detail);
      Free (P);
      Circuit_Reader_GF2_128.Free_Packed (Hash_C);
      Circuit_Reader_P256.Free_Packed (Sig_C);
      TIO.Put_Line
        (Lower (St'Image)
         & (if Detail /= Verifier_Status.Ok then " " & Lower (Detail'Image)
            else ""));
      CL.Set_Exit_Status (if St = Mdoc_Status.Ok then 0 else 1);
   end;
exception
   when E : Refused =>
      TIO.Put_Line (Ada.Exceptions.Exception_Message (E));
      CL.Set_Exit_Status (1);
   when E : Usage_Error =>
      if Ada.Exceptions.Exception_Message (E) /= "" then
         TIO.Put_Line (TIO.Standard_Error,
                       "longfellow_verify_mdoc: "
                       & Ada.Exceptions.Exception_Message (E));
         CL.Set_Exit_Status (2);
      end if;
   when E : Program_Error =>
      TIO.Put_Line (TIO.Standard_Error,
                    "longfellow_verify_mdoc: "
                    & Ada.Exceptions.Exception_Message (E));
      CL.Set_Exit_Status (2);
end Longfellow_Verify_Mdoc;
