pragma SPARK_Mode (On);

with GF2_128;
with Mdoc_Mac;
with Mdoc_Proof;

package body Mdoc_Verifier is

   procedure Digest_Element
     (D : Bytes_32; E : out P256_Field.Element; Ok : out Boolean)
   with Global => null;

   procedure Digest_Element
     (D : Bytes_32; E : out P256_Field.Element; Ok : out Boolean)
   is
      LE : Bytes_32;
   begin
      for I in LE'Range loop
         LE (I) := D (31 - I);
      end loop;
      P256_Field.From_Bytes (LE, E, Ok);
   end Digest_Element;

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
   is
      RH   : ZVH.Received;
      RS   : ZVS.Received;
      VSt  : Verifier_Status.Status;
      Av16 : Bytes_16;
      Av   : GF2_128.Element;
      Ok   : Boolean;
      E2   : P256_Field.Element;
   begin
      Detail := Verifier_Status.Ok;
      if Session'Length > Device_Auth.Max_Session_Transcript then
         St := Mdoc_Status.Transcript_Too_Long;
         return;
      end if;
      if not All_Fit (Version, Attrs) then
         St := Mdoc_Status.Attribute_Invalid;
         return;
      end if;
      if Hash_Count (Version, Attrs'Length) /= Hash_P.Npublic
        or else Sig_Count /= Sig_P.Npublic
      then
         St := Mdoc_Status.Input_Count;
         return;
      end if;
      if B'Length < Mdoc_Proof.Tags_Len then
         St     := Mdoc_Status.Hash_Failed;
         Detail := Verifier_Status.Proof_Encoding;
         return;
      end if;
      declare
         T : constant Mdoc_Mac.Tags := Mdoc_Proof.Read_Tags (B);
      begin
         --  The transcript, the two commitments received.
         Transcript.Reset (Session);
         ZVH.Receive (B, Mdoc_Proof.Hash_First, HI.Cfg, Hash_P, RH, VSt);
         if VSt /= Verifier_Status.Ok then
            St     := Mdoc_Status.Hash_Failed;
            Detail := VSt;
            return;
         end if;
         ZVS.Receive (B, ZVH.After (RH), SI.Cfg, Sig_P, RS, VSt);
         if VSt /= Verifier_Status.Ok then
            ZVH.Release (RH);
            St     := Mdoc_Status.Sig_Failed;
            Detail := VSt;
            return;
         end if;
         if ZVS.After (RS) /= B'Length then
            ZVH.Release (RH);
            ZVS.Release (RS);
            St     := Mdoc_Status.Sig_Failed;
            Detail := Verifier_Status.Proof_Encoding;
            return;
         end if;
         --  av, then the hash circuit.
         Transcript.Get_Random_Bytes (Av16);
         GF2_128.From_Bytes (Av16, Av, Ok);
         declare
            PubH : SAH.Element_Array
              (0 .. Hash_Count (Version, Attrs'Length) - 1);
            PubS : SAP.Element_Array (0 .. Sig_Count - 1);
         begin
            Hash_Inputs (Version, Attrs, Now, T, Av, PubH);
            ZVH.Verify_Received (HI.Id, HI.Cfg, Hash_P, PubH, RH, VSt);
            if VSt /= Verifier_Status.Ok then
               ZVS.Release (RS);
               St     := Mdoc_Status.Hash_Failed;
               Detail := VSt;
               return;
            end if;
            --  e2, then the signature circuit.
            Digest_Element (Device_Auth.Digest (Session, Doc_Type), E2, Ok);
            if not Ok then
               ZVS.Release (RS);
               St := Mdoc_Status.E2_Not_In_Field;
               return;
            end if;
            Sig_Inputs (Pk_X, Pk_Y, E2, T, Av, PubS);
            ZVS.Verify_Received (SI.Id, SI.Cfg, Sig_P, PubS, RS, VSt);
            if VSt /= Verifier_Status.Ok then
               St     := Mdoc_Status.Sig_Failed;
               Detail := VSt;
               return;
            end if;
            St := Mdoc_Status.Ok;
         end;
      end;
   end Verify;

   procedure Verify_Profile
     (Profile    : Bytes_32;
      Hash_P     : Hash_Circuit;
      Hash_Id    : Bytes_32;
      Sig_P      : Sig_Circuit;
      Sig_Id     : Bytes_32;
      Pk_X, Pk_Y : P256_Field.Element;
      Session    : Byte_Array;
      Attrs      : Attribute_List;
      Now        : Byte_Array;
      Doc_Type   : Byte_Array;
      B          : Byte_Array;
      St         : out Mdoc_Status.Status;
      Detail     : out Verifier_Status.Status)
   is
      I : Mdoc_Spec.Spec_Index;
   begin
      Detail := Verifier_Status.Ok;
      Mdoc_Spec.Select_Profile
        (Profile, Hash_Id, Sig_Id, Attrs'Length, I, St);
      if St /= Mdoc_Status.Ok then
         return;
      end if;
      declare
         S : constant Mdoc_Spec.Specification := Mdoc_Spec.Spec (I);
      begin
         Verify (S.Version, Hash_P, (Id => Hash_Id, Cfg => S.Hash_Cfg),
                 Sig_P, (Id => Sig_Id, Cfg => S.Sig_Cfg), Pk_X, Pk_Y,
                 Session, Attrs, Now, Doc_Type, B, St, Detail);
      end;
   end Verify_Profile;

end Mdoc_Verifier;
