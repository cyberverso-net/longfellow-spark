pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;
with Transcript;
with GF2_128;

package body Mdoc_Prover is

   type Buffer_Access is access Byte_Array;

   procedure Free is
     new Ada.Unchecked_Deallocation (Byte_Array, Buffer_Access);

   --  The digest as a P-256 element: big-endian in the digest, little-
   --  endian for From_Bytes; Ok when it is below p.
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
   is
      Max_H : constant Natural :=
        ZKH.Max_Proof_Len (HI.Cfg, ZKH.Shape_Of (Hash_P), HI.Sfb);
      Max_S : constant Natural :=
        ZKS.Max_Proof_Len (SI.Cfg, ZKS.Shape_Of (Sig_P), SI.Sfb);
      CH   : ZKH.Committed;
      CS   : ZKS.Committed;
      PSt  : Prover_Status.Status;
      Av16 : Bytes_16;
      Av   : GF2_128.Element;
      Ok   : Boolean;
      E2   : P256_Field.Element;
   begin
      B      := [others => 0];
      Len    := 0;
      Detail := Prover_Status.Ok;
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
      --  Steps 1 to 3: the transcript, the two commitments.
      Transcript.Reset (Session);
      ZKH.Commit (HI.Sfb, HI.Cfg, Hash_P, Hash_Priv, CH, PSt);
      if PSt /= Prover_Status.Ok then
         St     := Mdoc_Status.Hash_Failed;
         Detail := PSt;
         return;
      end if;
      ZKS.Commit (SI.Sfb, SI.Cfg, Sig_P, Sig_Priv, CS, PSt);
      if PSt /= Prover_Status.Ok then
         ZKH.Release (CH);
         St     := Mdoc_Status.Sig_Failed;
         Detail := PSt;
         return;
      end if;
      --  Steps 4 and 5: av, the tags.
      Transcript.Get_Random_Bytes (Av16);
      GF2_128.From_Bytes (Av16, Av, Ok);
      declare
         T    : constant Mdoc_Mac.Tags := Mdoc_Mac.Legacy_Tags (Av, Ap, M);
         PubH : SAH.Element_Array
           (0 .. Hash_Count (Version, Attrs'Length) - 1);
         PubS : SAP.Element_Array (0 .. Sig_Count - 1);
         Buf  : Buffer_Access;
         LenH : Natural;
         LenS : Natural;
      begin
         --  Step 6: the public inputs.
         Hash_Inputs (Version, Attrs, Now, T, Av, PubH);
         Digest_Element (Device_Auth.Digest (Session, Doc_Type), E2, Ok);
         if not Ok then
            ZKH.Release (CH);
            ZKS.Release (CS);
            St := Mdoc_Status.E2_Not_In_Field;
            return;
         end if;
         Sig_Inputs (Pk_X, Pk_Y, E2, T, Av, PubS);
         --  Step 9 begins: the tags at the front.
         Mdoc_Proof.Write_Tags (T, B (0 .. Mdoc_Proof.Tags_Len - 1));
         --  Step 7: the hash proof, into a buffer of its own length.
         Buf := new Byte_Array'([0 .. Max_H - 1 => 0]);
         ZKH.Prove_Committed
           (HI.Id, HI.Sfb, HI.Cfg, Hash_P, PubH, CH, Buf.all, LenH, PSt);
         if PSt /= Prover_Status.Ok then
            Free (Buf);
            ZKS.Release (CS);
            B      := [others => 0];
            St     := Mdoc_Status.Hash_Failed;
            Detail := PSt;
            return;
         end if;
         B (Mdoc_Proof.Hash_First .. Mdoc_Proof.Hash_First + LenH - 1) :=
           Buf (0 .. LenH - 1);
         Free (Buf);
         --  Step 8: the signature proof after it.
         Buf := new Byte_Array'([0 .. Max_S - 1 => 0]);
         ZKS.Prove_Committed
           (SI.Id, SI.Sfb, SI.Cfg, Sig_P, PubS, CS, Buf.all, LenS, PSt);
         if PSt /= Prover_Status.Ok then
            Free (Buf);
            B      := [others => 0];
            St     := Mdoc_Status.Sig_Failed;
            Detail := PSt;
            return;
         end if;
         B (Mdoc_Proof.Hash_First + LenH
            .. Mdoc_Proof.Hash_First + LenH + LenS - 1) := Buf (0 .. LenS - 1);
         Free (Buf);
         Len := Mdoc_Proof.Hash_First + LenH + LenS;
         St  := Mdoc_Status.Ok;
      end;
   end Prove;

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
   is
      use type Mdoc_Witness.Status;
      P  : Mdoc_Parse.Parsed_Mdoc;
      WS : Mdoc_Witness.Status;
   begin
      Hash_W   := [others => GF2_128.Zero];
      Sig_W    := [others => P256_Field.Zero];
      B        := [others => 0];
      Len      := 0;
      Detail   := Prover_Status.Ok;
      Parse_St := Mdoc_Parse.Ok;
      Cbor_St  := Cbor_Parse.Ok;
      --  The zero of the buffers on each path before the proof is
      --  asserted where it holds, one path at a time, for the provers.
      if Session'Length > Device_Auth.Max_Session_Transcript then
         St := Mdoc_Status.Transcript_Too_Long;
         pragma Assert
           (for all I in Hash_W'Range => Hash_W (I) = GF2_128.Zero);
         return;
      end if;
      Mdoc_Parse.Parse (Mdoc, Session, Doc_Type, Version, P, Parse_St, Cbor_St);
      if Parse_St /= Mdoc_Parse.Ok then
         St := Mdoc_Status.Parse_Failed;
         pragma Assert
           (for all I in Hash_W'Range => Hash_W (I) = GF2_128.Zero);
         return;
      end if;
      Mdoc_Witness.Hash_Witness (Version, Mdoc, P, Attrs, Ap, Hash_W, WS);
      if WS = Mdoc_Witness.Ok then
         Mdoc_Witness.Sig_Witness (Mdoc, P, Pk_X, Pk_Y, Ap, Sig_W, WS);
      end if;
      case WS is
         when Mdoc_Witness.Ok =>
            Prove (Version, Hash_P, HI, Sig_P, SI, Hash_W, Sig_W, Ap,
                   Mdoc_Witness.Messages (P), Pk_X, Pk_Y, Session, Attrs,
                   Now, Doc_Type, B, Len, St, Detail);
         when Mdoc_Witness.Attribute_Not_Found =>
            St := Mdoc_Status.Attribute_Not_Found;
            pragma Assert
              (for all I in Hash_W'Range => Hash_W (I) = GF2_128.Zero);
         when Mdoc_Witness.Attribute_Too_Long =>
            St := Mdoc_Status.Attribute_Too_Long;
            pragma Assert
              (for all I in Hash_W'Range => Hash_W (I) = GF2_128.Zero);
         when Mdoc_Witness.Item_Order_Unsupported =>
            St := Mdoc_Status.Item_Order_Unsupported;
            pragma Assert
              (for all I in Hash_W'Range => Hash_W (I) = GF2_128.Zero);
         when Mdoc_Witness.Signature_Not_Canonical =>
            --  The hash witness was built: cleared, as the contract says.
            Hash_W := [others => GF2_128.Zero];
            St := Mdoc_Status.Signature_Not_Canonical;
            pragma Assert
              (for all I in Hash_W'Range => Hash_W (I) = GF2_128.Zero);
      end case;
   end Prove_Mdoc;

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
   is
      I : Mdoc_Spec.Spec_Index;

      --  A refusal of the profile: everything zero, nothing proved.
      procedure Refuse (S : Mdoc_Status.Status) with
        Global => (Output => (Hash_W, Sig_W, B, Len, St, Detail,
                              Parse_St, Cbor_St)),
        Pre    => S in Mdoc_Status.Profile_Unknown
                     | Mdoc_Status.Profile_Mismatch
                     | Mdoc_Status.Attribute_Count,
        Post   => St = S and then Len = 0
                  and then Detail = Prover_Status.Ok
                  and then Parse_St = Mdoc_Parse.Ok
                  and then (for all J in Hash_W'Range =>
                              Hash_W (J) = GF2_128.Zero)
                  and then (for all J in Sig_W'Range =>
                              Sig_W (J) = P256_Field.Zero)
                  and then (for all J in B'Range => B (J) = 0)
      is
      begin
         Hash_W   := [others => GF2_128.Zero];
         Sig_W    := [others => P256_Field.Zero];
         B        := [others => 0];
         Len      := 0;
         St       := S;
         Detail   := Prover_Status.Ok;
         Parse_St := Mdoc_Parse.Ok;
         Cbor_St  := Cbor_Parse.Ok;
      end Refuse;

      Sel : Mdoc_Status.Status;
   begin
      Mdoc_Spec.Select_Profile
        (Profile, Hash_Id, Sig_Id, Attrs'Length, I, Sel);
      if Sel /= Mdoc_Status.Ok then
         Refuse (Sel);
         return;
      end if;
      declare
         S  : constant Mdoc_Spec.Specification := Mdoc_Spec.Spec (I);
         HI : constant Circuit_Info :=
           (Id => Hash_Id, Sfb => Hash_Sfb, Cfg => S.Hash_Cfg);
         SI : constant Circuit_Info :=
           (Id => Sig_Id, Sfb => Sig_Sfb, Cfg => S.Sig_Cfg);
      begin
         if not (Hash_Ok (Hash_P, HI.Cfg) and then Sig_Ok (Sig_P, SI.Cfg)
                 and then Parts_Fit (Hash_P, HI, Sig_P, SI)
                 and then Hash_W'First = 0
                 and then Hash_W'Length
                          = Mdoc_Witness.Hash_Count (S.Version, Attrs'Length)
                 and then Sig_W'First = 0
                 and then Sig_W'Length = Mdoc_Witness.Sig_Count
                 and then B'First = 0
                 and then B'Length = Max_Len (Hash_P, HI, Sig_P, SI))
         then
            Refuse (Mdoc_Status.Profile_Mismatch);
            return;
         end if;
         Prove_Mdoc (S.Version, Hash_P, HI, Sig_P, SI, Mdoc, Ap, Pk_X, Pk_Y,
                     Session, Attrs, Now, Doc_Type, Hash_W, Sig_W, B, Len,
                     St, Detail, Parse_St, Cbor_St);
         --  Any other refusal, of the request, of the witness or of the
         --  proof: the witnesses built from the credential and the proof
         --  buffer are wiped, so that a refusal leaves only a status.
         if St /= Mdoc_Status.Ok then
            Hash_W := [others => GF2_128.Zero];
            Sig_W  := [others => P256_Field.Zero];
            B      := [others => 0];
         end if;
      end;
   end Prove_Profile;

end Mdoc_Prover;
