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

end Mdoc_Prover;
