pragma SPARK_Mode (On);

package body Circuit_Check is

   use type Circuit_Status.Status;
   use type CC.Status;
   use type CK.Status;

   procedure Check
     (Circuit_File     : Byte_Array;
      Certificate_File : Byte_Array;
      R                : out Result)
   is
      No_Pin : constant Bytes_32 := [others => 0];
      P      : CR.Packed_Access;
      H      : CR.Header;
      CSt    : Circuit_Status.Status;
      K      : CC.Cert_Access;
      KSt    : CC.Status;
      WSt    : CK.Status;
   begin
      R := (Outcome     => Circuit_Refused,
            Circuit     => Circuit_Status.Bad_Magic,
            Certificate => CC.Bad_Magic,
            Walk        => CK.Cert_Mismatch);
      CR.Read_Packed (Circuit_File, False, No_Pin, P, H, CSt);
      R.Circuit := CSt;
      if CSt /= Circuit_Status.Ok then
         return;
      end if;
      CC.Read (Certificate_File, K, KSt);
      R.Certificate := KSt;
      if KSt /= CC.Ok then
         R.Outcome := Certificate_Refused;
         CR.Free_Packed (P);
         return;
      end if;
      if K.Circuit_Id /= H.Id then
         R.Outcome := Wrong_Circuit;
         CC.Free (K);
         CR.Free_Packed (P);
         return;
      end if;
      PC.Lemma_Valid (P.all);
      CK.Walk (P.all, K.all, WSt);
      R.Walk := WSt;
      R.Outcome := (if WSt = CK.Accepted then Accepted else Walk_Refused);
      CC.Free (K);
      CR.Free_Packed (P);
   end Check;

end Circuit_Check;
