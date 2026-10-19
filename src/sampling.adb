pragma SPARK_Mode (On);

package body Sampling is

   procedure Sample_Element (E : out Element) is
      B  : Byte_Array (0 .. F.Serialized_Size - 1);
      Ok : Boolean;
   begin
      Fill (B);
      F.From_Bytes (B, E, Ok);
      if F.Sampling_Rejects then
         --  Rejection sampling with no cap (ADR 0030): the loop is the
         --  reason the procedure is possibly non-terminating for a
         --  field that rejects.
         while not Ok loop
            Fill (B);
            F.From_Bytes (B, E, Ok);
         end loop;
      end if;
   end Sample_Element;

   procedure Sample_Subfield (E : out Element) is
      B  : Byte_Array (0 .. F.Subfield_Size - 1);
      Ok : Boolean;
   begin
      Fill (B);
      F.From_Subfield_Bytes (B, E, Ok);
      if F.Sampling_Rejects then
         while not Ok loop
            Fill (B);
            F.From_Subfield_Bytes (B, E, Ok);
         end loop;
      end if;
   end Sample_Subfield;

   procedure Sample_Nonce (N : out Bytes_32) is
   begin
      Fill (N);
   end Sample_Nonce;

end Sampling;
