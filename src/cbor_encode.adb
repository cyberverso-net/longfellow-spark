pragma SPARK_Mode (On);

package body Cbor_Encode is

   function Head (Major : Unsigned_8; N : Natural) return Byte_Array is
   begin
      if N <= 23 then
         return [0 => Major or Unsigned_8 (N)];
      elsif N <= 255 then
         return [0 => Major or 24, 1 => Unsigned_8 (N)];
      elsif N <= 65535 then
         return [0 => Major or 25,
                 1 => Unsigned_8 (N / 256),
                 2 => Unsigned_8 (N mod 256)];
      else
         return [0 => Major or 26,
                 1 => Unsigned_8 (N / 2**24),
                 2 => Unsigned_8 ((N / 2**16) mod 256),
                 3 => Unsigned_8 ((N / 256) mod 256),
                 4 => Unsigned_8 (N mod 256)];
      end if;
   end Head;

end Cbor_Encode;
