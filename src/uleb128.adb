pragma SPARK_Mode (On);

package body Uleb128 is

   procedure Read
     (B    : Byte_Array;
      Pos  : in out Natural;
      V    : out Value;
      Ok   : out Boolean;
      Long : out Boolean)
   is
      Acc  : Natural := 0;
      Byte : Unsigned_8;
   begin
      V    := 0;
      Ok   := False;
      Long := False;
      for I in 0 .. Max_Bytes - 1 loop
         pragma Loop_Invariant (Pos = Pos'Loop_Entry);
         pragma Loop_Invariant (Acc = Payload (B, Pos, I));
         pragma Loop_Invariant (Acc < Pow128 (I));
         if B'Length - Pos <= I then
            return;
         end if;
         Byte := B (Pos + I);
         Acc  := Acc + Natural (Byte and 16#7F#) * Pow128 (I);
         pragma Assert (Acc = Payload (B, Pos, I + 1));
         if (Byte and 16#80#) = 0 then
            V   := Acc;
            Pos := Pos + I + 1;
            Ok  := True;
            return;
         end if;
      end loop;
      Long := True;
   end Read;

end Uleb128;
