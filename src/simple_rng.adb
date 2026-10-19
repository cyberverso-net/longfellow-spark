pragma SPARK_Mode (On);

package body Simple_Rng with
  Refined_State => (State => Current)
is

   Current : Unsigned_64 := 0;

   procedure Seed (S : Unsigned_64) is
   begin
      Current := S;
   end Seed;

   procedure Fill (B : out Byte_Array) is
   begin
      for I in B'Range loop
         Current := Current * 6364136223846793005 + 1442695040888963407;
         B (I) := Unsigned_8 (Shift_Right (Current, 32) and 16#FF#);
      end loop;
   end Fill;

end Simple_Rng;
