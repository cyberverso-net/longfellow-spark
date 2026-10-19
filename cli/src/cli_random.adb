pragma SPARK_Mode (Off);

with Simple_Rng;
with Os_Random;

package body Cli_Random is

   Seeded : Boolean := False;

   procedure Set_Seed (S : Unsigned_64) is
   begin
      Simple_Rng.Seed (S);
      Seeded := True;
   end Set_Seed;

   procedure Fill (B : out Byte_Array) is
   begin
      if Seeded then
         Simple_Rng.Fill (B);
      else
         Os_Random.Fill (B);
      end if;
   end Fill;

end Cli_Random;
