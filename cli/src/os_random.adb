pragma SPARK_Mode (Off);

with Ada.Streams.Stream_IO;
with Interfaces;

package body Os_Random is

   Device : constant String := "/dev/urandom";

   procedure Fill (B : out Byte_Array) is
      use Ada.Streams;
      use Ada.Streams.Stream_IO;
      F    : File_Type;
      S    : Stream_Element_Array (1 .. Stream_Element_Offset (B'Length));
      Last : Stream_Element_Offset;
   begin
      B := [others => 0];
      if B'Length = 0 then
         return;
      end if;
      Open (F, In_File, Device);
      Read (F, S, Last);
      Close (F);
      if Natural (Last) /= B'Length then
         raise Program_Error with "short read of " & Device;
      end if;
      for I in S'Range loop
         B (B'First + Natural (I) - 1) := Interfaces.Unsigned_8 (S (I));
      end loop;
   exception
      when others =>
         raise Program_Error with "cannot read " & Device;
   end Fill;

end Os_Random;
