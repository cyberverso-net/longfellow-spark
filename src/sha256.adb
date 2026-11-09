pragma SPARK_Mode (On);

package body Sha256 is

   --  Section 6.2.2: one block into the state, the 64 bytes of Data
   --  from First, read in place so that whole blocks of the input are
   --  not copied into the context first. The child Sha256.Trace repeats
   --  this procedure with the words of the rounds written out, over
   --  the same functions and constants of the private part.
   procedure Compress (H : in out State; Data : Byte_Array; First : Natural)
   with
     Global => null,
     Inline,
     Pre    => First >= Data'First and then Data'Last >= First
               and then Data'Last - First >= 63
   is
      type Schedule is array (Round_Index) of Unsigned_32;
      --  Zeroed first so that flow analysis has it initialised; the
      --  loop below assigns every word.
      W : Schedule := [others => 0];
      A, B, C, D, E, F, G, HH, T1, T2 : Unsigned_32;
   begin
      --  The first sixteen words are the block, big-endian, the rest
      --  the recurrence of Section 6.2.2 step 1.
      for T in Round_Index range 0 .. 15 loop
         pragma Loop_Optimize (No_Vector, Unroll);
         W (T) :=
           Shift_Left (Unsigned_32 (Data (First + 4 * Natural (T))), 24)
           or Shift_Left (Unsigned_32 (Data (First + 4 * Natural (T) + 1)), 16)
           or Shift_Left (Unsigned_32 (Data (First + 4 * Natural (T) + 2)), 8)
           or Unsigned_32 (Data (First + 4 * Natural (T) + 3));
      end loop;
      for T in Round_Index range 16 .. 63 loop
         pragma Loop_Optimize (No_Vector, Unroll);
         W (T) :=
           Small_1 (W (T - 2)) + W (T - 7) + Small_0 (W (T - 15)) + W (T - 16);
      end loop;

      A  := H (0);
      B  := H (1);
      C  := H (2);
      D  := H (3);
      E  := H (4);
      F  := H (5);
      G  := H (6);
      HH := H (7);

      for T in Round_Index loop
         pragma Loop_Optimize (No_Vector, Unroll);
         T1 := HH + Sigma_1 (E) + Ch (E, F, G) + K (T) + W (T);
         T2 := Sigma_0 (A) + Maj (A, B, C);
         HH := G;
         G  := F;
         F  := E;
         E  := D + T1;
         D  := C;
         C  := B;
         B  := A;
         A  := T1 + T2;
      end loop;

      H (0) := H (0) + A;
      H (1) := H (1) + B;
      H (2) := H (2) + C;
      H (3) := H (3) + D;
      H (4) := H (4) + E;
      H (5) := H (5) + F;
      H (6) := H (6) + G;
      H (7) := H (7) + HH;
   end Compress;

   --  One byte into the block buffer, compressing when it fills. The
   --  postcondition on Fill is what the padding loop of Digest needs.
   procedure Put (Ctx : in out Context; B : Unsigned_8) with
     Global => null,
     Inline,
     Post   => Ctx.Fill = (if Ctx.Fill'Old = 63 then 0 else Ctx.Fill'Old + 1)
   is
   begin
      Ctx.Block (Ctx.Fill) := B;
      Ctx.Total := Ctx.Total + 1;
      if Ctx.Fill = 63 then
         Compress (Ctx.H, Ctx.Block, 0);
         Ctx.Fill := 0;
      else
         Ctx.Fill := Ctx.Fill + 1;
      end if;
   end Put;

   function Initial return Context is
     (H     => Initial_State,
      Block => [others => 0],
      Fill  => 0,
      Total => 0);

   procedure Update_Nonempty (Ctx : in out Context; Data : Byte_Array) with
     Global => null,
     Pre    => Data'Length > 0;

   --  Bytes one at a time until the buffer is empty, then the whole
   --  blocks of Data straight into the state, then the rest into the
   --  buffer.
   procedure Update (Ctx : in out Context; Data : Byte_Array) is
   begin
      --  The bounds of an empty array need not be in Byte_Index.
      if Data'Length = 0 then
         return;
      end if;
      Update_Nonempty (Ctx, Data);
   end Update;

   procedure Update_Nonempty (Ctx : in out Context; Data : Byte_Array) is
      --  The next byte of Data to take; Data'Last + 1 once all are.
      I : Natural := Data'First;
   begin
      while Ctx.Fill /= 0 and then I <= Data'Last loop
         pragma Loop_Invariant (I in Data'First .. Data'Last);
         pragma Loop_Variant (Increases => I);
         Put (Ctx, Data (I));
         I := I + 1;
      end loop;
      while I <= Data'Last and then Data'Last - I >= 63 loop
         pragma Loop_Invariant (I in Data'First .. Data'Last);
         pragma Loop_Invariant (Ctx.Fill = 0);
         pragma Loop_Variant (Increases => I);
         Compress (Ctx.H, Data, I);
         Ctx.Total := Ctx.Total + 64;
         I := I + 64;
      end loop;
      for J in I .. Data'Last loop
         Put (Ctx, Data (J));
      end loop;
   end Update_Nonempty;

   function Digest (Ctx : Context) return Bytes_32 is
      C      : Context := Ctx;
      Length : constant Unsigned_64 := Shift_Left (Ctx.Total, 3);
      Out_B  : Bytes_32 := [others => 0];
   begin
      --  Section 5.1.1: the bit 1, zeros to 56 bytes modulo 64, then
      --  the bit length as a 64-bit big-endian integer.
      Put (C, 16#80#);
      while C.Fill /= 56 loop
         pragma Loop_Variant (Increases => (if C.Fill < 56 then C.Fill
                                            else C.Fill - 64));
         Put (C, 0);
      end loop;
      for I in 0 .. 7 loop
         Put (C, Unsigned_8 (Shift_Right (Length, 56 - 8 * I) and 16#FF#));
      end loop;
      --  Fill is 0 again: the length filled the block and Put compressed.
      --  Word I goes to bytes 4 I .. 4 I + 3, big-endian. Literal shift
      --  amounts and "mod 256" rather than a mask, so that the range
      --  check of the conversion is plain arithmetic for the provers.
      for I in Word_Index loop
         Out_B (4 * Natural (I)) :=
           Unsigned_8 (Shift_Right (C.H (I), 24) mod 256);
         Out_B (4 * Natural (I) + 1) :=
           Unsigned_8 (Shift_Right (C.H (I), 16) mod 256);
         Out_B (4 * Natural (I) + 2) :=
           Unsigned_8 (Shift_Right (C.H (I), 8) mod 256);
         Out_B (4 * Natural (I) + 3) := Unsigned_8 (C.H (I) mod 256);
      end loop;
      return Out_B;
   end Digest;

end Sha256;
