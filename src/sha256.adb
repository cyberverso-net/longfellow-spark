pragma SPARK_Mode (On);

package body Sha256 is

   --  FIPS 180-4 Section 4.2.2: the first 32 bits of the fractional
   --  parts of the cube roots of the first 64 primes.
   type Round_Index is range 0 .. 63;
   type Round_Constants is array (Round_Index) of Unsigned_32;

   K : constant Round_Constants :=
     [16#428A2F98#, 16#71374491#, 16#B5C0FBCF#, 16#E9B5DBA5#,
      16#3956C25B#, 16#59F111F1#, 16#923F82A4#, 16#AB1C5ED5#,
      16#D807AA98#, 16#12835B01#, 16#243185BE#, 16#550C7DC3#,
      16#72BE5D74#, 16#80DEB1FE#, 16#9BDC06A7#, 16#C19BF174#,
      16#E49B69C1#, 16#EFBE4786#, 16#0FC19DC6#, 16#240CA1CC#,
      16#2DE92C6F#, 16#4A7484AA#, 16#5CB0A9DC#, 16#76F988DA#,
      16#983E5152#, 16#A831C66D#, 16#B00327C8#, 16#BF597FC7#,
      16#C6E00BF3#, 16#D5A79147#, 16#06CA6351#, 16#14292967#,
      16#27B70A85#, 16#2E1B2138#, 16#4D2C6DFC#, 16#53380D13#,
      16#650A7354#, 16#766A0ABB#, 16#81C2C92E#, 16#92722C85#,
      16#A2BFE8A1#, 16#A81A664B#, 16#C24B8B70#, 16#C76C51A3#,
      16#D192E819#, 16#D6990624#, 16#F40E3585#, 16#106AA070#,
      16#19A4C116#, 16#1E376C08#, 16#2748774C#, 16#34B0BCB5#,
      16#391C0CB3#, 16#4ED8AA4A#, 16#5B9CCA4F#, 16#682E6FF3#,
      16#748F82EE#, 16#78A5636F#, 16#84C87814#, 16#8CC70208#,
      16#90BEFFFA#, 16#A4506CEB#, 16#BEF9A3F7#, 16#C67178F2#];

   --  FIPS 180-4 Section 5.3.3: the initial hash value.
   H0 : constant State :=
     [16#6A09E667#, 16#BB67AE85#, 16#3C6EF372#, 16#A54FF53A#,
      16#510E527F#, 16#9B05688C#, 16#1F83D9AB#, 16#5BE0CD19#];

   --  The six functions of Section 4.1.2.
   function Ch (X, Y, Z : Unsigned_32) return Unsigned_32 is
     ((X and Y) xor ((not X) and Z));

   function Maj (X, Y, Z : Unsigned_32) return Unsigned_32 is
     ((X and Y) xor (X and Z) xor (Y and Z));

   function Sigma_0 (X : Unsigned_32) return Unsigned_32 is
     (Rotate_Right (X, 2) xor Rotate_Right (X, 13) xor Rotate_Right (X, 22));

   function Sigma_1 (X : Unsigned_32) return Unsigned_32 is
     (Rotate_Right (X, 6) xor Rotate_Right (X, 11) xor Rotate_Right (X, 25));

   function Small_0 (X : Unsigned_32) return Unsigned_32 is
     (Rotate_Right (X, 7) xor Rotate_Right (X, 18) xor Shift_Right (X, 3));

   function Small_1 (X : Unsigned_32) return Unsigned_32 is
     (Rotate_Right (X, 17) xor Rotate_Right (X, 19) xor Shift_Right (X, 10));

   --  Section 6.2.2: one block into the state.
   procedure Compress (H : in out State; Block : Bytes_64) with
     Global => null
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
         W (T) :=
           Shift_Left (Unsigned_32 (Block (4 * Natural (T))), 24)
           or Shift_Left (Unsigned_32 (Block (4 * Natural (T) + 1)), 16)
           or Shift_Left (Unsigned_32 (Block (4 * Natural (T) + 2)), 8)
           or Unsigned_32 (Block (4 * Natural (T) + 3));
      end loop;
      for T in Round_Index range 16 .. 63 loop
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
     Post   => Ctx.Fill = (if Ctx.Fill'Old = 63 then 0 else Ctx.Fill'Old + 1)
   is
   begin
      Ctx.Block (Ctx.Fill) := B;
      Ctx.Total := Ctx.Total + 1;
      if Ctx.Fill = 63 then
         Compress (Ctx.H, Ctx.Block);
         Ctx.Fill := 0;
      else
         Ctx.Fill := Ctx.Fill + 1;
      end if;
   end Put;

   function Initial return Context is
     (H     => H0,
      Block => [others => 0],
      Fill  => 0,
      Total => 0);

   procedure Update (Ctx : in out Context; Data : Byte_Array) is
   begin
      for I in Data'Range loop
         Put (Ctx, Data (I));
      end loop;
   end Update;

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
