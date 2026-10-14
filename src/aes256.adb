pragma SPARK_Mode (On);

with Interfaces; use Interfaces;

package body Aes256 is

   --  FIPS 197 Figure 7: the S-box, generated from its definition
   --  (inverse in GF(2^8), then the affine map) by the vector generator
   --  gen_transcript_vectors.py and checked there against the first
   --  row of the figure.
   type Sbox_Table is array (Unsigned_8) of Unsigned_8;

   Sbox : constant Sbox_Table :=
     [16#63#, 16#7C#, 16#77#, 16#7B#, 16#F2#, 16#6B#, 16#6F#, 16#C5#,
      16#30#, 16#01#, 16#67#, 16#2B#, 16#FE#, 16#D7#, 16#AB#, 16#76#,
      16#CA#, 16#82#, 16#C9#, 16#7D#, 16#FA#, 16#59#, 16#47#, 16#F0#,
      16#AD#, 16#D4#, 16#A2#, 16#AF#, 16#9C#, 16#A4#, 16#72#, 16#C0#,
      16#B7#, 16#FD#, 16#93#, 16#26#, 16#36#, 16#3F#, 16#F7#, 16#CC#,
      16#34#, 16#A5#, 16#E5#, 16#F1#, 16#71#, 16#D8#, 16#31#, 16#15#,
      16#04#, 16#C7#, 16#23#, 16#C3#, 16#18#, 16#96#, 16#05#, 16#9A#,
      16#07#, 16#12#, 16#80#, 16#E2#, 16#EB#, 16#27#, 16#B2#, 16#75#,
      16#09#, 16#83#, 16#2C#, 16#1A#, 16#1B#, 16#6E#, 16#5A#, 16#A0#,
      16#52#, 16#3B#, 16#D6#, 16#B3#, 16#29#, 16#E3#, 16#2F#, 16#84#,
      16#53#, 16#D1#, 16#00#, 16#ED#, 16#20#, 16#FC#, 16#B1#, 16#5B#,
      16#6A#, 16#CB#, 16#BE#, 16#39#, 16#4A#, 16#4C#, 16#58#, 16#CF#,
      16#D0#, 16#EF#, 16#AA#, 16#FB#, 16#43#, 16#4D#, 16#33#, 16#85#,
      16#45#, 16#F9#, 16#02#, 16#7F#, 16#50#, 16#3C#, 16#9F#, 16#A8#,
      16#51#, 16#A3#, 16#40#, 16#8F#, 16#92#, 16#9D#, 16#38#, 16#F5#,
      16#BC#, 16#B6#, 16#DA#, 16#21#, 16#10#, 16#FF#, 16#F3#, 16#D2#,
      16#CD#, 16#0C#, 16#13#, 16#EC#, 16#5F#, 16#97#, 16#44#, 16#17#,
      16#C4#, 16#A7#, 16#7E#, 16#3D#, 16#64#, 16#5D#, 16#19#, 16#73#,
      16#60#, 16#81#, 16#4F#, 16#DC#, 16#22#, 16#2A#, 16#90#, 16#88#,
      16#46#, 16#EE#, 16#B8#, 16#14#, 16#DE#, 16#5E#, 16#0B#, 16#DB#,
      16#E0#, 16#32#, 16#3A#, 16#0A#, 16#49#, 16#06#, 16#24#, 16#5C#,
      16#C2#, 16#D3#, 16#AC#, 16#62#, 16#91#, 16#95#, 16#E4#, 16#79#,
      16#E7#, 16#C8#, 16#37#, 16#6D#, 16#8D#, 16#D5#, 16#4E#, 16#A9#,
      16#6C#, 16#56#, 16#F4#, 16#EA#, 16#65#, 16#7A#, 16#AE#, 16#08#,
      16#BA#, 16#78#, 16#25#, 16#2E#, 16#1C#, 16#A6#, 16#B4#, 16#C6#,
      16#E8#, 16#DD#, 16#74#, 16#1F#, 16#4B#, 16#BD#, 16#8B#, 16#8A#,
      16#70#, 16#3E#, 16#B5#, 16#66#, 16#48#, 16#03#, 16#F6#, 16#0E#,
      16#61#, 16#35#, 16#57#, 16#B9#, 16#86#, 16#C1#, 16#1D#, 16#9E#,
      16#E1#, 16#F8#, 16#98#, 16#11#, 16#69#, 16#D9#, 16#8E#, 16#94#,
      16#9B#, 16#1E#, 16#87#, 16#E9#, 16#CE#, 16#55#, 16#28#, 16#DF#,
      16#8C#, 16#A1#, 16#89#, 16#0D#, 16#BF#, 16#E6#, 16#42#, 16#68#,
      16#41#, 16#99#, 16#2D#, 16#0F#, 16#B0#, 16#54#, 16#BB#, 16#16#];

   --  Multiplication by x in GF(2^8) modulo x^8 + x^4 + x^3 + x + 1
   --  (Section 4.2.1). The conditional is on data, as the exemption
   --  in the header allows.
   function Xtime (A : Unsigned_8) return Unsigned_8 is
     (if (A and 16#80#) /= 0 then Shift_Left (A, 1) xor 16#1B#
      else Shift_Left (A, 1));

   subtype Word is Byte_Array (0 .. 3);

   --  Section 5.2: w (i) = w (i - 8) xor f (w (i - 1)), where f is
   --  RotWord then SubWord then the round constant when i is a
   --  multiple of 8, SubWord alone when i is 4 modulo 8, and the
   --  identity otherwise. Word i lives in round key i / 4 at bytes
   --  4 (i mod 4) .. 4 (i mod 4) + 3.
   function Expand_Key (Key : Bytes_32) return Key_Schedule is
      KS   : Key_Schedule;
      T    : Word;
      Prev : Word;
      Rcon : Unsigned_8 := 1;
   begin
      KS.Keys := [others => [others => 0]];
      for I in 0 .. 7 loop
         KS.Keys (Round_Index (I / 4)) (4 * (I mod 4) .. 4 * (I mod 4) + 3) :=
           Key (4 * I .. 4 * I + 3);
      end loop;
      for I in 8 .. 59 loop
         Prev :=
           KS.Keys (Round_Index ((I - 1) / 4))
             (4 * ((I - 1) mod 4) .. 4 * ((I - 1) mod 4) + 3);
         if I mod 8 = 0 then
            T := [Sbox (Prev (1)) xor Rcon, Sbox (Prev (2)),
                  Sbox (Prev (3)), Sbox (Prev (0))];
            Rcon := Xtime (Rcon);
         elsif I mod 8 = 4 then
            T := [Sbox (Prev (0)), Sbox (Prev (1)),
                  Sbox (Prev (2)), Sbox (Prev (3))];
         else
            T := Prev;
         end if;
         declare
            Back : constant Word :=
              KS.Keys (Round_Index ((I - 8) / 4))
                (4 * ((I - 8) mod 4) .. 4 * ((I - 8) mod 4) + 3);
         begin
            for J in 0 .. 3 loop
               KS.Keys (Round_Index (I / 4)) (4 * (I mod 4) + J) :=
                 Back (J) xor T (J);
            end loop;
         end;
      end loop;
      return KS;
   end Expand_Key;

   --  Section 5.1.1.
   procedure Sub_Bytes (S : in out Bytes_16) with Global => null is
   begin
      for I in S'Range loop
         S (I) := Sbox (S (I));
      end loop;
   end Sub_Bytes;

   --  Section 5.1.2: row r is rotated left by r positions, that is
   --  s' (r, c) = s (r, (c + r) mod 4).
   procedure Shift_Rows (S : in out Bytes_16) with Global => null is
      T : constant Bytes_16 := S;
   begin
      for C in 0 .. 3 loop
         for R in 0 .. 3 loop
            S (4 * C + R) := T (4 * ((C + R) mod 4) + R);
         end loop;
      end loop;
   end Shift_Rows;

   --  Section 5.1.3, one column: multiplication by the fixed
   --  polynomial {03} x^3 + {01} x^2 + {01} x + {02}.
   procedure Mix_Columns (S : in out Bytes_16) with Global => null is
      A0, A1, A2, A3 : Unsigned_8;
   begin
      for C in 0 .. 3 loop
         A0 := S (4 * C);
         A1 := S (4 * C + 1);
         A2 := S (4 * C + 2);
         A3 := S (4 * C + 3);
         S (4 * C)     := Xtime (A0) xor Xtime (A1) xor A1 xor A2 xor A3;
         S (4 * C + 1) := A0 xor Xtime (A1) xor Xtime (A2) xor A2 xor A3;
         S (4 * C + 2) := A0 xor A1 xor Xtime (A2) xor Xtime (A3) xor A3;
         S (4 * C + 3) := Xtime (A0) xor A0 xor A1 xor A2 xor Xtime (A3);
      end loop;
   end Mix_Columns;

   procedure Add_Round_Key (S : in out Bytes_16; RK : Bytes_16) with
     Global => null
   is
   begin
      for I in S'Range loop
         S (I) := S (I) xor RK (I);
      end loop;
   end Add_Round_Key;

   function Encrypt (KS : Key_Schedule; Input : Bytes_16) return Bytes_16
   is
      S : Bytes_16 := Input;
   begin
      Add_Round_Key (S, KS.Keys (0));
      for R in Round_Index range 1 .. Rounds - 1 loop
         Sub_Bytes (S);
         Shift_Rows (S);
         Mix_Columns (S);
         Add_Round_Key (S, KS.Keys (R));
      end loop;
      Sub_Bytes (S);
      Shift_Rows (S);
      Add_Round_Key (S, KS.Keys (Rounds));
      return S;
   end Encrypt;

end Aes256;
