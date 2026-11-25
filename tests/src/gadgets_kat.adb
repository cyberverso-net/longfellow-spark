--  gadgets_kat: the tests of the gadgets of the SHA-256 circuit and of
--  the reference netlist (ADR 0091, piece 2; chapter 10, Section 2).
--
--    lean   : the vectors of the Lean model of GF(2^128)
--             (tests/vectors/lean_gf2_128.txt, from
--             lean/scripts/Vectors.lean) against GF2_128.Mul and the
--             constants Alpha_2 and Shift of Gadgets.Words.
--    G1     : Gadgets.Bits. The interpolation at the 64 points (bit K of
--             nibble I at Point (I)), the constant terms C (K, 0)
--             neither 0 nor 1 and equal to p_K (0), packed words decoded
--             to the word they were packed from, and the bridged
--             statement Lemma_Output_Is_Bit evaluated on every element
--             tried.
--    G3     : Gadgets.Words. The bridged statement Lemma_Assert_Eqmod
--             evaluated, premise and conclusion, for K from 1 to 7: on
--             random words, with a equal to the sum, off by one, off in
--             the top bit; on sums that pass 2^32 (they differ from a by
--             a multiple of 2^32); on an operand that is not a bit.
--    netlist: Sha256.Trace.Netlist.Interpret against the traced
--             compression on the NIST vectors (FIPS 180-4 examples
--             "abc" and the two blocks of the 448-bit message) and on
--             random blocks and states.
--    G4     : Sha256.Trace.Netlist.Gadget. On the same blocks every
--             assertion holds on the honest trace; a word of the
--             witness off by one (a schedule word, an e, an a, a word of
--             the new state) makes its own assertion fail.
--
--  Run: tests/bin/gadgets_kat [tests/vectors/lean_gf2_128.txt]

pragma SPARK_Mode (Off);

with Ada.Command_Line; use Ada.Command_Line;
with Ada.Text_IO;      use Ada.Text_IO;
with Interfaces;       use Interfaces;
with Bytes;            use Bytes;
with GF2_128;          use GF2_128;
with Gadgets;          use Gadgets;

--  Element is GF2_128.Element, named through Gadgets.
with Gadgets.Bits;
with Gadgets.Words;
with Sha256;
with Sha256.Trace;
with Sha256.Trace.Netlist.Gadget;
with Block_Checks;

procedure Gadgets_KAT is

   subtype Element is GF2_128.Element;

   package GB renames Gadgets.Bits;
   package GW renames Gadgets.Words;
   package Netlist renames Sha256.Trace.Netlist;
   package Gadget renames Sha256.Trace.Netlist.Gadget;

   Failures : Natural := 0;
   Passed   : Natural := 0;

   procedure Check (Label : String; Ok : Boolean) is
   begin
      if Ok then
         Passed := Passed + 1;
      else
         Failures := Failures + 1;
         Put_Line ("FAIL " & Label);
      end if;
   end Check;

   --  xorshift64*, for operands spread over the whole field.
   Seed : Unsigned_64 := 16#9E37_79B9_7F4A_7C15#;

   function Next return Unsigned_64 is
   begin
      Seed := Seed xor Shift_Right (Seed, 12);
      Seed := Seed xor Shift_Left (Seed, 25);
      Seed := Seed xor Shift_Right (Seed, 27);
      return Seed * 16#2545_F491_4F6C_DD1D#;
   end Next;

   function Random_Element return Element is
     ((Limbs => [0 => Next, 1 => Next]));

   function Random_Word return Unsigned_32 is
     (Unsigned_32 (Shift_Right (Next, 32)));

   ----------------------------------------------------------------------
   --  The Lean vectors
   ----------------------------------------------------------------------

   function Hex_Digit (C : Character) return Unsigned_64 is
     (case C is
        when '0' .. '9' => Character'Pos (C) - Character'Pos ('0'),
        when 'a' .. 'f' => Character'Pos (C) - Character'Pos ('a') + 10,
        when others     => raise Constraint_Error with "bad hex digit");

   --  32 hexadecimal digits, the coefficient of x^127 first.
   function To_Element (S : String) return Element is
      R : Element := Zero;
   begin
      if S'Length /= 32 then
         raise Constraint_Error with "expected 32 hex digits: " & S;
      end if;
      for I in 0 .. 31 loop
         declare
            L : constant Limb_Index := (if I < 16 then 1 else 0);
         begin
            R.Limbs (L) :=
              Shift_Left (R.Limbs (L), 4) or Hex_Digit (S (S'First + I));
         end;
      end loop;
      return R;
   end To_Element;

   procedure Lean_Vectors (Path : String) is
      F     : File_Type;
      Lines : Natural := 0;
   begin
      Open (F, In_File, Path);
      while not End_Of_File (F) loop
         declare
            L : constant String := Get_Line (F);
            function Field (N : Positive) return String is
               Start : Natural := L'First;
               Count : Natural := 0;
            begin
               for I in L'Range loop
                  if L (I) = ' ' then
                     Count := Count + 1;
                     if Count = N then
                        return L (Start .. I - 1);
                     end if;
                     Start := I + 1;
                  end if;
               end loop;
               return L (Start .. L'Last);
            end Field;
         begin
            if L'Length > 0 and then L (L'First) /= '#' then
               Lines := Lines + 1;
               if Field (1) = "mul" then
                  Check ("lean " & L,
                         Mul (To_Element (Field (2)), To_Element (Field (3)))
                         = To_Element (Field (4)));
               elsif Field (1) = "alpha2" then
                  Check ("lean " & L,
                         GW.Alpha_2 (Natural'Value (Field (2)))
                         = To_Element (Field (3)));
               elsif Field (1) = "shift" then
                  Check ("lean " & L,
                         GW.Shift (Natural'Value (Field (2)))
                         = To_Element (Field (3)));
               else
                  Check ("lean: unknown line " & L, False);
               end if;
            end if;
         end;
      end loop;
      Close (F);
      Check ("lean: the vector file is not empty", Lines > 0);
      Put_Line ("lean:" & Lines'Image & " vectors");
   end Lean_Vectors;

   ----------------------------------------------------------------------
   --  G1
   ----------------------------------------------------------------------

   C : constant GB.Coefficients := GB.Interpolate;

   --  The bridged statement of G1, evaluated: the premise implies the
   --  conclusion, and the bits satisfy the premise.
   procedure Output_Is_Bit (Label : String; V : Element) is
      Premise : constant Boolean := GB.Bit_Assertion (V) = Zero;
   begin
      Check ("G1 bridge " & Label, not Premise or else Is_Bit (V));
      Check ("G1 bits satisfy the assertion " & Label,
             not Is_Bit (V) or else Premise);
   end Output_Is_Bit;

   procedure Test_G1 is
      P : GB.Packed_Word;
      V : Unsigned_32;
   begin
      for I in GB.Nibble loop
         for K in GB.Pluck_Index loop
            Check ("G1 point" & I'Image & K'Image,
                   GB.Pluck (C, K, GB.Point (I))
                   = (if (I / 2 ** K) mod 2 = 1 then One else Zero));
            Output_Is_Bit ("output at a point",
                           GB.Pluck (C, K, GB.Point (I)));
         end loop;
      end loop;
      for K in GB.Pluck_Index loop
         Check ("G1 constant term" & K'Image & " is not a bit",
                not Is_Bit (C (K, 0)));
         Check ("G1 constant term" & K'Image & " is p_k (0)",
                GB.Pluck (C, K, Zero) = C (K, 0));
         Output_Is_Bit ("constant term", C (K, 0));
      end loop;
      Output_Is_Bit ("zero", Zero);
      Output_Is_Bit ("one", One);
      Output_Is_Bit ("x", X);
      for N in 1 .. 200 loop
         Output_Is_Bit ("random", Random_Element);
      end loop;
      --  Packed words, as the witness packs them (Mdoc_Witness).
      for N in 1 .. 50 loop
         V := Random_Word;
         for I in GB.Packed_Index loop
            P (I) := GB.Point (Natural (Shift_Right (V, 4 * I) and 15));
         end loop;
         Check ("G1 decode", GB.Decode (C, P) = V);
         Check ("G1 plucks hold", GB.Plucks_Hold (C, P));
      end loop;
      --  A packed element off the 16 points: the outputs are not bits.
      P := [others => GB.Point (0)];
      P (3) := Random_Element;
      Check ("G1 an element off the points fails its assertions",
             not GB.Plucks_Hold (C, P));
   end Test_G1;

   ----------------------------------------------------------------------
   --  G3
   ----------------------------------------------------------------------

   --  The bridged statement of G3, evaluated: when the premise holds,
   --  the assertion is zero exactly when the sum matches. Expect_Zero
   --  is what the case is built to give.
   procedure Eqmod
     (Label : String; L : GW.Word_List; K : GW.Term_Count;
      A : Word_Bits; Expect_Zero : Boolean)
   is
      Premise : constant Boolean := GW.All_Bits (L, K) and then All_Bits (A);
      Zero_A  : constant Boolean := GW.Assertion (L, K, A) = Zero;
      Matches : constant Boolean :=
        GW.Sum_Upto (L, K) mod 2 ** 32 = Value (A);
   begin
      Check ("G3 premise " & Label, Premise);
      Check ("G3 bridge " & Label, Zero_A = Matches);
      Check ("G3 expected " & Label, Zero_A = Expect_Zero);
   end Eqmod;

   procedure Test_G3 is
      L : GW.Word_List;
      S : Unsigned_32;
   begin
      for K in GW.Term_Count loop
         for N in 1 .. 6 loop
            S := 0;
            L := [others => Bits_Of (0)];
            for J in 0 .. K - 1 loop
               declare
                  W : constant Unsigned_32 := Random_Word;
               begin
                  L (J) := Bits_Of (W);
                  S := S + W;
               end;
            end loop;
            Eqmod ("sum k =" & K'Image, L, K, Bits_Of (S), True);
            Eqmod ("off by one k =" & K'Image, L, K, Bits_Of (S + 1), False);
            Eqmod ("top bit k =" & K'Image, L, K,
                   Bits_Of (S xor 16#8000_0000#), False);
         end loop;
         --  All words 2^32 - 1: the sum is K 2^32 - K, a multiple of
         --  2^32 away from 2^32 - K.
         L := [others => Bits_Of (16#FFFF_FFFF#)];
         Eqmod ("wrap k =" & K'Image, L, K,
                Bits_Of (Unsigned_32'Last - Unsigned_32 (K) + 1), True);
         Eqmod ("wrap off by one k =" & K'Image, L, K,
                Bits_Of (Unsigned_32'Last - Unsigned_32 (K)), False);
         --  An operand that is not a bit: the premise fails, so the
         --  lemma says nothing; its precondition excludes the case.
         L (0) (0) := X;
         Check ("G3 a non-bit fails the premise k =" & K'Image,
                not GW.All_Bits (L, K));
      end loop;
   end Test_G3;

   ----------------------------------------------------------------------
   --  The netlist and G4
   ----------------------------------------------------------------------

   function Padded (Msg : String; Blocks : Positive) return Byte_Array is
      R   : Byte_Array (0 .. 64 * Blocks - 1) := [others => 0];
      Len : constant Unsigned_64 := Unsigned_64 (Msg'Length) * 8;
   begin
      for I in Msg'Range loop
         R (I - Msg'First) := Character'Pos (Msg (I));
      end loop;
      R (Msg'Length) := 16#80#;
      for I in 0 .. 7 loop
         R (R'Last - I) := Unsigned_8 (Shift_Right (Len, 8 * I) and 16#FF#);
      end loop;
      return R;
   end Padded;

   procedure Blocks_Of (Label : String; Data : Byte_Array) is
      H : Sha256.State := Sha256.Initial_State;
      T : Sha256.Trace.Block_Trace;
   begin
      for B in 0 .. Data'Length / 64 - 1 loop
         declare
            Block : constant Bytes_64 := Data (64 * B .. 64 * B + 63);
         begin
            Check ("netlist " & Label & B'Image,
                   Block_Checks.Check_Netlist (H, Block));
            Check ("G4 honest " & Label & B'Image,
                   Block_Checks.Check_Gadget (H, Block));
            Sha256.Trace.Compress_Traced (H, Data, 64 * B, T);
         end;
      end loop;
   end Blocks_Of;

   procedure Mutations is
      H     : constant Sha256.State := Sha256.Initial_State;
      Data  : constant Byte_Array := Padded ("abc", 1);
      Block : constant Bytes_64 := Data;
      T     : Sha256.Trace.Block_Trace;
      H1    : Sha256.State := H;
      M     : Gadget.Message_Bits;
      H0    : Gadget.State_Bits;
      X, Y  : Gadget.Block_Witness;
   begin
      Sha256.Trace.Compress_Traced (H1, Data, 0, T);
      Block_Checks.Honest (H, Block, T, H1, M, H0, X);
      Y := X;
      Y.W (20) := Bits_Of (T.W (4) + 1);
      Check ("G4 mutated schedule word 20 fails its assertion",
             GW.Assertion (Gadget.Schedule_Words (M, Y, 20), 4, Y.W (20))
             /= Zero);
      Y := X;
      Y.E (10) := Bits_Of (T.E (10) + 1);
      Check ("G4 mutated e of round 10 fails its assertion",
             GW.Assertion (Gadget.E_Words (M, H0, Y, 10), 6, Y.E (10))
             /= Zero);
      Y := X;
      Y.A (30) := Bits_Of (T.A (30) + 1);
      Check ("G4 mutated a of round 30 fails its assertion",
             GW.Assertion (Gadget.A_Words (M, H0, Y, 30), 7, Y.A (30))
             /= Zero);
      Y := X;
      Y.H1 (3) := Bits_Of (H1 (3) + 1);
      Check ("G4 mutated word 3 of the new state fails its assertion",
             GW.Assertion (Gadget.H_Words (H0, Y, 3), 2, Y.H1 (3)) /= Zero);
      Check ("G4 mutated witness fails the block",
             not Gadget.Assertions_Hold (M, H0, Y));
   end Mutations;

   procedure Random_Blocks is
      H     : Sha256.State;
      Block : Bytes_64;
   begin
      for N in 1 .. 4 loop
         for J in Sha256.Word_Index loop
            H (J) := Random_Word;
         end loop;
         for I in Block'Range loop
            Block (I) := Unsigned_8 (Next and 16#FF#);
         end loop;
         Check ("netlist random block",
                Block_Checks.Check_Netlist (H, Block));
         Check ("G4 honest random block",
                Block_Checks.Check_Gadget (H, Block));
      end loop;
   end Random_Blocks;

begin
   if Argument_Count > 1 then
      Put_Line ("usage: gadgets_kat [lean_gf2_128.txt]");
      Set_Exit_Status (Failure);
      return;
   end if;
   Lean_Vectors
     (if Argument_Count = 1 then Argument (1)
      else "tests/vectors/lean_gf2_128.txt");
   Test_G1;
   Test_G3;
   Blocks_Of ("abc", Padded ("abc", 1));
   Blocks_Of ("448-bit",
              Padded ("abcdbcdecdefdefgefghfghighijhijk"
                      & "ijkljklmklmnlmnomnopnopq", 2));
   Random_Blocks;
   Mutations;
   Put_Line ("gadgets_kat:" & Passed'Image & " passed," & Failures'Image
             & " failed");
   if Failures > 0 then
      Set_Exit_Status (Failure);
   end if;
end Gadgets_KAT;
