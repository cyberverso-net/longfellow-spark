pragma SPARK_Mode (On);

with Sha256;
with Aes256;

package body Transcript with
  Refined_State =>
    (State => (Hash, Live, Exhausted, Schedule, Counter, Buffer, Avail))
is

   --  FsPrf refuses to go past 2^40 blocks (ADR 0028).
   Max_Blocks : constant := 2**40;
   subtype Block_Count is Unsigned_64 range 0 .. Max_Blocks;

   Hash      : Sha256.Context := Sha256.Initial;
   Live      : Boolean := False;
   Exhausted : Boolean := False;
   --  The generator: key schedule of the current seed, the next block
   --  number, the current block and how many of its bytes are unread.
   Schedule  : Aes256.Key_Schedule := Aes256.Expand_Key ([others => 0]);
   Counter   : Block_Count := 0;
   Buffer    : Bytes_16 := [others => 0];
   Avail     : Natural range 0 .. 16 := 0;

   function Generator_Live return Boolean is (Live);

   function Is_Exhausted return Boolean is (Exhausted);

   function Length_Bytes (N : Unsigned_64) return Bytes_8 is
     [0 => Unsigned_8 (N mod 256),
      1 => Unsigned_8 (Shift_Right (N, 8) mod 256),
      2 => Unsigned_8 (Shift_Right (N, 16) mod 256),
      3 => Unsigned_8 (Shift_Right (N, 24) mod 256),
      4 => Unsigned_8 (Shift_Right (N, 32) mod 256),
      5 => Unsigned_8 (Shift_Right (N, 40) mod 256),
      6 => Unsigned_8 (Shift_Right (N, 48) mod 256),
      7 => Unsigned_8 (Shift_Right (N, 56) mod 256)];

   ----------------------------------------------------------------------
   --  The two points where bytes reach SHA-256 and the model
   ----------------------------------------------------------------------

   --  write_untyped of the reference: the bytes go to the accumulator
   --  and to the model. The writes below discard the generator first.
   procedure Absorb (D : Byte_Array) with
     Global => (In_Out => (Hash, Absorbed)),
     Post   =>
       (SPARKlib_Full =>
          Byte_Seqs.Logical_Eq (Absorbed, Append (Absorbed'Old, D)))
   is
   begin
      Sha256.Update (Hash, D);
      Absorbed := Append (Absorbed, D);
   end Absorb;

   procedure Absorb_Byte (B : Unsigned_8) with
     Global => (In_Out => (Hash, Absorbed)),
     Post   =>
       (SPARKlib_Full =>
          Byte_Seqs.Logical_Eq (Absorbed, Byte_Seqs.Add (Absorbed'Old, B)))
   is
   begin
      Sha256.Update (Hash, [B]);
      Absorbed := Byte_Seqs.Add (Absorbed, B);
   end Absorb_Byte;

   ----------------------------------------------------------------------
   --  Absorb
   ----------------------------------------------------------------------

   procedure Reset (Label : Byte_Array) is
   begin
      Hash      := Sha256.Initial;
      Live      := False;
      Exhausted := False;
      Counter   := 0;
      Buffer    := [others => 0];
      Avail     := 0;
      Absorbed  := Byte_Seqs.Empty_Sequence;
      Write_Bytes (Label);
   end Reset;

   procedure Write_Bytes (D : Byte_Array) is
   begin
      Live := False;
      Absorb_Byte (0);
      Absorb (Length_Bytes (Unsigned_64 (D'Length)));
      Absorb (D);
   end Write_Bytes;

   procedure Write0 (N : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Add_Zeros);
      Base : Byte_Seq with Ghost => SPARKlib_Full;
   begin
      Live := False;
      Absorb_Byte (0);
      Absorb (Length_Bytes (Unsigned_64 (N)));
      Base := Absorbed;
      --  One zero byte at a time: the accumulator works byte by byte
      --  anyway, and the model follows Add_Zeros step by step.
      for I in 1 .. N loop
         Absorb_Byte (0);
         pragma Loop_Invariant
           (SPARKlib_Full =>
              Byte_Seqs.Logical_Eq (Absorbed, Add_Zeros (Base, I)));
      end loop;
   end Write0;

   procedure Write_Element (E : Byte_Array) is
   begin
      Live := False;
      Absorb_Byte (1);
      Absorb (E);
   end Write_Element;

   procedure Write_Slice (Count : Natural; E : Byte_Array) is
   begin
      Live := False;
      Absorb_Byte (2);
      Absorb (Length_Bytes (Unsigned_64 (Count)));
      Absorb (E);
   end Write_Slice;

   ----------------------------------------------------------------------
   --  Squeeze
   ----------------------------------------------------------------------

   --  The next block of the keystream: AES-256 of the 16-byte little-
   --  endian counter under the seed (Section 3.1.1), or zeros once the
   --  counter has reached the bound, which also raises Exhausted.
   procedure Refill with
     Global => (In_Out => (Counter, Exhausted), Input => Schedule,
                Output => (Buffer, Avail)),
     Post   => Exhausted'Old <= Exhausted and then Avail = 16
   is
   begin
      if Counter = Max_Blocks then
         Exhausted := True;
         Buffer    := [others => 0];
      else
         Buffer  :=
           Aes256.Encrypt (Schedule, Length_Bytes (Counter) & [1 .. 8 => 0]);
         Counter := Counter + 1;
      end if;
      Avail := 16;
   end Refill;

   procedure Get_Random_Bytes (D : out Byte_Array) is
   begin
      if not Live then
         Schedule := Aes256.Expand_Key (Sha256.Digest (Hash));
         Counter  := 0;
         Avail    := 0;
         Live     := True;
      end if;
      for I in D'Range loop
         if Avail = 0 then
            Refill;
         end if;
         D (I)  := Buffer (16 - Avail);
         Avail  := Avail - 1;
         pragma Loop_Invariant (Live);
         pragma Loop_Invariant (Exhausted'Loop_Entry <= Exhausted);
      end loop;
   end Get_Random_Bytes;

   --  The smallest all-ones value covering N (Section 3.4.1):
   --  2^bitlen (N) - 1, so that (N and Mask) = N and N > Mask / 2.
   function Mask_Of (N : Unsigned_64) return Unsigned_64 with
     Global => null,
     Pre    => N in 1 .. 2**31 - 1,
     Post   =>
       Mask_Of'Result < 2**32
       and then (N and Mask_Of'Result) = N
       and then N > Mask_Of'Result / 2
   is
      Mask : Unsigned_64 := 0;
   begin
      while (N and Mask) /= N loop
         pragma Loop_Invariant (Mask < 2**31);
         pragma Loop_Invariant (((Mask + 1) and Mask) = 0);
         pragma Loop_Invariant (Mask = 0 or else (N and Mask / 2) /= N);
         pragma Loop_Variant (Increases => Mask);
         Mask := Mask * 2 + 1;
      end loop;
      return Mask;
   end Mask_Of;

   --  The little-endian value of at most eight bytes.
   function LE_Value (B : Byte_Array) return Unsigned_64 with
     Global => null,
     Pre    => B'Length <= 8
   is
      V : Unsigned_64 := 0;
   begin
      for I in reverse B'Range loop
         V := V * 256 + Unsigned_64 (B (I));
      end loop;
      return V;
   end LE_Value;

   procedure Nat (N : Positive; R : out Natural) is
      --  l of Section 3.4.1: the byte length of N (N < 2^31, so at
      --  most four); written as a comparison rather than the
      --  reference's shift loop, with the same value.
      L    : constant Positive :=
        (if N < 2**8 then 1 elsif N < 2**16 then 2 elsif N < 2**24 then 3
         else 4);
      NN   : constant Unsigned_64 := Unsigned_64 (N);
      Mask : constant Unsigned_64 := Mask_Of (NN);
      B    : Byte_Array (0 .. L - 1);
      V    : Unsigned_64;
   begin
      --  Draw l bytes, read little-endian, mask, accept below N. Each
      --  attempt consumes fresh bytes; the number of attempts is not
      --  bounded (ADR 0030).
      loop
         pragma Loop_Invariant (Exhausted'Loop_Entry <= Exhausted);
         Get_Random_Bytes (B);
         V := LE_Value (B) and Mask;
         exit when V < NN;
      end loop;
      R := Natural (V);
   end Nat;

   --  The draw predicate Fisher_Yates.Draws_Below is opaque here (its
   --  body is hidden): the loop below reasons with Record_Draw's
   --  contract only.
   procedure Choose (N, K : Natural; R : out Index_Array) is
      V : Index_Array (0 .. K - 1) := [others => 0];
      X : Natural;
   begin
      Fisher_Yates.Lemma_Draws_Below_Empty (V, N);
      for I in V'Range loop
         Nat (N - I, X);
         Fisher_Yates.Record_Draw (V, N, I, X);
         pragma Loop_Invariant (Exhausted'Loop_Entry <= Exhausted);
         pragma Loop_Invariant (Fisher_Yates.Draws_Below (V, N, I));
      end loop;
      Fisher_Yates.Choose (N, V, R);
   end Choose;

end Transcript;
