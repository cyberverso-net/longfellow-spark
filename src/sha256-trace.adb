pragma SPARK_Mode (On);

package body Sha256.Trace is

   --  The constants and the six functions are the parent's (its
   --  private part): this is Sha256.Compress with the words written out.

   procedure Compress_Traced
     (H     : in out State;
      Data  : Byte_Array;
      First : Natural;
      T     : out Block_Trace)
   is
      type Schedule is array (Round_Index) of Unsigned_32;
      --  Zeroed first so that flow analysis has it initialised; the
      --  loops below assign every word.
      W : Schedule := [others => 0];
      A, B, C, D, E, F, G, HH, T1, T2 : Unsigned_32;
      --  For the proof: the block as Compress_Spec takes it, and the
      --  state on entry.
      Blk : constant Bytes_64 := Data (First .. First + 63)
      with Ghost => Proof_Only;
      H0  : constant State := H with Ghost => Proof_Only;
   begin
      T := (W => [others => 0], E => [others => 0], A => [others => 0]);
      --  The first sixteen words are the block, big-endian, the rest
      --  the recurrence of Section 6.2.2 step 1.
      for I in Round_Index range 0 .. 15 loop
         pragma Loop_Optimize (No_Vector, Unroll);
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J in 0 .. I - 1 =>
                 W (J) = Block_Word (Blk, Natural (J))));
         W (I) :=
           Shift_Left (Unsigned_32 (Data (First + 4 * Natural (I))), 24)
           or Shift_Left (Unsigned_32 (Data (First + 4 * Natural (I) + 1)), 16)
           or Shift_Left (Unsigned_32 (Data (First + 4 * Natural (I) + 2)), 8)
           or Unsigned_32 (Data (First + 4 * Natural (I) + 3));
         pragma Assert
           (Proof_Only => W (I) = Block_Word (Blk, Natural (I)));
      end loop;
      pragma Assert
        (Proof_Only =>
           (for all J in Round_Index range 0 .. 15 =>
              W (J) = Schedule_Word (Blk, Natural (J))));
      for I in Round_Index range 16 .. 63 loop
         pragma Loop_Optimize (No_Vector, Unroll);
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J in 0 .. I - 1 =>
                 W (J) = Schedule_Word (Blk, Natural (J))));
         --  The four words the recurrence reads, by the invariant.
         pragma Assert
           (Proof_Only =>
              W (I - 2) = Schedule_Word (Blk, Natural (I) - 2)
              and then W (I - 7) = Schedule_Word (Blk, Natural (I) - 7)
              and then W (I - 15) = Schedule_Word (Blk, Natural (I) - 15)
              and then W (I - 16) = Schedule_Word (Blk, Natural (I) - 16));
         W (I) :=
           Small_1 (W (I - 2)) + W (I - 7) + Small_0 (W (I - 15)) + W (I - 16);
         pragma Assert
           (Proof_Only => W (I) = Schedule_Word (Blk, Natural (I)));
         T.W (Natural (I) - 16) := W (I);
      end loop;

      A  := H (0);
      B  := H (1);
      C  := H (2);
      D  := H (3);
      E  := H (4);
      F  := H (5);
      G  := H (6);
      HH := H (7);

      for I in Round_Index loop
         pragma Loop_Optimize (No_Vector, Unroll);
         pragma Loop_Invariant
           (Proof_Only =>
              A = Rounds (H0, Blk, Natural (I)) (0)
              and then B = Rounds (H0, Blk, Natural (I)) (1)
              and then C = Rounds (H0, Blk, Natural (I)) (2)
              and then D = Rounds (H0, Blk, Natural (I)) (3)
              and then E = Rounds (H0, Blk, Natural (I)) (4)
              and then F = Rounds (H0, Blk, Natural (I)) (5)
              and then G = Rounds (H0, Blk, Natural (I)) (6)
              and then HH = Rounds (H0, Blk, Natural (I)) (7));
         T1 := HH + Sigma_1 (E) + Ch (E, F, G) + K (I) + W (I);
         T2 := Sigma_0 (A) + Maj (A, B, C);
         HH := G;
         G  := F;
         F  := E;
         E  := D + T1;
         D  := C;
         C  := B;
         B  := A;
         A  := T1 + T2;
         T.E (Natural (I)) := E;
         T.A (Natural (I)) := A;
      end loop;
      pragma Assert
        (Proof_Only =>
           A = Rounds (H0, Blk, 64) (0) and then B = Rounds (H0, Blk, 64) (1)
           and then C = Rounds (H0, Blk, 64) (2)
           and then D = Rounds (H0, Blk, 64) (3)
           and then E = Rounds (H0, Blk, 64) (4)
           and then F = Rounds (H0, Blk, 64) (5)
           and then G = Rounds (H0, Blk, 64) (6)
           and then HH = Rounds (H0, Blk, 64) (7));

      H (0) := H (0) + A;
      H (1) := H (1) + B;
      H (2) := H (2) + C;
      H (3) := H (3) + D;
      H (4) := H (4) + E;
      H (5) := H (5) + F;
      H (6) := H (6) + G;
      H (7) := H (7) + HH;
      pragma Assert
        (Proof_Only =>
           (for all J in Word_Index =>
              H (J) = H0 (J) + Rounds (H0, Blk, 64) (J)));
      pragma Assert (Proof_Only => H = Compress_Spec (H0, Blk));
   end Compress_Traced;

   --  The statements of Compress_Traced without the trace, with the
   --  same invariants.
   function Compress (H : State; Block : Bytes_64) return State is
      type Schedule is array (Round_Index) of Unsigned_32;
      W : Schedule := [others => 0];
      A, B, C, D, E, F, G, HH, T1, T2 : Unsigned_32;
      R : State := H;
   begin
      for I in Round_Index range 0 .. 15 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J in 0 .. I - 1 =>
                 W (J) = Block_Word (Block, Natural (J))));
         W (I) :=
           Shift_Left (Unsigned_32 (Block (4 * Natural (I))), 24)
           or Shift_Left (Unsigned_32 (Block (4 * Natural (I) + 1)), 16)
           or Shift_Left (Unsigned_32 (Block (4 * Natural (I) + 2)), 8)
           or Unsigned_32 (Block (4 * Natural (I) + 3));
         pragma Assert
           (Proof_Only => W (I) = Block_Word (Block, Natural (I)));
      end loop;
      pragma Assert
        (Proof_Only =>
           (for all J in Round_Index range 0 .. 15 =>
              W (J) = Schedule_Word (Block, Natural (J))));
      for I in Round_Index range 16 .. 63 loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J in 0 .. I - 1 =>
                 W (J) = Schedule_Word (Block, Natural (J))));
         --  The four words the recurrence reads, by the invariant.
         pragma Assert
           (Proof_Only =>
              W (I - 2) = Schedule_Word (Block, Natural (I) - 2)
              and then W (I - 7) = Schedule_Word (Block, Natural (I) - 7)
              and then W (I - 15) = Schedule_Word (Block, Natural (I) - 15)
              and then W (I - 16) = Schedule_Word (Block, Natural (I) - 16));
         W (I) :=
           Small_1 (W (I - 2)) + W (I - 7) + Small_0 (W (I - 15)) + W (I - 16);
         pragma Assert
           (Proof_Only => W (I) = Schedule_Word (Block, Natural (I)));
      end loop;

      A  := H (0);
      B  := H (1);
      C  := H (2);
      D  := H (3);
      E  := H (4);
      F  := H (5);
      G  := H (6);
      HH := H (7);

      for I in Round_Index loop
         pragma Loop_Invariant
           (Proof_Only =>
              A = Rounds (H, Block, Natural (I)) (0)
              and then B = Rounds (H, Block, Natural (I)) (1)
              and then C = Rounds (H, Block, Natural (I)) (2)
              and then D = Rounds (H, Block, Natural (I)) (3)
              and then E = Rounds (H, Block, Natural (I)) (4)
              and then F = Rounds (H, Block, Natural (I)) (5)
              and then G = Rounds (H, Block, Natural (I)) (6)
              and then HH = Rounds (H, Block, Natural (I)) (7));
         T1 := HH + Sigma_1 (E) + Ch (E, F, G) + K (I) + W (I);
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
      pragma Assert
        (Proof_Only =>
           A = Rounds (H, Block, 64) (0) and then B = Rounds (H, Block, 64) (1)
           and then C = Rounds (H, Block, 64) (2)
           and then D = Rounds (H, Block, 64) (3)
           and then E = Rounds (H, Block, 64) (4)
           and then F = Rounds (H, Block, 64) (5)
           and then G = Rounds (H, Block, 64) (6)
           and then HH = Rounds (H, Block, 64) (7));

      R (0) := R (0) + A;
      R (1) := R (1) + B;
      R (2) := R (2) + C;
      R (3) := R (3) + D;
      R (4) := R (4) + E;
      R (5) := R (5) + F;
      R (6) := R (6) + G;
      R (7) := R (7) + HH;
      pragma Assert
        (Proof_Only =>
           (for all J in Word_Index =>
              R (J) = H (J) + Rounds (H, Block, 64) (J)));
      return R;
   end Compress;

   procedure Pad_Message
     (Msg      : Byte_Array;
      Blocks   : Block_Count;
      Padded   : out Byte_Array;
      N_Blocks : out Block_Count)
   is
      Len  : constant Natural := Msg'Length;
      Bits : constant Unsigned_64 := Unsigned_64 (Len) * 8;
      Tail : Natural;
   begin
      N_Blocks := Blocks_Of (Len, Blocks);
      Padded := [others => 0];
      for I in 0 .. Len - 1 loop
         pragma Loop_Invariant
           (for all J in 0 .. I - 1 => Padded (J) = Msg (Msg'First + J));
         pragma Loop_Invariant
           (for all J in I .. Padded'Last => Padded (J) = 0);
         Padded (I) := Msg (Msg'First + I);
      end loop;
      Padded (Len) := 16#80#;
      --  The length, big-endian, in the last eight bytes of block
      --  N_Blocks; the zeros between were placed above.
      Tail := 64 * N_Blocks - 8;
      for I in 0 .. 7 loop
         pragma Loop_Invariant
           (for all J in 0 .. Len - 1 => Padded (J) = Msg (Msg'First + J));
         pragma Loop_Invariant (Padded (Len) = 16#80#);
         pragma Loop_Invariant
           (for all J in Len + 1 .. Tail - 1 => Padded (J) = 0);
         pragma Loop_Invariant
           (for all J in Tail + 8 .. Padded'Last => Padded (J) = 0);
         pragma Loop_Invariant
           (for all J in 0 .. I - 1 =>
              Padded (Tail + J)
              = Unsigned_8 (Shift_Right (Bits, 56 - 8 * J) and 16#FF#));
         Padded (Tail + I) :=
           Unsigned_8 (Shift_Right (Bits, 56 - 8 * I) and 16#FF#);
      end loop;
   end Pad_Message;

end Sha256.Trace;
