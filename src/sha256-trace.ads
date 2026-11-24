--  Sha256.Trace: the compression function of SHA-256 with its trace,
--  for the witness of the hash circuit (ADR 0086).
--  Upstream's circuits/sha256/src/concrete.rs (derived) exposes, per
--  block, the 48 words w[16 .. 63] of the message schedule, the e and
--  the a of each of the 64 rounds and the state after the block;
--  circuits/sha256msg/src/concrete.rs pads a message to a fixed number
--  of blocks and compresses every block of the maximum, the zero
--  blocks after the message included (sha256_msg_derived), so that the
--  work does not depend on the length of the message.
--
--  Compress_Traced is Sha256.Compress with the words of the schedule
--  and of the rounds written out: the same statements over the same
--  round functions and constants, which the parent's private part
--  declares for both. The parent's own compression is untouched, so
--  the transcript's hashing pays nothing for the trace; that the two
--  agree is tested on every trace vector (the state after the last
--  block against Sha256.Digest), not proved.
--
--  Documentation: docs/guide/09-mdoc.md, Section 3.6.
--
--  Proof status (Silver = absence of run-time errors, Gold = proved
--  functional contracts).
--
--    Compress_Traced : Silver; the arithmetic is modular, nothing can
--                      fail. Gold on its final state: it is Compress
--                      of the state and the block. That it is FIPS
--                      180-4 is tested through the parent
--                      (tests/vectors/sha256.txt) and the trace against
--                      a Python transcription on upstream's test
--                      documents (mdoc_parse_kat).
--    Compress        : ghost, Gold against Compress_Spec, the steps of
--                      Section 6.2.2 written as functions at the level
--                      Proof_Only. That Compress_Spec is FIPS 180-4 is
--                      a reading of the section, tested through
--                      Compress_Traced (register row V1).
--    Pad_Message     : Gold on the layout of the padded buffer: the
--                      message, the byte 16#80#, zeros, the bit length
--                      big-endian at the end of block N_Blocks, zeros
--                      to the end.
--
--  Constant time: the compression has data-independent control flow
--  and memory access (ADR 0051), and a message is always compressed
--  over the circuit's maximum number of blocks by the caller. The
--  padding is NOT constant time: it copies the message and writes the
--  marker and the length where the message ends, so its work depends
--  on the message's length; ADR 0086 declares it outside the perimeter
--  with the parse, which has handled that length already.
--
--  Trusted: that the trace and its place in the hash witness are those
--  upstream's code specifies (register row R14); SHA-256 itself is
--  tested, not proved (V1).

pragma SPARK_Mode (On);

with Proof_Levels;

package Sha256.Trace is

   type Word_Array is array (Natural range <>) of Unsigned_32;
   subtype Schedule_Tail is Word_Array (0 .. 47);   --  w[16 .. 63]
   subtype Round_Words   is Word_Array (0 .. 63);

   --  The trace of one block: the schedule words 16 to 63, the e and
   --  the a after each round. The state after the block is the H of
   --  Compress_Traced.
   type Block_Trace is record
      W : Schedule_Tail := [others => 0];
      E : Round_Words := [others => 0];
      A : Round_Words := [others => 0];
   end record;

   --  FIPS 180-4 Section 6.2.2 on the 64 bytes of Data from First,
   --  into H, with the trace.
   procedure Compress_Traced
     (H     : in out State;
      Data  : Byte_Array;
      First : Natural;
      T     : out Block_Trace)
   with
     Global => null,
     Pre    => First >= Data'First and then Data'Last >= First
               and then Data'Last - First >= 63,
     Post   => H = Compress (H'Old, Data (First .. First + 63));

   --  FIPS 180-4 Section 6.2.2 as functions, for the proof only: word I
   --  of the message schedule of Block (step 1), the eight working
   --  variables a to h after I rounds from H, as a State (steps 2 and
   --  3), and the compression (step 4). At the level Proof_Only they
   --  are never compiled: the schedule's recursion would take
   --  exponential time if it were executed.
   subtype Round_Count is Natural range 0 .. 64;

   --  Word I of the block, big-endian: the first sixteen words of the
   --  schedule.
   function Block_Word (Block : Bytes_64; I : Natural) return Unsigned_32
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => I <= 15;

   function Schedule_Word (Block : Bytes_64; I : Natural) return Unsigned_32
   with
     Ghost              => Proof_Only,
     Global             => null,
     Pre                => I <= 63,
     Subprogram_Variant => (Decreases => I);

   function Rounds (H : State; Block : Bytes_64; I : Round_Count) return State
   with
     Ghost              => Proof_Only,
     Global             => null,
     Subprogram_Variant => (Decreases => I);

   function Compress_Spec (H : State; Block : Bytes_64) return State with
     Ghost  => Proof_Only,
     Global => null;

   --  FIPS 180-4 Section 6.2.2: the compression of one block as a
   --  function, the vocabulary of the relations of Mdoc_Relation (ADR
   --  0091). The same statements as Compress_Traced, over the same
   --  round functions and constants, without the trace. Ghost: the
   --  library never calls it.
   function Compress (H : State; Block : Bytes_64) return State with
     Ghost,
     Global => null,
     Post   => (Proof_Only => Compress'Result = Compress_Spec (H, Block));

   Max_Blocks : constant := 40;
   subtype Block_Count is Positive range 1 .. Max_Blocks;

   --  Whether a message of Len bytes fits Blocks blocks with its
   --  padding (the byte 16#80# and the eight bytes of length).
   function Fits (Len : Natural; Blocks : Block_Count) return Boolean is
     (Len <= 64 * Blocks - 9)
   with Global => null;

   --  The number of blocks the padded message occupies.
   function Blocks_Of (Len : Natural; Blocks : Block_Count) return Block_Count
   is ((Len + 9 + 63) / 64)
   with Global => null, Pre => Fits (Len, Blocks);

   --  The padding of Section 5.1.1 into a buffer of Blocks blocks: the
   --  message, 16#80#, zeros to eight bytes before the end of block
   --  N_Blocks, the bit length as eight big-endian bytes, then zeros
   --  to the end of the buffer (upstream's pad_sha256_message).
   procedure Pad_Message
     (Msg      : Byte_Array;
      Blocks   : Block_Count;
      Padded   : out Byte_Array;
      N_Blocks : out Block_Count)
   with
     Global => null,
     Pre    => Padded'First = 0 and then Padded'Length = 64 * Blocks
               and then Fits (Msg'Length, Blocks),
     Post   => N_Blocks = Blocks_Of (Msg'Length, Blocks)
               and then (for all I in 0 .. Msg'Length - 1 =>
                           Padded (I) = Msg (Msg'First + I))
               and then Padded (Msg'Length) = 16#80#
               and then (for all I in Msg'Length + 1 .. 64 * N_Blocks - 9 =>
                           Padded (I) = 0)
               and then (for all I in 0 .. 7 =>
                           Padded (64 * N_Blocks - 8 + I)
                           = Unsigned_8 (Shift_Right (Unsigned_64 (Msg'Length) * 8,
                                                      56 - 8 * I) and 16#FF#))
               and then (for all I in 64 * N_Blocks .. Padded'Last =>
                           Padded (I) = 0);

private

   function Block_Word (Block : Bytes_64; I : Natural) return Unsigned_32 is
     (Shift_Left (Unsigned_32 (Block (4 * I)), 24)
      or Shift_Left (Unsigned_32 (Block (4 * I + 1)), 16)
      or Shift_Left (Unsigned_32 (Block (4 * I + 2)), 8)
      or Unsigned_32 (Block (4 * I + 3)));

   function Schedule_Word (Block : Bytes_64; I : Natural) return Unsigned_32
   is
     (if I < 16 then Block_Word (Block, I)
      else
        Small_1 (Schedule_Word (Block, I - 2)) + Schedule_Word (Block, I - 7)
        + Small_0 (Schedule_Word (Block, I - 15))
        + Schedule_Word (Block, I - 16));

   --  Round R of step 3 on the working variables S (a to h as S (0) to
   --  S (7)).
   function Round_Step (S : State; Block : Bytes_64; R : Natural) return State
   is
     (declare
        T1 : constant Unsigned_32 :=
          S (7) + Sigma_1 (S (4)) + Ch (S (4), S (5), S (6))
          + K (Round_Index (R)) + Schedule_Word (Block, R);
        T2 : constant Unsigned_32 :=
          Sigma_0 (S (0)) + Maj (S (0), S (1), S (2));
      begin
        [T1 + T2, S (0), S (1), S (2), S (3) + T1, S (4), S (5), S (6)])
   with Ghost => Proof_Only, Global => null, Pre => R <= 63;

   function Rounds (H : State; Block : Bytes_64; I : Round_Count) return State
   is
     (if I = 0 then H
      else Round_Step (Rounds (H, Block, I - 1), Block, I - 1));

   function Compress_Spec (H : State; Block : Bytes_64) return State is
     ([for J in Word_Index => H (J) + Rounds (H, Block, 64) (J)]);

end Sha256.Trace;
