pragma SPARK_Mode (On);

--  Sha256.Trace.Netlist: the reference netlist of SHA-256's compression
--  of one block (ADR 0091, piece 2; chapter 10, Section 2), the list of
--  named values the gadget FlatSHA256Circuit::assert_transform_block of
--  upstream's generator asserts (lib/circuits/sha/flatsha256_circuit.h
--  at 0d92f80c, lines 91 to 150).
--
--  Each value is one operation on earlier values: an input word (the
--  state H0 before the block, a word of the block), one of the round
--  functions of FIPS 180-4 Section 4.1.2 (Sigma_0, Sigma_1, Small_0,
--  Small_1, Ch, Maj), or a sum modulo 2^32 of up to six earlier values
--  and a constant. The grouping is the gadget's: one sum per assertion
--  of the circuit (a schedule word is a sum of four words, the new e of
--  six, the new a of seven, a word of the new state of two), so that
--  the checker of the later blocks matches one value to one assertion.
--  The working variables b, c, d, f, g and h are not values: they are
--  the a and e of earlier rounds, or words of H0 (Var).
--
--  560 values: H0 (0 .. 7), the block's words (8 .. 23), three values
--  per schedule word 16 to 63 (24 .. 167), six per round (168 .. 551),
--  the new state (552 .. 559). Def gives the definition of value I as
--  a function of I alone: the generator is that function, and Generate
--  the list it gives.
--
--  Proved (Gold): Interpret, the evaluation of the list in order,
--  returns as its last eight values the compression of FIPS 180-4,
--  Compress_Spec (H0, Block), and every other value is the word of the
--  specification it names (the schedule word, the e and the a after
--  each round); Lemma_Holds_Unique, any assignment of the 560 values
--  that satisfies every definition is Interpret's. Tested
--  (netlist_kat): Interpret against the library's Sha256 on the NIST
--  vectors and on every block of the test documents, and its named
--  values against Compress_Traced's trace. Trusted: nothing beyond the
--  proof tools.
--
--  Linked into the library archive with every unit of src/, and named
--  by no unit of the library: no program links it unless it names it.
--  It is executable for its tests and for the checker of the later
--  blocks, which reads the definitions.

with Proof_Levels;

package Sha256.Trace.Netlist is

   Value_Count : constant := 560;
   subtype Value_Index is Natural range 0 .. Value_Count - 1;

   --  The regions of the list.
   First_Message  : constant := 8;
   First_Schedule : constant := 24;
   First_Round    : constant := 168;
   First_Output   : constant := 552;

   type Op_Kind is
     (Op_State,        --  word J of H0, J = I
      Op_Message,      --  word I - 8 of the block, big-endian
      Op_Sigma_0, Op_Sigma_1, Op_Small_0, Op_Small_1,  --  of Args (1)
      Op_Ch, Op_Maj,   --  of Args (1 .. 3)
      Op_Add);         --  Args (1 .. N) and C, modulo 2^32

   subtype Arg_Count is Natural range 0 .. 6;
   type Arg_Array is array (1 .. 6) of Value_Index;

   type Value_Def is record
      Op   : Op_Kind;
      N    : Arg_Count;
      Args : Arg_Array;
      C    : Unsigned_32;
   end record;

   type Netlist is array (Value_Index) of Value_Def;
   type Values is array (Value_Index) of Unsigned_32;

   ----------------------------------------------------------------------
   --  The indices of the named values
   ----------------------------------------------------------------------

   subtype Schedule_Step is Natural range 16 .. 63;
   subtype Round is Natural range 0 .. 63;
   subtype Round_Or_End is Natural range 0 .. 64;

   --  Small_0 (w (I - 15)), Small_1 (w (I - 2)) and w (I) of step I.
   function S0_Ix (I : Schedule_Step) return Value_Index is
     (First_Schedule + 3 * (I - 16));
   function S1_Ix (I : Schedule_Step) return Value_Index is
     (First_Schedule + 3 * (I - 16) + 1);

   --  Schedule word I: a word of the block for I below 16.
   function W_Ix (I : Round) return Value_Index is
     (if I < 16 then First_Message + I
      else First_Schedule + 3 * (I - 16) + 2);

   --  Sigma_1 (e), Ch (e, f, g), Sigma_0 (a), Maj (a, b, c), the new e
   --  and the new a of round T.
   function Sg1_Ix (T : Round) return Value_Index is (First_Round + 6 * T);
   function Ch_Ix (T : Round) return Value_Index is (First_Round + 6 * T + 1);
   function Sg0_Ix (T : Round) return Value_Index is (First_Round + 6 * T + 2);
   function Mj_Ix (T : Round) return Value_Index is (First_Round + 6 * T + 3);
   function E_Ix (T : Round) return Value_Index is (First_Round + 6 * T + 4);
   function A_Ix (T : Round) return Value_Index is (First_Round + 6 * T + 5);

   --  The value that holds working variable P (a to h as 0 to 7) before
   --  round T: the a (or e) of round T - 1 - P (or T - 1 - (P - 4)), or
   --  a word of H0 in the first rounds.
   function Var (T : Round_Or_End; P : Sha256.Word_Index) return Value_Index is
     (if P <= 3 then
        (if T > Natural (P) then A_Ix (T - 1 - Natural (P))
         else Natural (P) - T)
      else
        (if T > Natural (P) - 4 then E_Ix (T - 1 - (Natural (P) - 4))
         else 4 + (Natural (P) - 4) - T));

   ----------------------------------------------------------------------
   --  The generator
   ----------------------------------------------------------------------

   --  The definition of value I.
   function Def (I : Value_Index) return Value_Def;

   --  Every argument of a definition is an earlier value.
   function Args_Earlier (D : Value_Def; I : Value_Index) return Boolean is
     (for all K in 1 .. D.N => D.Args (K) < I);

   function Generate return Netlist with
     Global => null,
     Post   => (for all I in Value_Index =>
                  Generate'Result (I) = Def (I)
                  and then Args_Earlier (Def (I), I));

   ----------------------------------------------------------------------
   --  The interpretation
   ----------------------------------------------------------------------

   --  Word I of the block, big-endian.
   function Message_Word (Block : Bytes_64; I : Natural) return Unsigned_32 is
     (Shift_Left (Unsigned_32 (Block (4 * I)), 24)
      or Shift_Left (Unsigned_32 (Block (4 * I + 1)), 16)
      or Shift_Left (Unsigned_32 (Block (4 * I + 2)), 8)
      or Unsigned_32 (Block (4 * I + 3)))
   with Pre => I <= 15;

   --  The value of definition D over the values V before it.
   function Eval
     (D : Value_Def; V : Values; H0 : Sha256.State; Block : Bytes_64;
      I : Value_Index) return Unsigned_32;

   --  Every value equals its definition over the values before it.
   function Holds
     (V : Values; H0 : Sha256.State; Block : Bytes_64) return Boolean
   is
     (for all I in Value_Index => V (I) = Eval (Def (I), V, H0, Block, I));

   --  The specification's word that value I names.
   function Expected
     (H0 : Sha256.State; Block : Bytes_64; I : Value_Index) return Unsigned_32
   with Ghost => Proof_Only, Global => null;

   --  The list evaluated in order.
   function Interpret (H0 : Sha256.State; Block : Bytes_64) return Values with
     Global => null,
     Post   =>
       (Runtime    => Holds (Interpret'Result, H0, Block),
        Proof_Only =>
          (for all I in Value_Index =>
             Interpret'Result (I) = Expected (H0, Block, I))
          and then
          (for all J in Sha256.Word_Index =>
             Interpret'Result (First_Output + Natural (J))
             = Compress_Spec (H0, Block) (J)));

   --  The state after the block, the last eight values.
   function Output (V : Values) return Sha256.State is
     ([for J in Sha256.Word_Index => V (First_Output + Natural (J))]);

   --  Any assignment that satisfies every definition is Interpret's.
   procedure Lemma_Holds_Unique
     (V : Values; H0 : Sha256.State; Block : Bytes_64)
   with
     Ghost,
     Global => null,
     Pre    => Holds (V, H0, Block),
     Post   => V = Interpret (H0, Block);

private

   function Def (I : Value_Index) return Value_Def is
     (if I < First_Message then (Op_State, 0, [others => 0], 0)
      elsif I < First_Schedule then (Op_Message, 0, [others => 0], 0)
      elsif I < First_Round then
        (declare
           S : constant Schedule_Step := 16 + (I - First_Schedule) / 3;
         begin
           (case (I - First_Schedule) mod 3 is
              when 0 => (Op_Small_0, 1, [W_Ix (S - 15), others => 0], 0),
              when 1 => (Op_Small_1, 1, [W_Ix (S - 2), others => 0], 0),
              when others =>
                (Op_Add, 4,
                 [S1_Ix (S), W_Ix (S - 7), S0_Ix (S), W_Ix (S - 16),
                  others => 0], 0)))
      elsif I < First_Output then
        (declare
           T : constant Round := (I - First_Round) / 6;
         begin
           (case (I - First_Round) mod 6 is
              when 0 => (Op_Sigma_1, 1, [Var (T, 4), others => 0], 0),
              when 1 =>
                (Op_Ch, 3,
                 [Var (T, 4), Var (T, 5), Var (T, 6), others => 0], 0),
              when 2 => (Op_Sigma_0, 1, [Var (T, 0), others => 0], 0),
              when 3 =>
                (Op_Maj, 3,
                 [Var (T, 0), Var (T, 1), Var (T, 2), others => 0], 0),
              when 4 =>
                (Op_Add, 5,
                 [Var (T, 3), Var (T, 7), Sg1_Ix (T), Ch_Ix (T), W_Ix (T),
                  others => 0], K (Round_Index (T))),
              when others =>
                (Op_Add, 6,
                 [Var (T, 7), Sg1_Ix (T), Ch_Ix (T), W_Ix (T), Sg0_Ix (T),
                  Mj_Ix (T)], K (Round_Index (T)))))
      else
        (Op_Add, 2,
         [I - First_Output,
          Var (64, Sha256.Word_Index (I - First_Output)), others => 0], 0));

   --  Argument K of D, or zero when K is past D.N.
   function Arg (D : Value_Def; V : Values; K : Positive) return Unsigned_32 is
     (if K <= D.N then V (D.Args (K)) else 0)
   with Pre => K <= 6;

   function Eval
     (D : Value_Def; V : Values; H0 : Sha256.State; Block : Bytes_64;
      I : Value_Index) return Unsigned_32
   is
     (case D.Op is
        when Op_State =>
          (if I < First_Message then H0 (Sha256.Word_Index (I)) else 0),
        when Op_Message =>
          (if I in First_Message .. First_Schedule - 1
           then Message_Word (Block, I - First_Message) else 0),
        when Op_Sigma_0 => Sigma_0 (Arg (D, V, 1)),
        when Op_Sigma_1 => Sigma_1 (Arg (D, V, 1)),
        when Op_Small_0 => Small_0 (Arg (D, V, 1)),
        when Op_Small_1 => Small_1 (Arg (D, V, 1)),
        when Op_Ch      => Ch (Arg (D, V, 1), Arg (D, V, 2), Arg (D, V, 3)),
        when Op_Maj     => Maj (Arg (D, V, 1), Arg (D, V, 2), Arg (D, V, 3)),
        when Op_Add     =>
          Arg (D, V, 1) + Arg (D, V, 2) + Arg (D, V, 3) + Arg (D, V, 4)
          + Arg (D, V, 5) + Arg (D, V, 6) + D.C);

   function Expected
     (H0 : Sha256.State; Block : Bytes_64; I : Value_Index) return Unsigned_32
   is
     (if I < First_Message then H0 (Sha256.Word_Index (I))
      elsif I < First_Schedule then Block_Word (Block, I - First_Message)
      elsif I < First_Round then
        (declare
           S : constant Natural := 16 + (I - First_Schedule) / 3;
         begin
           (case (I - First_Schedule) mod 3 is
              when 0      => Small_0 (Schedule_Word (Block, S - 15)),
              when 1      => Small_1 (Schedule_Word (Block, S - 2)),
              when others => Schedule_Word (Block, S)))
      elsif I < First_Output then
        (declare
           T : constant Natural := (I - First_Round) / 6;
           R : constant Sha256.State := Rounds (H0, Block, T);
         begin
           (case (I - First_Round) mod 6 is
              when 0      => Sigma_1 (R (4)),
              when 1      => Ch (R (4), R (5), R (6)),
              when 2      => Sigma_0 (R (0)),
              when 3      => Maj (R (0), R (1), R (2)),
              when 4      => Rounds (H0, Block, T + 1) (4),
              when others => Rounds (H0, Block, T + 1) (0)))
      else Compress_Spec (H0, Block) (Sha256.Word_Index (I - First_Output)));

end Sha256.Trace.Netlist;
