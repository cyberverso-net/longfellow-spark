pragma SPARK_Mode (On);

--  Sha256.Trace.Netlist.Gadget: G4, the assertions of one block of
--  SHA-256's compression in upstream's circuit (ADR 0091, piece 2;
--  chapter 10, Section 2), the model of
--  FlatSHA256Circuit::assert_transform_block
--  (lib/circuits/sha/flatsha256_circuit.h at 0d92f80c, lines 91 to 150).
--
--  The circuit holds each word as 32 bits, field elements. The words of
--  the block and the state before it come from the message and from the
--  previous block; the witness gives the schedule words 16 to 63, the e
--  and the a after each round and the state after the block (in the
--  packed form, whose outputs are bits by G1, Gadgets.Bits). The round
--  functions are bit forms over the field (logic.h): xor is the sum,
--  not x is 1 + x, and is the product, so that
--    Ch  = x y + (1 + x) z,      Maj = x y + (x + y) z,
--  and the rotations and shifts select bits, with zeros shifted in. Each
--  sum modulo 2^32 is one assertion of G3 (Gadgets.Words): four words
--  for a schedule word, six for the new e (h, Sigma_1 (e), Ch, K_t, w_t
--  and d), seven for the new a (the five of T1, Sigma_0 (a), Maj) and
--  two for a word of the new state. The model takes each product of
--  elements in a row, in the order the generator lists the words; the
--  generator groups T1 = h Sigma_1 Ch K w first, the same element by
--  the laws of the product.
--
--  The theorem (Lemma_Block): when every word of the witness is bits and
--  every assertion of the block holds, the values the witness decodes to
--  satisfy every definition of the netlist (Holds), so the state after
--  the block is Compress_Spec (H0, Block), FIPS 180-4's compression.
--
--  Proved (Gold over Lean lemmas): Lemma_Block, and the lemmas of the
--  bit forms below it (Gold). It uses Gadgets.Words.Lemma_Assert_Eqmod,
--  proved in Lean and bridged by reading (register row L4). Tested
--  (gadgets_kat): the assertions on the honest trace of every block
--  tried hold, and a mutated word makes the matching one fail.
--
--  A child of Sha256.Trace.Netlist, not a unit Gadgets.Sha256, so that
--  its body sees the round functions of Sha256 and the definitions of
--  the netlist, both private. Linked into the library archive with every
--  unit of src/, and named by no unit of the library. Public data only,
--  as for Gadgets.

with GF2_128;
with Gadgets;       use Gadgets;
with Gadgets.Words;

package Sha256.Trace.Netlist.Gadget is

   use type GF2_128.Element;
   function Add (A, B : Element) return Element renames GF2_128.Add;
   function Mul (A, B : Element) return Element renames GF2_128.Mul;
   One  : Element renames GF2_128.One;
   Zero : Element renames GF2_128.Zero;

   ----------------------------------------------------------------------
   --  The bit forms (logic.h 268 to 316, 860 to 900)
   ----------------------------------------------------------------------

   function Xor3 (A, B, C : Element) return Element is (Add (Add (A, B), C));

   function Not_Bit (A : Element) return Element is (Add (One, A));

   function Ch_Bit (A, B, C : Element) return Element is
     (Add (Mul (A, B), Mul (Not_Bit (A), C)));

   function Maj_Bit (A, B, C : Element) return Element is
     (Add (Mul (A, B), Mul (Add (A, B), C)));

   --  Bit I of the rotation right by R, and of the shift right by S.
   function Rotr (W : Word_Bits; R, I : Bit_Index) return Element is
     (W ((I + R) mod 32));

   function Shr (W : Word_Bits; S, I : Bit_Index) return Element is
     (if I + S < 32 then W (I + S) else Zero);

   function Sigma_0_Form (W : Word_Bits) return Word_Bits is
     [for I in Bit_Index =>
        Xor3 (Rotr (W, 2, I), Rotr (W, 13, I), Rotr (W, 22, I))];

   function Sigma_1_Form (W : Word_Bits) return Word_Bits is
     [for I in Bit_Index =>
        Xor3 (Rotr (W, 6, I), Rotr (W, 11, I), Rotr (W, 25, I))];

   function Small_0_Form (W : Word_Bits) return Word_Bits is
     [for I in Bit_Index =>
        Xor3 (Rotr (W, 7, I), Rotr (W, 18, I), Shr (W, 3, I))];

   function Small_1_Form (W : Word_Bits) return Word_Bits is
     [for I in Bit_Index =>
        Xor3 (Rotr (W, 17, I), Rotr (W, 19, I), Shr (W, 10, I))];

   function Ch_Form (X, Y, Z : Word_Bits) return Word_Bits is
     [for I in Bit_Index => Ch_Bit (X (I), Y (I), Z (I))];

   function Maj_Form (X, Y, Z : Word_Bits) return Word_Bits is
     [for I in Bit_Index => Maj_Bit (X (I), Y (I), Z (I))];

   ----------------------------------------------------------------------
   --  The words of one block
   ----------------------------------------------------------------------

   type Message_Bits is array (0 .. 15) of Word_Bits;
   type State_Bits is array (Sha256.Word_Index) of Word_Bits;
   type Schedule_Bits is array (Schedule_Step) of Word_Bits;
   type Round_Bits is array (Round) of Word_Bits;

   --  The witness of one block, its words unpacked.
   type Block_Witness is record
      W  : Schedule_Bits;  --  the schedule words 16 to 63
      E  : Round_Bits;     --  the e after each round
      A  : Round_Bits;     --  the a after each round
      H1 : State_Bits;     --  the state after the block
   end record;

   function Witness_Bits (X : Block_Witness) return Boolean is
     ((for all I in Schedule_Step => All_Bits (X.W (I)))
      and then (for all T in Round =>
                  All_Bits (X.E (T)) and then All_Bits (X.A (T)))
      and then (for all J in Sha256.Word_Index => All_Bits (X.H1 (J))));

   --  Schedule word I.
   function W_Bits
     (M : Message_Bits; X : Block_Witness; I : Round) return Word_Bits
   is (if I < 16 then M (I) else X.W (I));

   --  Working variable P (a to h as 0 to 7) before round T, as Var.
   function Var_Bits
     (H0 : State_Bits; X : Block_Witness; T : Round_Or_End;
      P : Sha256.Word_Index) return Word_Bits
   is (if P <= 3 then
         (if T > Natural (P) then X.A (T - 1 - Natural (P))
          else H0 (Sha256.Word_Index (Natural (P) - T)))
       else
         (if T > Natural (P) - 4 then X.E (T - 1 - (Natural (P) - 4))
          else H0 (Sha256.Word_Index (4 + (Natural (P) - 4) - T))));

   ----------------------------------------------------------------------
   --  The assertions (flatsha256_circuit.h 101 to 149)
   ----------------------------------------------------------------------

   --  Schedule word I: sigma1 (w (I - 2)), w (I - 7), sigma0 (w (I - 15)),
   --  w (I - 16).
   function Schedule_Words
     (M : Message_Bits; X : Block_Witness; I : Schedule_Step)
      return Gadgets.Words.Word_List
   is ([0 => Small_1_Form (W_Bits (M, X, I - 2)),
        1 => W_Bits (M, X, I - 7),
        2 => Small_0_Form (W_Bits (M, X, I - 15)),
        3 => W_Bits (M, X, I - 16),
        others => [others => Zero]]);

   --  The new e of round T: h, Sigma1 (e), Ch (e, f, g), K_t, w_t, d.
   --  (K_t is a constant of Sha256's private part: the bodies are below.)
   function E_Words
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness; T : Round)
      return Gadgets.Words.Word_List;

   --  The new a of round T: the five words of T1, Sigma0 (a), Maj (a, b, c).
   function A_Words
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness; T : Round)
      return Gadgets.Words.Word_List;

   --  Word J of the new state: H0 (J) and the working variable J after
   --  the last round.
   function H_Words
     (H0 : State_Bits; X : Block_Witness; J : Sha256.Word_Index)
      return Gadgets.Words.Word_List
   is ([0 => H0 (J), 1 => Var_Bits (H0, X, 64, J),
        others => [others => Zero]]);

   --  Every assertion of the block holds.
   function Assertions_Hold
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness) return Boolean
   is ((for all I in Schedule_Step =>
          Gadgets.Words.Assertion (Schedule_Words (M, X, I), 4, X.W (I))
          = Zero)
       and then
       (for all T in Round =>
          Gadgets.Words.Assertion (E_Words (M, H0, X, T), 6, X.E (T)) = Zero
          and then
          Gadgets.Words.Assertion (A_Words (M, H0, X, T), 7, X.A (T)) = Zero)
       and then
       (for all J in Sha256.Word_Index =>
          Gadgets.Words.Assertion (H_Words (H0, X, J), 2, X.H1 (J)) = Zero));

   ----------------------------------------------------------------------
   --  The decoding and the theorem
   ----------------------------------------------------------------------

   --  The bits of value I of the netlist: an input, a word of the
   --  witness, or the bit form of a round function over them.
   function Bits_At
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness; I : Value_Index)
      return Word_Bits;

   --  The values the witness decodes to.
   function Decoded
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness) return Values
   is ([for I in Value_Index => Word_Value (Bits_At (M, H0, X, I))]);

   --  G4: with the inputs the bits of H0 and of the block, every word of
   --  the witness bits, and every assertion holding, the decoded values
   --  satisfy the netlist, and the state after the block is FIPS 180-4's
   --  compression.
   procedure Lemma_Block
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness;
      S : Sha256.State; Block : Bytes_64)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       (for all J in Sha256.Word_Index => H0 (J) = Bits_Of (S (J)))
       and then (for all I in 0 .. 15 =>
                   M (I) = Bits_Of (Message_Word (Block, I)))
       and then Witness_Bits (X)
       and then Assertions_Hold (M, H0, X),
     Post   =>
       Holds (Decoded (M, H0, X), S, Block)
       and then Output (Decoded (M, H0, X)) = Compress_Spec (S, Block);

private

   function E_Words
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness; T : Round)
      return Gadgets.Words.Word_List
   is ([0 => Var_Bits (H0, X, T, 7),
        1 => Sigma_1_Form (Var_Bits (H0, X, T, 4)),
        2 => Ch_Form (Var_Bits (H0, X, T, 4), Var_Bits (H0, X, T, 5),
                      Var_Bits (H0, X, T, 6)),
        3 => Bits_Of (K (Round_Index (T))),
        4 => W_Bits (M, X, T),
        5 => Var_Bits (H0, X, T, 3),
        others => [others => Zero]]);

   function A_Words
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness; T : Round)
      return Gadgets.Words.Word_List
   is ([0 => Var_Bits (H0, X, T, 7),
        1 => Sigma_1_Form (Var_Bits (H0, X, T, 4)),
        2 => Ch_Form (Var_Bits (H0, X, T, 4), Var_Bits (H0, X, T, 5),
                      Var_Bits (H0, X, T, 6)),
        3 => Bits_Of (K (Round_Index (T))),
        4 => W_Bits (M, X, T),
        5 => Sigma_0_Form (Var_Bits (H0, X, T, 0)),
        6 => Maj_Form (Var_Bits (H0, X, T, 0), Var_Bits (H0, X, T, 1),
                       Var_Bits (H0, X, T, 2))]);

   function Bits_At
     (M : Message_Bits; H0 : State_Bits; X : Block_Witness; I : Value_Index)
      return Word_Bits
   is
     (if I < First_Message then H0 (Sha256.Word_Index (I))
      elsif I < First_Schedule then M (I - First_Message)
      elsif I < First_Round then
        (declare
           S : constant Schedule_Step := 16 + (I - First_Schedule) / 3;
         begin
           (case (I - First_Schedule) mod 3 is
              when 0      => Small_0_Form (W_Bits (M, X, S - 15)),
              when 1      => Small_1_Form (W_Bits (M, X, S - 2)),
              when others => X.W (S)))
      elsif I < First_Output then
        (declare
           T : constant Round := (I - First_Round) / 6;
         begin
           (case (I - First_Round) mod 6 is
              when 0 => Sigma_1_Form (Var_Bits (H0, X, T, 4)),
              when 1 =>
                Ch_Form (Var_Bits (H0, X, T, 4), Var_Bits (H0, X, T, 5),
                         Var_Bits (H0, X, T, 6)),
              when 2 => Sigma_0_Form (Var_Bits (H0, X, T, 0)),
              when 3 =>
                Maj_Form (Var_Bits (H0, X, T, 0), Var_Bits (H0, X, T, 1),
                          Var_Bits (H0, X, T, 2)),
              when 4      => X.E (T),
              when others => X.A (T)))
      else X.H1 (Sha256.Word_Index (I - First_Output)));

end Sha256.Trace.Netlist.Gadget;
