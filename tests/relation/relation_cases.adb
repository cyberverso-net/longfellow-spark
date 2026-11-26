--  relation_cases: the relation of the hash circuit (Mdoc_Relation.Hash)
--  against the registered circuit's evaluator, case by case (ADR 0091,
--  docs/guide/10-certified-circuits.md, Section 1). Test code.
--
--  For each case the program evaluates the circuit on the inputs and
--  the relation on the same inputs, and compares the two verdicts. The
--  circuit accepting while the relation is false is a defect of the
--  relation, the direction the checker of block 5 must prove: the
--  program fails on it. The circuit refusing while the relation holds
--  is allowed and listed: it shows where the relation is weaker than
--  the circuit.
--
--  The cases, from a list of test documents (tests/vectors/
--  relation_cases.txt):
--
--    honest    the witness and the inputs this project's builder and
--              encoder make for the document; a document whose request
--              it contradicts must give false, the others true. On the
--              honest ones the program also runs the lemmas of the
--              package and evaluates the hypotheses, which must hold.
--    mutation  on the documents marked "mutate": one change of the
--              honest witness or inputs per clause, aimed so that the
--              named clause fails; after a change of the signed message
--              or the item, the traces, e and the tags are recomputed,
--              so that the circuit's verdict is that of the constraint
--              aimed at.
--    neutral   on the document marked "reference": changes that the
--              relation does not constrain, and that the circuit does
--              not read; both must still accept.
--    synthetic on the reference: a second validUntil inside the MSO,
--              and random as a text string; the relation and the
--              circuit accept, and the hypothesis that excludes it is
--              false, which is why the hypothesis is needed.
--
--  The traces are recomputed in the layout of Mdoc_Witness (register
--  row R14): per block the 48 schedule words, the e and a of each
--  round, the state after it, each word as eight 4-bit chunks in the
--  legacy plucked form. That the recomputation is the builder's is
--  checked on every honest witness, which it must leave unchanged.
--
--  Usage: relation_cases <hash circuit .lfc2> <cases file> <testcases dir>
--  Exit status 0 when every case agrees, 1 otherwise.

with Ada.Assertions;
with Ada.Command_Line;          use Ada.Command_Line;
with Ada.Exceptions;
with Ada.Streams.Stream_IO;
with Ada.Strings.Fixed;         use Ada.Strings.Fixed;
with Ada.Strings.Unbounded;     use Ada.Strings.Unbounded;
with Ada.Text_IO;               use Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Interfaces;                use Interfaces;
with Bytes;                     use Bytes;
with GF2_128;
with Sha256;
with Sha256.Trace;
with Cbor_Parse;
with Mdoc_Parse;
with Mdoc_Witness;
with Mdoc_Inputs;
with Mdoc_Mac;
with Circuit_Status;
with Circuit_Reader_GF2_128;
with Packed_Circuits_GF2_128;
with Packed_Eval_GF2_128;
with Sumcheck_Algebra_GF2_128;
with Mdoc_Relation.Hash;
with Mdoc_Relation.Hash.Conditions;
with Gadgets.Bits;
with Block_Checks;

procedure Relation_Cases is

   package CR renames Circuit_Reader_GF2_128;
   package PE renames Packed_Eval_GF2_128;
   package SA renames Sumcheck_Algebra_GF2_128;
   package R  renames Mdoc_Relation.Hash;
   package HC renames Mdoc_Relation.Hash.Conditions;

   use type GF2_128.Element;
   use type SA.Element_Array;
   use type Circuit_Status.Status;
   use type Mdoc_Parse.Status;
   use type Mdoc_Witness.Status;

   --  The layout, the harness's own copy: the package is ghost, and
   --  executable code cannot name it. Layout_Agrees, below, checks
   --  each position against the package's, inside an assertion.
   Public_Count  : constant := 952;
   Private_Count : constant := 84_166;
   X_Id_Len      : constant := 769;
   X_Now         : constant := 785;
   X_Tags        : constant := 945;
   X_Av          : constant := 951;
   W_E           : constant := 0;
   W_Dpk_X       : constant := 256;
   W_Count       : constant := 768;
   W_Message     : constant := 776;
   W_Blocks      : constant := 21_112;
   W_Valid_From  : constant := 79_992;
   W_Valid_Until : constant := 80_004;
   W_Device_Key  : constant := 80_016;
   W_Value_Digests : constant := 80_028;
   W_Item        : constant := 80_040;
   W_Item_Blocks : constant := 81_064;
   W_Digest_Index : constant := 84_008;
   W_Ei          : constant := 84_020;
   W_Ev          : constant := 84_044;
   W_Slots       : constant := 84_068;
   W_Slot_Lengths : constant := 84_104;
   W_Perm        : constant := 84_152;
   W_Pads        : constant := 84_160;
   Max_Blocks    : constant := 40;
   Prefix_Length : constant := 18;

   Prefix : constant Byte_Array (0 .. Prefix_Length - 1) :=
     [16#84#, 16#6A#, 16#53#, 16#69#, 16#67#, 16#6E#, 16#61#, 16#74#,
      16#75#, 16#72#, 16#65#, 16#31#, 16#43#, 16#A1#, 16#01#, 16#26#,
      16#40#, 16#59#];

   Valid_Until_Key : constant Byte_Array (0 .. 12) :=
     [16#6A#, 16#76#, 16#61#, 16#6C#, 16#69#, 16#64#, 16#55#, 16#6E#,
      16#74#, 16#69#, 16#6C#, 16#C0#, 16#74#];

   function Layout_Agrees return Boolean is
   begin
      pragma Assert
        (Public_Count = R.Public_Count and then Private_Count = R.Private_Count
         and then X_Id_Len = R.X_Id_Len and then X_Now = R.X_Now
         and then X_Tags = R.X_Tags and then X_Av = R.X_Av
         and then W_E = R.W_E and then W_Dpk_X = R.W_Dpk_X
         and then W_Count = R.W_Count and then W_Message = R.W_Message
         and then W_Blocks = R.W_Blocks and then W_Valid_From = R.W_Valid_From
         and then W_Valid_Until = R.W_Valid_Until
         and then W_Device_Key = R.W_Device_Key
         and then W_Value_Digests = R.W_Value_Digests
         and then W_Item = R.W_Item and then W_Item_Blocks = R.W_Item_Blocks
         and then W_Digest_Index = R.W_Digest_Index and then W_Ei = R.W_Ei
         and then W_Ev = R.W_Ev and then W_Slots = R.W_Slots
         and then W_Slot_Lengths = R.W_Slot_Lengths
         and then W_Perm = R.W_Perm and then W_Pads = R.W_Pads
         and then Max_Blocks = R.Max_Blocks
         and then Prefix_Length = R.Prefix_Length
         and then Prefix = R.Prefix
         and then Valid_Until_Key = R.Valid_Until_Key);
      return True;
   exception
      when Ada.Assertions.Assertion_Error => return False;
   end Layout_Agrees;

   subtype X_Array is SA.Element_Array (0 .. Public_Count - 1);
   subtype W_Array is SA.Element_Array (0 .. Private_Count - 1);
   subtype All_Array is
     SA.Element_Array (0 .. Public_Count + Private_Count - 1);
   subtype Date is Byte_Array (0 .. 19);

   type Byte_Access is access Byte_Array;
   type X_Access is access X_Array;
   type W_Access is access W_Array;
   type All_Access is access All_Array;

   procedure Free is new Ada.Unchecked_Deallocation (Byte_Array, Byte_Access);
   procedure Free is new Ada.Unchecked_Deallocation (X_Array, X_Access);
   procedure Free is new Ada.Unchecked_Deallocation (W_Array, W_Access);

   Usage : exception;

   Failures : Natural := 0;
   Cases    : Natural := 0;
   Weaker   : Natural := 0;

   ----------------------------------------------------------------------
   --  Files
   ----------------------------------------------------------------------

   function Read_File (Path : String) return Byte_Access is
      use Ada.Streams.Stream_IO;
      F : Ada.Streams.Stream_IO.File_Type;
   begin
      Open (F, In_File, Path);
      declare
         N : constant Natural := Natural (Size (F));
         B : constant Byte_Access := new Byte_Array (0 .. N - 1);
         S : constant Stream_Access := Stream (F);
      begin
         Byte_Array'Read (S, B.all);
         Close (F);
         return B;
      end;
   end Read_File;

   function Hex_Bytes (S : String) return Byte_Array is
      function Nibble (C : Character) return Unsigned_8 is
        (case C is
            when '0' .. '9' => Character'Pos (C) - Character'Pos ('0'),
            when 'a' .. 'f' => Character'Pos (C) - Character'Pos ('a') + 10,
            when 'A' .. 'F' => Character'Pos (C) - Character'Pos ('A') + 10,
            when others     => raise Usage);
      B : Byte_Array (0 .. S'Length / 2 - 1);
   begin
      if S'Length mod 2 /= 0 then
         raise Usage;
      end if;
      for I in B'Range loop
         B (I) := 16 * Nibble (S (S'First + 2 * I))
                  + Nibble (S (S'First + 2 * I + 1));
      end loop;
      return B;
   end Hex_Bytes;

   function To_Bytes (S : String) return Byte_Array is
     ([for I in 0 .. S'Length - 1 => Character'Pos (S (S'First + I))]);

   --  The value of "key value" in request.txt.
   function Request_Field (Path, Key : String) return String is
      F : Ada.Text_IO.File_Type;
   begin
      Open (F, In_File, Path);
      while not End_Of_File (F) loop
         declare
            L : constant String := Get_Line (F);
         begin
            if L'Length > Key'Length
              and then L (L'First .. L'First + Key'Length) = Key & ' '
            then
               Close (F);
               return L (L'First + Key'Length + 1 .. L'Last);
            end if;
         end;
      end loop;
      Close (F);
      raise Usage with Path & ": no " & Key;
   end Request_Field;

   ----------------------------------------------------------------------
   --  Reading and writing elements
   ----------------------------------------------------------------------

   function Bit_Element (V : Unsigned_64; K : Natural) return GF2_128.Element
   is
     (if (Shift_Right (V, K) and 1) = 1 then GF2_128.One else GF2_128.Zero);

   function Byte_Of (A : SA.Element_Array; Pos : Natural) return Unsigned_8 is
      B : Unsigned_8 := 0;
   begin
      for K in reverse 0 .. 7 loop
         B := 2 * B + (if A (Pos + K) = GF2_128.One then 1 else 0);
      end loop;
      return B;
   end Byte_Of;

   function Index_Of (A : SA.Element_Array; Pos : Natural) return Natural is
      N : Natural := 0;
   begin
      for K in reverse 0 .. 11 loop
         N := 2 * N + (if A (Pos + K) = GF2_128.One then 1 else 0);
      end loop;
      return N;
   end Index_Of;

   procedure Put_Byte
     (A : in out SA.Element_Array; Pos : Natural; B : Unsigned_8) is
   begin
      for K in 0 .. 7 loop
         A (Pos + K) := Bit_Element (Unsigned_64 (B), K);
      end loop;
   end Put_Byte;

   procedure Put_Index
     (A : in out SA.Element_Array; Pos : Natural; V : Natural) is
   begin
      for K in 0 .. 11 loop
         A (Pos + K) := Bit_Element (Unsigned_64 (V), K);
      end loop;
   end Put_Index;

   procedure Flip (A : in out SA.Element_Array; Pos : Natural) is
   begin
      A (Pos) := (if A (Pos) = GF2_128.One then GF2_128.Zero else GF2_128.One);
   end Flip;

   --  Byte J of the signed message after its 18-byte prefix (in_), and
   --  byte Q of the preimage, the prefix first.
   function Message (W : W_Array; J : Natural) return Unsigned_8 is
     (Byte_Of (W, W_Message + 8 * J));

   procedure Put_Message (W : in out W_Array; J : Natural; B : Unsigned_8) is
   begin
      Put_Byte (W, W_Message + 8 * J, B);
   end Put_Message;

   function Preimage (W : W_Array; Q : Natural) return Unsigned_8 is
     (if Q < Prefix_Length then Prefix (Q) else Message (W, Q - Prefix_Length));

   function Item_Byte (W : W_Array; I : Natural) return Unsigned_8 is
     (Byte_Of (W, W_Item + 8 * I));

   function Item_Bytes (W : W_Array) return Byte_Array is
     ([for I in 0 .. 127 => Item_Byte (W, I)]);

   --  The 32 bytes of a state, FIPS 180-4 order.
   function Digest_Of (S : Sha256.State) return Bytes_32 is
     ([for I in 0 .. 31 =>
         Unsigned_8 (Shift_Right (S (Sha256.Word_Index (I / 4)),
                                  24 - 8 * (I mod 4)) and 16#FF#)]);

   function Item_Digest (W : W_Array) return Bytes_32 is
      H  : Sha256.State := Sha256.Initial_State;
      T  : Sha256.Trace.Block_Trace;
      It : constant Byte_Array := Item_Bytes (W);
   begin
      Sha256.Trace.Compress_Traced (H, It, 0, T);
      Sha256.Trace.Compress_Traced (H, It, 64, T);
      return Digest_Of (H);
   end Item_Digest;

   --  A word in the legacy plucked form (Mdoc_Witness.Put_V32_Legacy).
   procedure Put_V32 (W : in out W_Array; Pos : in out Natural;
                      X : Unsigned_32) is
   begin
      for K in 0 .. 7 loop
         W (Pos) :=
           GF2_128.Inject
             (GF2_128.Subfield_Value
                (Shift_Left (Shift_Right (X, 4 * K) and 15, 1) xor 15));
         Pos := Pos + 1;
      end loop;
   end Put_V32;

   --  One block's trace (Mdoc_Witness.Put_Block).
   procedure Put_Block (W : in out W_Array; Pos : in out Natural;
                        T : Sha256.Trace.Block_Trace; H : Sha256.State) is
   begin
      for I in 0 .. 47 loop
         Put_V32 (W, Pos, T.W (I));
      end loop;
      for I in 0 .. 63 loop
         Put_V32 (W, Pos, T.E (I));
         Put_V32 (W, Pos, T.A (I));
      end loop;
      for I in Sha256.Word_Index loop
         Put_V32 (W, Pos, H (I));
      end loop;
   end Put_Block;

   --  The traces of the 40 blocks and of the item's two, and e, from
   --  the message and the item the witness holds.
   procedure Retrace (W : in out W_Array) is
      Nb  : constant Natural := Natural (Byte_Of (W, W_Count));
      H   : Sha256.State := Sha256.Initial_State;
      T   : Sha256.Trace.Block_Trace;
      Pos : Natural := W_Blocks;
      Pre : constant Byte_Array (0 .. 64 * Max_Blocks - 1) :=
        [for Q in 0 .. 64 * Max_Blocks - 1 => Preimage (W, Q)];
      E   : Bytes_32 := [others => 0];
      It  : constant Byte_Array := Item_Bytes (W);
   begin
      for B in 0 .. Max_Blocks - 1 loop
         Sha256.Trace.Compress_Traced (H, Pre, 64 * B, T);
         Put_Block (W, Pos, T, H);
         if B + 1 = Nb then
            E := Digest_Of (H);
         end if;
      end loop;
      H := Sha256.Initial_State;
      Pos := W_Item_Blocks;
      for B in 0 .. 1 loop
         Sha256.Trace.Compress_Traced (H, It, 64 * B, T);
         Put_Block (W, Pos, T, H);
      end loop;
      for I in 0 .. 31 loop
         Put_Byte (W, W_E + 8 * I, E (31 - I));
      end loop;
   end Retrace;

   --  The item's digest into the message at the digest's index.
   procedure Place_Item_Digest (W : in out W_Array) is
      D : constant Bytes_32 := Item_Digest (W);
      K : constant Natural := Index_Of (W, W_Digest_Index);
   begin
      for J in 0 .. 31 loop
         Put_Message (W, 7 + K + 2 + J, D (J));
      end loop;
   end Place_Item_Digest;

   function Bytes_At (W : W_Array; Pos : Natural) return Bytes_32 is
     ([for I in 0 .. 31 => Byte_Of (W, Pos + 8 * I)]);

   --  The tags of e, x and y under Av and the pads, into X and W.
   procedure Retag (X : in out X_Array; W : in out W_Array;
                    Ap : Mdoc_Mac.Pads; Av : GF2_128.Element) is
      T : constant Mdoc_Mac.Tags :=
        Mdoc_Mac.Legacy_Tags
          (Av, Ap, [Bytes_At (W, W_E), Bytes_At (W, W_Dpk_X),
                    Bytes_At (W, W_Dpk_X + 256)]);
   begin
      for I in Mdoc_Mac.Tag_Index loop
         X (X_Tags + I) := T (I);
      end loop;
      X (X_Av) := Av;
      for I in Mdoc_Mac.Message_Index loop
         for H in Mdoc_Mac.Half_Index loop
            W (W_Pads + 2 * I + H) := Ap (I) (H);
         end loop;
      end loop;
   end Retag;

   ----------------------------------------------------------------------
   --  The two verdicts
   ----------------------------------------------------------------------

   Circuit : CR.Packed_Access;

   function Circuit_Accepts (X : X_Array; W : W_Array) return Boolean is
      procedure Free is new Ada.Unchecked_Deallocation (All_Array, All_Access);
      All_In : All_Access := new All_Array;
      Segs   : SA.Seg_Array_Access;
      Ok     : Boolean;
   begin
      All_In (0 .. Public_Count - 1) := X;
      All_In (Public_Count .. All_In'Last) := W;
      SA.Allocate_Segs (PE.Shape_Of (Circuit.all), Segs);
      PE.Eval_Circuit (Circuit.all, All_In.all, Segs.all, Ok);
      SA.Release_Segs (Segs);
      Free (All_In);
      return Ok;
   end Circuit_Accepts;

   --  Where the circuit refuses: every Z assertion of every layer that
   --  fails (layer, the two input wires), and every output of layer 0
   --  that is not zero. The wires are those of the layer's input
   --  segment, so that a map of the wires (the generator's, outside
   --  this project) names the gadget of each. At most Shown lines each;
   --  the counts are complete.
   --  The constant terms of the four plucking polynomials, by
   --  interpolation (Gadgets.Bits). Neither 0 nor 1: Locate checks that
   --  the registered circuit's plucker gives them on the element 0.
   Pluck_C : constant Gadgets.Bits.Coefficients := Gadgets.Bits.Interpolate;

   --  Locate lists the failing assertions. For each failing assertion
   --  whose wire is v - v * v (a term v * v at the layer below), it also
   --  reads v, the plucker's output, and counts it against the four
   --  constant terms: Constant_Hits (K) for C (K, 0), Constant_Other for
   --  any other value. With the element 0 as the plucker's input, v is
   --  the constant term of its polynomial in the registered circuit.
   type Hit_Array is array (Gadgets.Bits.Pluck_Index) of Natural;

   procedure Locate (Label : String; X : X_Array; W : W_Array;
                     Constant_Hits : out Hit_Array;
                     Constant_Other : out Natural) is
      package PCG renames Packed_Circuits_GF2_128;
      procedure Free is new Ada.Unchecked_Deallocation (All_Array, All_Access);
      Shown  : constant := 8;
      All_In : All_Access := new All_Array;
      Segs   : SA.Seg_Array_Access;
      Ok     : Boolean;
      Total  : Natural := 0;
      Lines  : Natural := 0;

      --  The terms v * v of layer L whose output is wire A: v is read in
      --  the inputs of layer L.
      procedure Read_Plucks (L : Natural; A : SA.Wire_Index) is
         C  : PCG.Cursor := PCG.Start (Circuit.all, L);
         Tm : SA.Term;
      begin
         for K in 1 .. PCG.Layer_Len (Circuit.all, L) loop
            Tm := PCG.Term_Of (Circuit.all, C);
            if Tm.G = A and then Tm.H0 = Tm.H1 and then Tm.H0 /= 0 then
               declare
                  V     : constant GF2_128.Element := Segs (L + 1) (Tm.H0);
                  Found : Boolean := False;
               begin
                  for P in Gadgets.Bits.Pluck_Index loop
                     if V = Pluck_C (P, 0) then
                        Constant_Hits (P) := Constant_Hits (P) + 1;
                        Found := True;
                     end if;
                  end loop;
                  if not Found then
                     Constant_Other := Constant_Other + 1;
                  end if;
               end;
            end if;
            C := PCG.Step (Circuit.all, C);
         end loop;
      end Read_Plucks;
   begin
      Constant_Hits := [others => 0];
      Constant_Other := 0;
      All_In (0 .. Public_Count - 1) := X;
      All_In (Public_Count .. All_In'Last) := W;
      SA.Allocate_Segs (PE.Shape_Of (Circuit.all), Segs);
      PE.Eval_Circuit (Circuit.all, All_In.all, Segs.all, Ok);
      for J in 0 .. Circuit.Last_Layer loop
         declare
            C     : PCG.Cursor := PCG.Start (Circuit.all, J);
            Tm    : SA.Term;
            In_J  : SA.Element_Array renames Segs (J + 1).all;
            Count : Natural := 0;
         begin
            for K in 1 .. PCG.Layer_Len (Circuit.all, J) loop
               Tm := PCG.Term_Of (Circuit.all, C);
               if Tm.K = SA.Zero
                 and then GF2_128.Mul (In_J (Tm.H1), In_J (Tm.H0)) /= SA.Zero
               then
                  Count := Count + 1;
                  if J < Circuit.Last_Layer then
                     Read_Plucks (J + 1, Tm.H0);
                     if Tm.H1 /= Tm.H0 then
                        Read_Plucks (J + 1, Tm.H1);
                     end if;
                  end if;
                  if Lines < Shown then
                     Lines := Lines + 1;
                     Put_Line ("locate " & Label & ": z layer" & J'Image
                               & " h0" & Tm.H0'Image & " h1" & Tm.H1'Image);
                  end if;
               end if;
               C := PCG.Step (Circuit.all, C);
            end loop;
            if Count > 0 then
               Put_Line ("locate " & Label & ": layer" & J'Image & ","
                         & Count'Image & " Z assertions fail");
            end if;
            Total := Total + Count;
         end;
      end loop;
      for G in Segs (0)'Range loop
         if Segs (0) (G) /= SA.Zero then
            Put_Line ("locate " & Label & ": output" & G'Image & " not zero");
            Total := Total + 1;
         end if;
      end loop;
      Put_Line ("locate " & Label & ": plucker outputs equal to C (k, 0):"
                & Constant_Hits (0)'Image & Constant_Hits (1)'Image
                & Constant_Hits (2)'Image & Constant_Hits (3)'Image
                & ", other outputs read:" & Constant_Other'Image);
      Put_Line ("locate " & Label & ":" & Total'Image
                & " failing assertions and outputs, circuit "
                & (if Ok then "accepts" else "refuses"));
      SA.Release_Segs (Segs);
      Free (All_In);
   end Locate;

   --  The ghost predicates, read through an assertion: with -gnata a
   --  false assertion raises Assertion_Error, which these turn into
   --  False. The preconditions hold on every case (the shapes are
   --  fixed and X (0) is the one).
   function Relation_Holds (X : X_Array; W : W_Array) return Boolean is
   begin
      pragma Assert (R.Hash_Relation (X, W));
      return True;
   exception
      when Ada.Assertions.Assertion_Error => return False;
   end Relation_Holds;

   function Bits_Hold (X : X_Array; W : W_Array) return Boolean is
   begin
      pragma Assert (R.Bits (X, W));
      return True;
   exception
      when Ada.Assertions.Assertion_Error => return False;
   end Bits_Hold;

   Clause_Count : constant := 10;
   Clause_Names : constant array (0 .. Clause_Count - 1) of String (1 .. 13) :=
     ["chain        ", "zero_tail    ", "length       ", "valid_from   ",
      "valid_until  ", "device_key   ", "value_digests", "value_digest ",
      "item         ", "tags         "];

   function Clause_Holds (C : Natural; X : X_Array; W : W_Array)
     return Boolean is
   begin
      pragma Assert
        (R.Clause_Holds
           (R.Clause'Val (C), R.Decode_Public (X), R.Decode_Private (W)));
      return True;
   exception
      when Ada.Assertions.Assertion_Error => return False;
   end Clause_Holds;

   --  The clauses that fail, by name, or "bits".
   function Failing (X : X_Array; W : W_Array) return String is
      Out_S : String (1 .. 200) := [others => ' '];
      Last  : Natural := 0;
   begin
      if not Bits_Hold (X, W) then
         return "bits";
      end if;
      for C in 0 .. Clause_Count - 1 loop
         if not Clause_Holds (C, X, W) then
            declare
               N : constant String := Trim (Clause_Names (C), Ada.Strings.Right);
            begin
               if Last > 0 then
                  Last := Last + 1;
               end if;
               Out_S (Last + 1 .. Last + N'Length) := N;
               Last := Last + N'Length;
            end;
         end if;
      end loop;
      return Out_S (1 .. Last);
   end Failing;

   function Matching_Holds
     (Map : Byte_Array; P : Mdoc_Parse.Parsed_Mdoc; It : Mdoc_Parse.Item;
      D   : Bytes_32) return Boolean is
   begin
      pragma Assert (HC.H_Matching_By_Content (Map, P, It, D));
      return True;
   exception
      when Ada.Assertions.Assertion_Error => return False;
   end Matching_Holds;

   function Types_Hold (Item : Byte_Array; It : Mdoc_Parse.Item)
     return Boolean is
   begin
      pragma Assert (HC.H_Types_In_Item (Item, It));
      return True;
   exception
      when Ada.Assertions.Assertion_Error => return False;
   end Types_Hold;

   type Expectation is (Holds, Fails, Neutral, Synthetic);

   --  One case: the two verdicts, compared. Target names the clause a
   --  mutation aims at ("" for none).
   procedure Check
     (Label  : String;
      X      : X_Array;
      W      : W_Array;
      Expect : Expectation;
      Target : String := "")
   is
      C_Ok : constant Boolean := Circuit_Accepts (X, W);
      R_Ok : constant Boolean := Relation_Holds (X, W);
      F    : constant String := Failing (X, W);
      Why  : Unbounded_String;
   begin
      Cases := Cases + 1;
      if C_Ok and then not R_Ok then
         Append (Why, "the circuit accepts and the relation is false; ");
      end if;
      if R_Ok /= (F = "") then
         Append (Why, "the relation and its clauses disagree; ");
      end if;
      case Expect is
         when Holds | Neutral | Synthetic =>
            if not R_Ok then
               Append (Why, "the relation should hold; ");
            elsif not C_Ok then
               Append (Why, "the circuit should accept; ");
            end if;
         when Fails =>
            if R_Ok then
               Append (Why, "the relation should be false; ");
            elsif Target /= "" and then Index (" " & F & " ", " " & Target & " ") = 0
            then
               Append (Why, "the clause aimed at holds; ");
            end if;
      end case;
      Put ((if Length (Why) > 0 then "FAIL " else "ok   ") & Label & ": circuit "
           & (if C_Ok then "accepts" else "refuses") & ", relation "
           & (if R_Ok then "holds" else "false (" & F & ")"));
      if not C_Ok and then R_Ok then
         Weaker := Weaker + 1;
         Put (" [the circuit refuses where the relation holds]");
      end if;
      if Length (Why) > 0 then
         Put (": " & To_String (Why));
         Failures := Failures + 1;
      end if;
      New_Line;
   end Check;

   procedure Report (Label : String; Ok : Boolean) is
   begin
      Put_Line ((if Ok then "ok   " else "FAIL ") & Label);
      if not Ok then
         Failures := Failures + 1;
      end if;
   end Report;

   ----------------------------------------------------------------------
   --  One document
   ----------------------------------------------------------------------

   --  Fixed pads and challenge: the relation does not depend on them
   --  being random, and the cases are reproducible.
   Ap : constant Mdoc_Mac.Pads :=
     [for I in Mdoc_Mac.Message_Index =>
        [for H in Mdoc_Mac.Half_Index =>
           (Limbs => [0 => Unsigned_64 (16#1000# + 2 * I + H),
                      1 => 16#A5A5_5A5A_0F0F_F0F0#])]];
   Av : constant GF2_128.Element :=
     (Limbs => [0 => 16#0123_4567_89AB_CDEF#, 1 => 16#FEDC_BA98_7654_3210#]);

   type Mutation is
     (M_Bits, M_Chain, M_Zero_Tail, M_Length, M_Valid_From, M_Valid_Until,
      M_Device_Key, M_Value_Digests, M_Value_Digest, M_Item_Slot,
      M_Item_Map, M_Tags, M_Id_Len);

   Target_Of : constant array (Mutation) of String (1 .. 13) :=
     [M_Bits          => "bits         ",
      M_Chain         => "chain        ",
      M_Zero_Tail     => "zero_tail    ",
      M_Length        => "length       ",
      M_Valid_From    => "valid_from   ",
      M_Valid_Until   => "valid_until  ",
      M_Device_Key    => "device_key   ",
      M_Value_Digests => "value_digests",
      M_Value_Digest  => "value_digest ",
      M_Item_Slot     => "item         ",
      M_Item_Map      => "item         ",
      M_Tags          => "tags         ",
      M_Id_Len        => "item         "];

   --  The start of the random entry in the item: its slot by the
   --  permutation (bits 2 and 3), the slot's start (5, i1, i2, i3).
   function Random_Start (W : W_Array) return Natural is
      Perm : constant Unsigned_8 := Byte_Of (W, W_Perm);
      S    : constant Natural := Natural (Shift_Right (Perm, 2) and 3);
   begin
      return (if S = 0 then 5 else Index_Of (W, W_Slots + 12 * (S - 1)));
   end Random_Start;

   --  The request the encoder puts in X at version 7 with one
   --  attribute, as Decode_Public should read it: the identifier as a
   --  CBOR text (a one-byte head up to 23 characters, two from 24),
   --  the value, the lengths upstream's encoder pushes (mdoc_witness.h
   --  501 and 502), now, the tags and av. Ghost: it names the package.
   function Expected_Public
     (A : Mdoc_Inputs.Attribute; Now : Date; T : Mdoc_Mac.Tags)
      return R.Public_Part
   is
     (R.Public_Part'
        (Id        =>
           [for I in 0 .. 31 =>
              (if A.Id_Len <= 23 then
                 (if I = 0 then 16#60# + Unsigned_8 (A.Id_Len)
                  elsif I <= A.Id_Len then A.Id (I - 1)
                  else 0)
               else
                 (if I = 0 then 16#78#
                  elsif I = 1 then Unsigned_8 (A.Id_Len)
                  elsif I <= A.Id_Len + 1 then A.Id (I - 2)
                  else 0))],
         Value     =>
           [for I in 0 .. 63 =>
              (if I < A.Value_Len then A.Value (I) else 0)],
         Id_Len    => Unsigned_8 (1 + 17 + 1 + A.Id_Len),
         Value_Len => Unsigned_8 (A.Value_Len + 12 + 1),
         Now       => Now,
         Tags      => T,
         Av        => Av))
   with Ghost;

   --  The document with the item of Old_Id rewritten under the
   --  identifier New_Id, the same value and digestID, a random of 16
   --  bytes, and its value digest in the MSO replaced by the digest of
   --  the new item. The issuer's signature no longer verifies, which
   --  the hash circuit does not read: the case tests the hash circuit
   --  alone. Null when the parse refuses either document.
   function Renamed
     (Doc, Tr, Doc_Type, Old_Id, New_Id, Value : Byte_Array)
      return Byte_Access
   is
      P   : Mdoc_Parse.Parsed_Mdoc;
      St  : Mdoc_Parse.Status;
      Cst : Cbor_Parse.Status;
      K   : Natural;
   begin
      Mdoc_Parse.Parse (Doc, Tr, Doc_Type, 7, P, St, Cst);
      if St /= Mdoc_Parse.Ok then
         return null;
      end if;
      K := Natural (Mdoc_Parse.Find_Item (Doc, P, Old_Id));
      if K = 0 then
         return null;
      end if;
      declare
         It  : constant Mdoc_Parse.Item := P.Items (Mdoc_Parse.Item_Index (K));
         D   : constant Unsigned_64 := It.Digest_Id;
         Did : constant Byte_Array :=
           (if D <= 23 then [0 => Unsigned_8 (D)]
            elsif D <= 255 then [16#18#, Unsigned_8 (D)]
            else [16#19#, Unsigned_8 (D / 256), Unsigned_8 (D mod 256)]);
         Rnd : constant Byte_Array := [16#50#] & [1 .. 16 => 16#A5#];
         IdH : constant Byte_Array :=
           (if New_Id'Length <= 23
            then [0 => 16#60# + Unsigned_8 (New_Id'Length)]
            else [16#78#, Unsigned_8 (New_Id'Length)]);
         Map : constant Byte_Array :=
           [16#A4#, 16#68#] & To_Bytes ("digestID") & Did
           & [0 => 16#66#] & To_Bytes ("random") & Rnd
           & [0 => 16#71#] & To_Bytes ("elementIdentifier") & IdH & New_Id
           & [0 => 16#6C#] & To_Bytes ("elementValue") & Value;
         Wrapped : constant Byte_Array :=
           [16#D8#, 16#18#, 16#58#, Unsigned_8 (Map'Length)] & Map;
         First  : constant Natural := Doc'First + It.Item_Start;
         N      : constant Byte_Access :=
           new Byte_Array'(Doc (Doc'First .. First - 1) & Wrapped
                           & Doc (First + It.Item_Len .. Doc'Last));
         Ctx    : Sha256.Context := Sha256.Initial;
         P2     : Mdoc_Parse.Parsed_Mdoc;
         K2     : Natural;
         Pos    : Natural;
      begin
         Mdoc_Parse.Parse (N.all, Tr, Doc_Type, 7, P2, St, Cst);
         if St /= Mdoc_Parse.Ok then
            return null;
         end if;
         K2 := Natural (Mdoc_Parse.Find_Item (N.all, P2, New_Id));
         if K2 = 0 then
            return null;
         end if;
         Pos := N'First + P2.Mso_Start + Mdoc_Parse.Mso_Head_Len
                + P2.Items (Mdoc_Parse.Item_Index (K2)).Digest_Offset;
         if N (Pos) /= 16#58# or else N (Pos + 1) /= 16#20# then
            return null;
         end if;
         Sha256.Update (Ctx, Wrapped);
         N (Pos + 2 .. Pos + 33) := Sha256.Digest (Ctx);
         return N;
      end;
   end Renamed;

   Count_Values : constant array (1 .. 3) of Unsigned_8 := [0, 41, 255];

   --  The reference netlist and the gadget G4 on every block the
   --  honest witness hashes: the nb blocks of the signed message and
   --  the item's two (Block_Checks; chapter 10, Section 2).
   procedure Check_Blocks (Name : String; W : W_Array) is
      Nb  : constant Natural := Natural (Byte_Of (W, W_Count));
      H   : Sha256.State := Sha256.Initial_State;
      T   : Sha256.Trace.Block_Trace;
      Pre : constant Byte_Array (0 .. 64 * Max_Blocks - 1) :=
        [for Q in 0 .. 64 * Max_Blocks - 1 => Preimage (W, Q)];
      It  : constant Byte_Array := Item_Bytes (W);
      Net : Boolean := True;
      Gad : Boolean := True;

      procedure One (Data : Byte_Array; B : Natural) is
         Block : constant Bytes_64 := Data (64 * B .. 64 * B + 63);
      begin
         Net := Net and then Block_Checks.Check_Netlist (H, Block);
         Gad := Gad and then Block_Checks.Check_Gadget (H, Block);
         Sha256.Trace.Compress_Traced (H, Data, 64 * B, T);
      end One;
   begin
      for B in 0 .. Nb - 1 loop
         One (Pre, B);
      end loop;
      H := Sha256.Initial_State;
      for B in 0 .. 1 loop
         One (It, B);
      end loop;
      Report ("netlist " & Name & ": Interpret is the traced compression"
              & " on the" & Natural'Image (Nb + 2) & " blocks", Net);
      Report ("gadget " & Name & ": every assertion holds on the honest"
              & " trace of the" & Natural'Image (Nb + 2) & " blocks", Gad);
   end Check_Blocks;

   procedure Run_Document
     (Dir, Doc_Name, Attr : String;
      Positive_Case, Mutate, Reference : Boolean;
      Rename : String := "";
      Padding : Boolean := False;
      Count : Boolean := False)
   is
      --  The case's name in the report: the document, and the new
      --  identifier of a rewritten one.
      Name   : constant String :=
        (if Rename = "" then Doc_Name else Doc_Name & "/" & Rename);
      D      : constant String := Dir & "/" & Doc_Name;
      Doc    : Byte_Access := Read_File (D & "/mdoc.bin");
      Tr     : Byte_Access := Read_File (D & "/transcript.bin");
      Now_S  : constant String := Request_Field (D & "/request.txt", "now");
      Type_S : constant String := Request_Field (D & "/request.txt", "doc_type");
      Colon  : constant Natural := Index (Attr, ":");
      Old_Id : constant Byte_Array := To_Bytes (Attr (Attr'First .. Colon - 1));
      Id     : constant Byte_Array :=
        (if Rename = "" then Old_Id else To_Bytes (Rename));
      Value  : constant Byte_Array := Hex_Bytes (Attr (Colon + 1 .. Attr'Last));
      A      : Mdoc_Inputs.Attribute;
      Attrs  : Mdoc_Inputs.Attribute_List (1 .. 1);
      Now    : constant Date := To_Bytes (Now_S);
      P      : Mdoc_Parse.Parsed_Mdoc;
      St     : Mdoc_Parse.Status;
      Cst    : Cbor_Parse.Status;
      WS     : Mdoc_Witness.Status;
      X0     : X_Access := new X_Array;
      W0     : W_Access := new W_Array;
      X      : X_Access := new X_Array;
      W      : W_Access := new W_Array;
      T      : Mdoc_Mac.Tags;
   begin
      if Rename /= "" then
         declare
            N : constant Byte_Access :=
              Renamed (Doc.all, Tr.all, To_Bytes (Type_S), Old_Id, Id, Value);
         begin
            if N = null then
               Report (Name & ": the document cannot be rewritten", False);
               return;
            end if;
            Free (Doc);
            Doc := N;
         end;
      end if;
      A.Id (0 .. Id'Length - 1) := Id;
      A.Id_Len := Id'Length;
      A.Value (0 .. Value'Length - 1) := Value;
      A.Value_Len := Value'Length;
      Attrs (1) := A;
      Mdoc_Parse.Parse (Doc.all, Tr.all, To_Bytes (Type_S), 7, P, St, Cst);
      if St /= Mdoc_Parse.Ok then
         Report (Name & ": the parse refuses it, " & St'Image, False);
         return;
      end if;
      Mdoc_Witness.Hash_Witness (7, Doc.all, P, Attrs, Ap, W0.all, WS);
      if WS /= Mdoc_Witness.Ok then
         Report (Name & ": the builder refuses it, " & WS'Image, False);
         return;
      end if;
      T := Mdoc_Mac.Legacy_Tags (Av, Ap, Mdoc_Witness.Messages (P));
      Mdoc_Inputs.Hash_Inputs (7, Attrs, Now, T, Av, X0.all);

      --  The recomputation of the traces leaves the honest witness as
      --  the builder made it.
      W.all := W0.all;
      Retrace (W.all);
      if W.all /= W0.all then
         Report (Name & ": the traces recomputed differ from the builder's",
                 False);
      end if;

      --  The public inputs decode to the request (tested here, to be
      --  proved with the emitter), and each byte's elements are the
      --  layout Lemma_Byte_At takes.
      begin
         pragma Assert
           (R."=" (R.Decode_Public (X0.all), Expected_Public (A, Now, T)));
         for I in 0 .. 31 loop
            R.Lemma_Byte_At
              (X0.all, R.X_Id + 8 * I, Expected_Public (A, Now, T).Id (I));
         end loop;
         Report ("public " & Name & ": Decode_Public is the request", True);
      exception
         when E : Ada.Assertions.Assertion_Error =>
            Report ("public " & Name & ": "
                    & Ada.Exceptions.Exception_Message (E), False);
      end;

      Check ("honest " & Name, X0.all, W0.all,
             (if Positive_Case then Holds else Fails),
             (if Positive_Case then "" else "item"));
      if Positive_Case then
         Check_Blocks (Name, W0.all);
      end if;

      declare
         It      : constant Mdoc_Parse.Item :=
           P.Items (Mdoc_Parse.Find_Item (Doc.all, P, Id));
         Map_Len : constant Natural := P.Mso_Len - Mdoc_Parse.Mso_Head_Len;
         Nb      : constant Natural := Natural (Byte_Of (W0.all, W_Count));
         VF      : constant Natural := Index_Of (W0.all, W_Valid_From);
         VU      : constant Natural := Index_Of (W0.all, W_Valid_Until);
         DK      : constant Natural := Index_Of (W0.all, W_Device_Key);
         VD      : constant Natural := Index_Of (W0.all, W_Value_Digests);
         DI      : constant Natural := Index_Of (W0.all, W_Digest_Index);

         function Map_Of (W : W_Array) return Byte_Array is
           ([for J in 0 .. Map_Len - 1 => Message (W, 7 + J)]);
      begin
         if Positive_Case then
            --  The hypotheses hold, and the lemmas run: their
            --  preconditions and assertions are checked.
            Report ("hypotheses " & Name & ": H_Matching_By_Content",
                    Matching_Holds (Map_Of (W0.all), P, It, Item_Digest (W0.all)));
            Report ("hypotheses " & Name & ": H_Types_In_Item",
                    Types_Hold (Item_Bytes (W0.all), It));
            declare
               V  : constant R.Private_Part := R.Decode_Private (W0.all)
               with Ghost;
               Pp : constant R.Public_Part := R.Decode_Public (X0.all)
               with Ghost;
               N  : constant Natural := Mdoc_Parse.Message_Length (P);
            begin
               R.Lemma_Count_In_Range (X0.all, W0.all);
               R.Lemma_Item_No_Wrap (Pp, V);
               for K in 0 .. 4_095 loop
                  HC.Fact_Padding (V, N, K);
               end loop;
               Report ("lemmas " & Name & ": "
                       & "Lemma_Count_In_Range, Lemma_Item_No_Wrap, "
                       & "Fact_Padding at every index", True);
            exception
               when E : Ada.Assertions.Assertion_Error =>
                  Report ("lemmas " & Name & ": "
                          & Ada.Exceptions.Exception_Message (E), False);
            end;
         end if;

         if Mutate then
            for M in Mutation loop
               X.all := X0.all;
               W.all := W0.all;
               case M is
                  when M_Bits =>
                     W (W_Count) := (Limbs => [0 => 2, 1 => 0]);
                  when M_Chain =>
                     Flip (W.all, W_E);
                     Retag (X.all, W.all, Ap, Av);
                  when M_Zero_Tail =>
                     --  The first byte of block nb; a count of 40 leaves
                     --  no block after it, and the byte past the
                     --  windows is changed instead.
                     Put_Message (W.all, Natural'Min (64 * Nb, 64 * Max_Blocks - 1)
                                         - Prefix_Length, 1);
                     Retrace (W.all);
                     Retag (X.all, W.all, Ap, Av);
                  when M_Length =>
                     Put_Message (W.all, 64 * Nb - 1 - Prefix_Length,
                                  Preimage (W0.all, 64 * Nb - 1) + 1);
                     Retrace (W.all);
                     Retag (X.all, W.all, Ap, Av);
                  when M_Valid_From =>
                     Put_Index (W.all, W_Valid_From, VF + 1);
                  when M_Valid_Until =>
                     Put_Index (W.all, W_Valid_Until, 4_095);
                  when M_Device_Key =>
                     Flip (W.all, W_Dpk_X);
                     Retag (X.all, W.all, Ap, Av);
                  when M_Value_Digests =>
                     Put_Index (W.all, W_Value_Digests, VD + 1);
                  when M_Value_Digest =>
                     Put_Index (W.all, W_Digest_Index, DI + 1);
                  when M_Item_Slot =>
                     Put_Index (W.all, W_Slot_Lengths,
                                Index_Of (W0.all, W_Slot_Lengths) + 1);
                  when M_Item_Map =>
                     --  Byte 4, the map's head, A5 for A4: the item's
                     --  digest, the message, its traces and e follow.
                     Put_Byte (W.all, W_Item + 8 * 4, 16#A5#);
                     Place_Item_Digest (W.all);
                     Retrace (W.all);
                     Retag (X.all, W.all, Ap, Av);
                  when M_Tags =>
                     X (X_Tags) := GF2_128.Add (X (X_Tags), GF2_128.One);
                  when M_Id_Len =>
                     Put_Byte (X.all, X_Id_Len, Byte_Of (X0.all, X_Id_Len) + 1);
               end case;
               Check ("mutation " & M'Image & " " & Name, X.all, W.all, Fails,
                      Trim (Target_Of (M), Ada.Strings.Right));
            end loop;
         end if;

         if Reference then
            --  attr_ei_ and attr_ev_, bits the circuit does not read at
            --  version 7.
            X.all := X0.all;
            W.all := W0.all;
            Flip (W.all, W_Ei);
            Check ("neutral attr_ei " & Name, X.all, W.all, Neutral);
            W.all := W0.all;
            Flip (W.all, W_Ev + 3);
            Check ("neutral attr_ev " & Name, X.all, W.all, Neutral);
            --  Other pads and another challenge, the tags recomputed.
            W.all := W0.all;
            Retag (X.all, W.all,
                   [for I in Mdoc_Mac.Message_Index =>
                      [for H in Mdoc_Mac.Half_Index =>
                         (Limbs => [0 => Unsigned_64 (77 + 5 * I + H),
                                    1 => 16#3C3C#])]],
                   (Limbs => [0 => 16#BEEF#, 1 => 16#CAFE#]));
            Check ("neutral pads and av " & Name, X.all, W.all, Neutral);
            --  Byte 3 of the item, the length of its byte string.
            X.all := X0.all;
            W.all := W0.all;
            Put_Byte (W.all, W_Item + 8 * 3, Item_Byte (W0.all, 3) + 1);
            Place_Item_Digest (W.all);
            Retrace (W.all);
            Retag (X.all, W.all, Ap, Av);
            Check ("neutral item byte 3 " & Name, X.all, W.all, Neutral);
            --  The size of the map after valueDigests.
            X.all := X0.all;
            W.all := W0.all;
            Put_Message (W.all, 7 + VD + 13, Message (W0.all, 7 + VD + 13) xor 1);
            Retrace (W.all);
            Retag (X.all, W.all, Ap, Av);
            Check ("neutral valueDigests map size " & Name, X.all, W.all,
                   Neutral);

            --  H_Matching_By_Content: a second validUntil, in the 32
            --  bytes of a value digest that is not the requested one,
            --  dated 9999; now in 2099, past the real validUntil.
            declare
               Fake  : constant Byte_Array (0 .. 31) :=
                 Valid_Until_Key & To_Bytes ("9999-12-31T23:59:59");
               Late  : constant Date := To_Bytes ("2099-01-01T00:00:00Z");
               J     : Natural := VD + 13;
               Found : Boolean := False;

               --  The 34 bytes from J clear of the windows the honest
               --  witness reads.
               function Clear (Start, Len : Natural) return Boolean is
                 (J + 34 <= Start or else J >= Start + Len);
            begin
               while J + 34 < Map_Len loop
                  if Message (W0.all, 7 + J) = 16#58#
                    and then Message (W0.all, 8 + J) = 16#20#
                    and then Clear (DI, 34) and then Clear (DK, 100)
                    and then Clear (VF, 32) and then Clear (VU, 33)
                  then
                     Found := True;
                     exit;
                  end if;
                  J := J + 1;
               end loop;
               if not Found then
                  Report ("synthetic second validUntil " & Name
                          & ": no other value digest", False);
               else
                  X.all := X0.all;
                  W.all := W0.all;
                  for I in Fake'Range loop
                     Put_Message (W.all, 7 + J + 2 + I, Fake (I));
                  end loop;
                  Retrace (W.all);
                  Retag (X.all, W.all, Ap, Av);
                  Put_Index (W.all, W_Valid_Until, J + 2);
                  for I in Late'Range loop
                     Put_Byte (X.all, X_Now + 8 * I, Late (I));
                  end loop;
                  Check ("synthetic second validUntil " & Name, X.all, W.all,
                         Synthetic);
                  Report ("synthetic second validUntil " & Name
                          & ": H_Matching_By_Content is false",
                          not Matching_Holds (Map_Of (W.all), P, It,
                                              Item_Digest (W.all)));
               end if;
            end;

            --  H_Types_In_Item: random as a text string of the same
            --  length (major type 3 for 2).
            X.all := X0.all;
            W.all := W0.all;
            declare
               H : constant Natural := Random_Start (W0.all) + 7;
            begin
               Put_Byte (W.all, W_Item + 8 * H, Item_Byte (W0.all, H) + 16#20#);
            end;
            Place_Item_Digest (W.all);
            Retrace (W.all);
            Retag (X.all, W.all, Ap, Av);
            Check ("synthetic random as text " & Name, X.all, W.all, Synthetic);
            Report ("synthetic random as text " & Name
                    & ": H_Types_In_Item is false",
                    not Types_Hold (Item_Bytes (W.all), It));
         end if;

         if Padding then
            --  H_Matching_By_Content: a digest whose window runs into
            --  the SHA-256 padding. The map's last 33 bytes become 58 20
            --  and the first 31 bytes of the digest of an item whose
            --  digest ends with 16#80#, the padding's first byte: found
            --  by trial over two bytes of random. The last 33 bytes
            --  must be clear of every window the honest witness reads.
            declare
               K     : constant Natural := Map_Len - 33;
               R     : constant Natural := Random_Start (W0.all) + 9;
               D     : Bytes_32;
               T     : Natural := 0;

               function Clear (Start, Len : Natural) return Boolean is
                 (K + 33 <= Start or else K >= Start + Len);
            begin
               if not (Clear (DI, 34) and then Clear (DK, 100)
                       and then Clear (VF, 32) and then Clear (VU, 33)
                       and then Clear (VD, 13))
               then
                  Report ("synthetic digest across the padding " & Name
                          & ": the map's end is read by a window", False);
               else
                  X.all := X0.all;
                  W.all := W0.all;
                  loop
                     Put_Byte (W.all, W_Item + 8 * R, Unsigned_8 (T mod 256));
                     Put_Byte (W.all, W_Item + 8 * (R + 1),
                               Unsigned_8 (T / 256));
                     D := Item_Digest (W.all);
                     exit when D (31) = 16#80# or else T = 65_535;
                     T := T + 1;
                  end loop;
                  Put_Message (W.all, 7 + K, 16#58#);
                  Put_Message (W.all, 7 + K + 1, 16#20#);
                  for J in 0 .. 30 loop
                     Put_Message (W.all, 7 + K + 2 + J, D (J));
                  end loop;
                  Put_Index (W.all, W_Digest_Index, K);
                  Retrace (W.all);
                  Retag (X.all, W.all, Ap, Av);
                  Check ("synthetic digest across the padding " & Name,
                         X.all, W.all, Synthetic);
                  Report ("synthetic digest across the padding " & Name
                          & ": H_Matching_By_Content is false",
                          not Matching_Holds (Map_Of (W.all), P, It, D));
               end if;
            end;
         end if;
      end;

      --  "count": the block count outside 1 to 40 (nb is eight bits,
      --  and the circuit does not assert nb <= 40). The rest of the
      --  honest witness is kept: the relation is false (it implies nb in
      --  1 to 40, Lemma_Count_In_Range), and the circuit must refuse.
      --  Locate says which of its assertions fail.
      if Count then
         for Nb_New of Count_Values loop
            X.all := X0.all;
            W.all := W0.all;
            Put_Byte (W.all, W_Count, Nb_New);
            declare
               L : constant String := "count nb =" & Nb_New'Image & " " & Name;
               Hits  : Hit_Array;
               Other : Natural;
            begin
               Check (L, X.all, W.all, Fails);
               Locate (L, X.all, W.all, Hits, Other);
               --  The fact of G1 on the registered circuit: the 256
               --  outputs of the unpacking of the 64 zero elements are
               --  the constant terms, 64 of each, none of them a bit.
               --  The other squares read are 256, as many as the failing
               --  comparisons of assert_hash: a count, not a mapping of
               --  each read to its assertion.
               Report (L & ": the plucker's outputs on 0 are the four"
                       & " constant terms, 64 of each",
                       Hits = [Gadgets.Bits.Pluck_Index => 64]);
               Report (L & ": the other squares read are 256, as many"
                       & " as the comparisons of assert_hash (a count)",
                       Other = 256);
            end;
         end loop;
      end if;

      Free (Doc);
      Free (Tr);
      Free (X0);
      Free (W0);
      Free (X);
      Free (W);
   end Run_Document;

   ----------------------------------------------------------------------
   --  The list
   ----------------------------------------------------------------------

   Hdr : CR.Header;
   CSt : Circuit_Status.Status;
   F   : Ada.Text_IO.File_Type;
begin
   if Argument_Count /= 3 then
      raise Usage;
   end if;
   Report ("the harness's layout is the package's", Layout_Agrees);
   declare
      B : Byte_Access := Read_File (Argument (1));
   begin
      CR.Read_Packed (B.all, False, [others => 0], Circuit, Hdr, CSt);
      Free (B);
   end;
   if CSt /= Circuit_Status.Ok then
      Put_Line ("FAIL the circuit: " & CSt'Image);
      Set_Exit_Status (1);
      return;
   end if;
   Open (F, In_File, Argument (2));
   while not End_Of_File (F) loop
      declare
         L : constant String := Trim (Get_Line (F), Ada.Strings.Both);
         S1, S2, S3 : Natural;
      begin
         if L'Length > 0 and then L (L'First) /= '#' then
            S1 := Index (L, " ");
            S2 := Index (L (S1 + 1 .. L'Last), " ");
            S3 := Index (L (S2 + 1 .. L'Last), " ");
            declare
               Name : constant String := L (L'First .. S1 - 1);
               Attr : constant String := L (S1 + 1 .. S2 - 1);
               Want : constant String :=
                 (if S3 = 0 then L (S2 + 1 .. L'Last) else L (S2 + 1 .. S3 - 1));
               Rest : constant String :=
                 (if S3 = 0 then "" else L (S3 + 1 .. L'Last));
               --  rename=<identifier>: the synthetic document of
               --  Renamed (the identifiers of 24 characters or more).
               R_At : constant Natural := Index (Rest, "rename=");
               R_To : constant Natural :=
                 (if R_At = 0 then 0
                  elsif Index (Rest (R_At .. Rest'Last), " ") = 0
                  then Rest'Last
                  else Index (Rest (R_At .. Rest'Last), " ") - 1);
            begin
               Run_Document
                 (Argument (3), Name, Attr,
                  Positive_Case => Want = "holds",
                  Mutate        => Index (Rest, "mutate") > 0,
                  Reference     => Index (Rest, "reference") > 0,
                  Padding       => Index (Rest, "padding") > 0,
                  Count         => Index (Rest, "count") > 0,
                  Rename        =>
                    (if R_At = 0 then "" else Rest (R_At + 7 .. R_To)));
            end;
         end if;
      end;
   end loop;
   Close (F);
   Put_Line ("relation_cases:" & Cases'Image & " cases," & Failures'Image
             & " failures," & Weaker'Image
             & " where the circuit refuses and the relation holds");
   Set_Exit_Status (if Failures = 0 then Success else Ada.Command_Line.Failure);
exception
   when Usage =>
      Put_Line ("usage: relation_cases <hash circuit> <cases file> <testcases dir>");
      Set_Exit_Status (2);
end Relation_Cases;
