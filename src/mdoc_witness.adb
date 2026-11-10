pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Sha256;
with Sha256.Trace;
with P256_Curve;
with Q256_Field;

package body Mdoc_Witness is

   subtype Nat_256 is Ecdsa_Witness.Nat_256;

   -------------------------------------------------------------------
   --  The values
   -------------------------------------------------------------------

   function Reversed (B : Bytes_32) return Bytes_32 is
     ([for I in Bytes_32'Range => B (31 - I)]);

   function Nat_Of (B : Bytes_32) return Nat_256 is
     (P256_Field.Limbs_Of_Bytes (Reversed (B)));

   function Messages (P : Parsed_Mdoc) return Mdoc_Mac.Messages is
     ([0 => Reversed (P.Issuer_Sig_Digest),
       1 => Reversed (P.Device_Pk_X),
       2 => Reversed (P.Device_Pk_Y)]);

   --  A word as an element: four words below p, canonical.
   function Of_Word (X : Unsigned_64) return P256_Field.Element is
     (P256_Field.From_Canonical ([0 => X, 1 => 0, 2 => 0, 3 => 0]))
   with Global => null;

   Two_64 : constant P256_Field.Element :=
     P256_Field.From_Canonical ([0 => 0, 1 => 1, 2 => 0, 3 => 0]);

   function Reduce (N : Nat_256) return P256_Field.Element is
      E : P256_Field.Element := Of_Word (N (3));
   begin
      --  Horner over the words: ((n3 2^64 + n2) 2^64 + n1) 2^64 + n0.
      E := P256_Field.Add (P256_Field.Mul (E, Two_64), Of_Word (N (2)));
      E := P256_Field.Add (P256_Field.Mul (E, Two_64), Of_Word (N (1)));
      E := P256_Field.Add (P256_Field.Mul (E, Two_64), Of_Word (N (0)));
      return E;
   end Reduce;

   -------------------------------------------------------------------
   --  The encodings of the hash witness (builder.rs)
   -------------------------------------------------------------------

   subtype Hash_Array is SAH.Element_Array;

   --  Bit K of V as an element: the low limb is the bit, zero or one.
   function Bit (V : Unsigned_64; K : Natural) return GF2_128.Element is
     (Limbs => [0 => Shift_Right (V, K) and 1, 1 => 0])
   with Global => null, Pre => K <= 63;

   --  The N low bits of V, least significant first, at Pos, each as
   --  Bit, without a branch on the bit (ADR 0051: the bits are secret).
   --  Gold: element Pos'Old + K is bit K.
   procedure Put_Bits
     (W   : in out Hash_Array;
      Pos : in out Natural;
      V   : Unsigned_64;
      N   : Natural)
   with
     Global => null,
     Pre    => N <= 64 and then Pos >= W'First and then Pos <= W'Last + 1
               and then W'Last - Pos + 1 >= N,
     Post   => Pos = Pos'Old + N
               and then (for all K in 0 .. N - 1 =>
                           W (Pos'Old + K) = Bit (V, K))
   is
   begin
      for K in 0 .. N - 1 loop
         pragma Loop_Invariant (Pos = Pos'Loop_Entry + K);
         pragma Loop_Invariant
           (for all L in 0 .. K - 1 => W (Pos'Loop_Entry + L) = Bit (V, L));
         W (Pos) := Bit (V, K);
         Pos := Pos + 1;
      end loop;
   end Put_Bits;

   --  The bytes of B, eight bits each (push_raw_bytes).
   procedure Put_Bytes
     (W : in out Hash_Array; Pos : in out Natural; B : Byte_Array)
   with
     Global => null,
     Pre    => Pos >= W'First and then Pos <= W'Last + 1
               and then B'Length <= Natural'Last / 8
               and then W'Last - Pos + 1 >= 8 * B'Length,
     Post   => Pos = Pos'Old + 8 * B'Length
   is
   begin
      for I in B'Range loop
         pragma Loop_Invariant (Pos = Pos'Loop_Entry + 8 * (I - B'First));
         Put_Bits (W, Pos, Unsigned_64 (B (I)), 8);
      end loop;
   end Put_Bytes;

   --  Chunk K of the word X in the legacy plucked form: the 4-bit
   --  chunk c as the subfield element of bits (c << 1) xor 15.
   function Chunk (X : Unsigned_32; K : Natural) return GF2_128.Element is
     (GF2_128.Inject
        (GF2_128.Subfield_Value
           (Shift_Left (Shift_Right (X, 4 * K) and 15, 1) xor 15)))
   with Global => null, Pre => K <= 7;

   --  A 32-bit word in the legacy plucked form (push_v32_legacy): the
   --  eight chunks, least significant first. Gold: element Pos'Old + K
   --  is Chunk K.
   procedure Put_V32_Legacy
     (W : in out Hash_Array; Pos : in out Natural; X : Unsigned_32)
   with
     Global => null,
     Pre    => Pos >= W'First and then Pos <= W'Last + 1
               and then W'Last - Pos + 1 >= 8,
     Post   => Pos = Pos'Old + 8
               and then (for all K in 0 .. 7 =>
                           W (Pos'Old + K) = Chunk (X, K))
   is
   begin
      for K in 0 .. 7 loop
         pragma Loop_Invariant (Pos = Pos'Loop_Entry + K);
         pragma Loop_Invariant
           (for all L in 0 .. K - 1 =>
              W (Pos'Loop_Entry + L) = Chunk (X, L));
         W (Pos) := Chunk (X, K);
         Pos := Pos + 1;
      end loop;
   end Put_V32_Legacy;

   --  One block's trace in the legacy order: w[16 .. 63], then (e_i,
   --  a_i) for the 64 rounds, then the eight words of the new state.
   procedure Put_Block
     (W   : in out Hash_Array;
      Pos : in out Natural;
      T   : Sha256.Trace.Block_Trace;
      H   : Sha256.State)
   with
     Global => null,
     Pre    => Pos >= W'First and then Pos <= W'Last + 1
               and then W'Last - Pos + 1 >= Block_Elements,
     Post   => Pos = Pos'Old + Block_Elements
   is
   begin
      for I in 0 .. 47 loop
         pragma Loop_Invariant (Pos = Pos'Loop_Entry + 8 * I);
         Put_V32_Legacy (W, Pos, T.W (I));
      end loop;
      for I in 0 .. 63 loop
         pragma Loop_Invariant (Pos = Pos'Loop_Entry + 16 * I);
         Put_V32_Legacy (W, Pos, T.E (I));
         Put_V32_Legacy (W, Pos, T.A (I));
      end loop;
      for I in Sha256.Word_Index loop
         pragma Loop_Invariant
           (Pos = Pos'Loop_Entry + 8 * Natural (I));
         Put_V32_Legacy (W, Pos, H (I));
      end loop;
   end Put_Block;

   --  The head of a CBOR string in the request's value (val_header_len
   --  of private.rs): a tag 24 over a string, a text or a byte string
   --  with a head of one to three bytes, else none.
   function Value_Header_Len (V : Byte_Array) return Natural with
     Global => null, Post => Value_Header_Len'Result <= 5
   is
   begin
      if V'Length = 0 then
         return 0;
      end if;
      case V (V'First) is
         when 16#D9# =>
            if V'Length > 3
              and then (V (V'First + 3) = 16#78#
                        or else V (V'First + 3) = 16#58#)
            then
               return 5;
            else
               return 4;
            end if;
         when 16#60# .. 16#77# | 16#40# .. 16#57# => return 1;
         when 16#78# | 16#58# => return 2;
         when 16#79# | 16#59# => return 3;
         when others => return 0;
      end case;
   end Value_Header_Len;

   -------------------------------------------------------------------
   --  The hash witness
   -------------------------------------------------------------------

   procedure Hash_Witness
     (Version : Version_Number;
      Mdoc    : Byte_Array;
      P       : Parsed_Mdoc;
      Attrs   : Attribute_List;
      Ap      : Mdoc_Mac.Pads;
      W       : out SAH.Element_Array;
      Result  : out Status)
   is
      MB     : constant Positive := Mso_Blocks (Version);
      M      : constant Mdoc_Mac.Messages := Messages (P);
      Pos    : Natural := 0;
      Msg    : Byte_Array (0 .. Mdoc_Parse.Max_Message - 1);
      Len    : Natural;
      Padded : Byte_Array (0 .. 64 * MB - 1);
      NB     : Sha256.Trace.Block_Count;
      H      : Sha256.State;
      T      : Sha256.Trace.Block_Trace;
   begin
      W := [others => GF2_128.Zero];
      Result := Ok;
      --  1. The three bound values, 768 bits.
      for I in Mdoc_Mac.Message_Index loop
         pragma Loop_Invariant (Pos = 256 * I);
         Put_Bytes (W, Pos, M (I));
      end loop;
      --  2. The signed message, padded into the capacity; its block
      --  count, then its bytes from the 18th.
      Mdoc_Parse.Signed_Message (Mdoc, P, Msg, Len);
      Sha256.Trace.Pad_Message (Msg (0 .. Len - 1), MB, Padded, NB);
      Put_Bits (W, Pos, Unsigned_64 (NB), 8);
      Put_Bytes (W, Pos, Padded (18 .. 64 * MB - 1));
      --  3. The trace of every block of the capacity.
      H := Sha256.Initial_State;
      for B in 0 .. MB - 1 loop
         pragma Loop_Invariant
           (Pos = 768 + 8 + (64 * MB - 18) * 8 + B * Block_Elements);
         Sha256.Trace.Compress_Traced (H, Padded, 64 * B, T);
         Put_Block (W, Pos, T, H);
      end loop;
      --  4. The four offsets.
      Put_Bits (W, Pos, Unsigned_64 (P.Valid_From_Offset), 12);
      Put_Bits (W, Pos, Unsigned_64 (P.Valid_Until_Offset), 12);
      Put_Bits (W, Pos, Unsigned_64 (P.Device_Key_Info_Offset), 12);
      Put_Bits (W, Pos, Unsigned_64 (P.Value_Digests_Offset), 12);
      --  5. The requested attributes.
      for A in Attrs'Range loop
         pragma Loop_Invariant
           (Pos = 768 + 8 + (64 * MB - 18) * 8 + MB * Block_Elements + 48
                  + (A - Attrs'First) * Per_Attribute (Version));
         declare
            Req   : Mdoc_Inputs.Attribute renames Attrs (A);
            I    : constant Mdoc_Parse.Item_Count :=
              Mdoc_Parse.Find_Item (Mdoc, P, Req.Id (0 .. Req.Id_Len - 1));
            Pad2 : Byte_Array (0 .. 127);
            NB2  : Sha256.Trace.Block_Count;
            H2   : Sha256.State := Sha256.Initial_State;
            T2   : Sha256.Trace.Block_Trace;
            Ei_Pos, Ei_Len, Ev_Pos, Ev_Len : Natural;
            Slot_Ei, Slot_Ev : Mdoc_Parse.Slot_Index;
            Hdr, Val_Len : Natural;
         begin
            if I = 0 then
               W := [others => GF2_128.Zero];
               Result := Attribute_Not_Found;
               return;
            end if;
            declare
               It : Mdoc_Parse.Item renames P.Items (I);
            begin
               if It.Item_Len > Max_Item_Bytes then
                  W := [others => GF2_128.Zero];
                  Result := Attribute_Too_Long;
                  return;
               end if;
               --  The item into two blocks, as bits, then its two traces.
               Sha256.Trace.Pad_Message
                 (Mdoc (Mdoc'First + It.Item_Start
                        .. Mdoc'First + It.Item_Start + It.Item_Len - 1),
                  2, Pad2, NB2);
               Put_Bytes (W, Pos, Pad2);
               for B in 0 .. 1 loop
                  pragma Loop_Invariant
                    (Pos = Pos'Loop_Entry + B * Block_Elements);
                  Sha256.Trace.Compress_Traced (H2, Pad2, 64 * B, T2);
                  Put_Block (W, Pos, T2, H2);
               end loop;
               Put_Bits (W, Pos, Unsigned_64 (It.Digest_Offset), 12);
               --  The locator of the identifier and of the value.
               Slot_Ei := Mdoc_Parse.Slot_Index ((It.Permutation / 16) mod 4);
               Slot_Ev := Mdoc_Parse.Slot_Index ((It.Permutation / 64) mod 4);
               if Version < 7 then
                  Hdr := Value_Header_Len (Req.Value (0 .. Req.Value_Len - 1));
                  Val_Len := (if Req.Value_Len >= Hdr
                              then Req.Value_Len - Hdr else 0);
                  Ei_Pos := It.Slot (Slot_Ei) + 18;
                  Ei_Len := Req.Id_Len + Val_Len + 13;
                  Ev_Pos := It.Slot (Slot_Ev) + 1;
                  Ev_Len := Val_Len;
               else
                  Ei_Pos := It.Slot (Slot_Ei);
                  Ei_Len := It.Length (Slot_Ei);
                  Ev_Pos := It.Slot (Slot_Ev);
                  Ev_Len := It.Length (Slot_Ev);
               end if;
               Put_Bits (W, Pos, Unsigned_64 (Ei_Pos), 12);
               Put_Bits (W, Pos, Unsigned_64 (Ei_Len), 12);
               Put_Bits (W, Pos, Unsigned_64 (Ev_Pos), 12);
               Put_Bits (W, Pos, Unsigned_64 (Ev_Len), 12);
               if Version = 7 then
                  for S in Mdoc_Parse.Slot_Index range 1 .. 3 loop
                     pragma Loop_Invariant
                       (Pos = Pos'Loop_Entry + 12 * (Natural (S) - 1));
                     Put_Bits (W, Pos, Unsigned_64 (It.Slot (S)), 12);
                  end loop;
                  for S in Mdoc_Parse.Slot_Index loop
                     pragma Loop_Invariant
                       (Pos = Pos'Loop_Entry + 12 * Natural (S));
                     Put_Bits (W, Pos, Unsigned_64 (It.Length (S)), 12);
                  end loop;
                  Put_Bits (W, Pos, Unsigned_64 (It.Permutation), 8);
               end if;
            end;
         end;
      end loop;
      --  6. The six pads.
      for I in Mdoc_Mac.Message_Index loop
         pragma Loop_Invariant (Pos = W'Length - 6 + 2 * I);
         pragma Loop_Invariant
           (for all J in 0 .. I - 1 =>
              (for all H in Mdoc_Mac.Half_Index =>
                 W (W'Last - 5 + 2 * J + H) = Ap (J) (H)));
         W (Pos) := Ap (I) (0);
         W (Pos + 1) := Ap (I) (1);
         Pos := Pos + 2;
      end loop;
      pragma Assert (Pos = W'Length);
   end Hash_Witness;

   -------------------------------------------------------------------
   --  The signature witness
   -------------------------------------------------------------------

   --  Pair K of the 128-bit value of two words, least significant
   --  first, as the element 2 v - 3 of the pair v.
   function Pair (Lo, Hi : Unsigned_64; K : Natural) return P256_Field.Element
   is (Mdoc_Inputs.Plucked
         (Natural (Shift_Right ((if K < 32 then Lo else Hi),
                                2 * (K mod 32)) and 3)))
   with Global => null, Pre => K <= 63;

   --  The 64 pairs of a 128-bit value (push_plucked_128_legacy). Gold:
   --  element Pos'Old + K is Pair K.
   procedure Put_Plucked_128
     (W      : in out SAP.Element_Array;
      Pos    : in out Natural;
      Lo, Hi : Unsigned_64)
   with
     Global => null,
     Pre    => Pos >= W'First and then Pos <= W'Last + 1
               and then W'Last - Pos + 1 >= 64,
     Post   => Pos = Pos'Old + 64
               and then (for all K in 0 .. 63 =>
                           W (Pos'Old + K) = Pair (Lo, Hi, K))
   is
   begin
      for K in 0 .. 63 loop
         pragma Loop_Invariant (Pos = Pos'Loop_Entry + K);
         pragma Loop_Invariant
           (for all L in 0 .. K - 1 =>
              W (Pos'Loop_Entry + L) = Pair (Lo, Hi, L));
         W (Pos) := Pair (Lo, Hi, K);
         Pos := Pos + 1;
      end loop;
   end Put_Plucked_128;

   procedure Sig_Witness
     (Mdoc       : Byte_Array;
      P          : Parsed_Mdoc;
      Pk_X, Pk_Y : P256_Field.Element;
      Ap         : Mdoc_Mac.Pads;
      W          : out SAP.Element_Array;
      Result     : out Status)
   is
      pragma Unreferenced (Mdoc);
      E_I  : constant Nat_256 := Nat_Of (P.Issuer_Sig_Digest);
      R_I  : constant Nat_256 := Nat_Of (P.Issuer_Sig_R);
      S_I  : constant Nat_256 := Nat_Of (P.Issuer_Sig_S);
      E_D  : constant Nat_256 := Nat_Of (P.Device_Sig_Digest);
      R_D  : constant Nat_256 := Nat_Of (P.Device_Sig_R);
      S_D  : constant Nat_256 := Nat_Of (P.Device_Sig_S);
      X_N  : constant Nat_256 := Nat_Of (P.Device_Pk_X);
      Y_N  : constant Nat_256 := Nat_Of (P.Device_Pk_Y);
      Dev  : constant P256_Curve.Affine_Point :=
        (X => Reduce (X_N), Y => Reduce (Y_N));
      Pos  : Natural;
   begin
      W := [others => P256_Field.Zero];
      Result := Ok;
      --  Both values are checked before the one branch, so that the
      --  work does not say which signature failed (ADR 0051).
      if not (Q256_Field.Is_Canonical (Ecdsa_Witness.To_Q (S_I))
              and Q256_Field.Is_Canonical (Ecdsa_Witness.To_Q (S_D)))
      then
         Result := Signature_Not_Canonical;
         return;
      end if;
      --  The three bound values reduced into the field.
      W (0) := Reduce (E_I);
      W (1) := Dev.X;
      W (2) := Dev.Y;
      --  The two ECDSA witnesses.
      Ecdsa_Witness.Push_Legacy ((X => Pk_X, Y => Pk_Y), E_I, R_I, S_I, W, 3);
      Ecdsa_Witness.Push_Legacy
        (Dev, E_D, R_D, S_D, W, 3 + Ecdsa_Witness.Count);
      --  The pads and the halves of the three values, two bits each.
      Pos := 3 + 2 * Ecdsa_Witness.Count;
      declare
         Vals : constant array (Mdoc_Mac.Message_Index) of Nat_256 :=
           [E_I, X_N, Y_N];
      begin
         for I in Mdoc_Mac.Message_Index loop
            pragma Loop_Invariant
              (Pos = 3 + 2 * Ecdsa_Witness.Count + 256 * I);
            Put_Plucked_128
              (W, Pos, Ap (I) (0).Limbs (0), Ap (I) (0).Limbs (1));
            Put_Plucked_128
              (W, Pos, Ap (I) (1).Limbs (0), Ap (I) (1).Limbs (1));
            Put_Plucked_128 (W, Pos, Vals (I) (0), Vals (I) (1));
            Put_Plucked_128 (W, Pos, Vals (I) (2), Vals (I) (3));
         end loop;
      end;
      pragma Assert (Pos = Sig_Count);
   end Sig_Witness;

end Mdoc_Witness;
