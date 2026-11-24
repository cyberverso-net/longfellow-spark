pragma SPARK_Mode (On);

package body Mdoc_Relation.Hash is

   -------------------
   -- Lemma_Byte_At --
   -------------------

   --  Bit by bit, in Unsigned_8 where the provers reason on bit
   --  vectors: element B counts 2 ** B exactly when bit B of V is set,
   --  and V is the sum of its bits.
   procedure Lemma_Byte_At
     (A : SAH.Element_Array; Pos : Natural; V : Unsigned_8)
   is
   begin
      pragma Assert (GF2_128.One /= GF2_128.Zero);
      pragma Assert
        (A (Pos) = (if (V and 1) /= 0 then GF2_128.One else GF2_128.Zero));
      pragma Assert
        (A (Pos + 1) =
           (if (V and 2) /= 0 then GF2_128.One else GF2_128.Zero));
      pragma Assert
        (A (Pos + 2) =
           (if (V and 4) /= 0 then GF2_128.One else GF2_128.Zero));
      pragma Assert
        (A (Pos + 3) =
           (if (V and 8) /= 0 then GF2_128.One else GF2_128.Zero));
      pragma Assert
        (A (Pos + 4) =
           (if (V and 16) /= 0 then GF2_128.One else GF2_128.Zero));
      pragma Assert
        (A (Pos + 5) =
           (if (V and 32) /= 0 then GF2_128.One else GF2_128.Zero));
      pragma Assert
        (A (Pos + 6) =
           (if (V and 64) /= 0 then GF2_128.One else GF2_128.Zero));
      pragma Assert
        (A (Pos + 7) =
           (if (V and 128) /= 0 then GF2_128.One else GF2_128.Zero));
      pragma Assert (Bit_Value (A (Pos)) = (V and 1));
      pragma Assert (2 * Bit_Value (A (Pos + 1)) = (V and 2));
      pragma Assert (4 * Bit_Value (A (Pos + 2)) = (V and 4));
      pragma Assert (8 * Bit_Value (A (Pos + 3)) = (V and 8));
      pragma Assert (16 * Bit_Value (A (Pos + 4)) = (V and 16));
      pragma Assert (32 * Bit_Value (A (Pos + 5)) = (V and 32));
      pragma Assert (64 * Bit_Value (A (Pos + 6)) = (V and 64));
      pragma Assert (128 * Bit_Value (A (Pos + 7)) = (V and 128));
      pragma Assert
        (V = (V and 1) + (V and 2) + (V and 4) + (V and 8) + (V and 16)
             + (V and 32) + (V and 64) + (V and 128));
   end Lemma_Byte_At;

   --------------------------
   -- Lemma_Count_In_Range --
   --------------------------

   --  Only the clause Value_Digests is used: its index is below the
   --  signed length in bytes, so that length is not zero, and a count
   --  outside 1 to 40 gives zero. The definitions of the other clauses
   --  and of the decodings are hidden: they are not needed, and with
   --  them in the context the provers did not reach the step from
   --  Clause_Holds to Value_Digests.
   procedure Lemma_Count_In_Range (X, W : SAH.Element_Array) is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Decode_Public);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Decode_Private);
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Bits);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Chain);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Zero_Tail);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Length);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Valid_From);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Valid_Until);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Device_Key);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Value_Digest);
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Item);
      pragma Annotate (GNATprove, Hide_Info, "Expression_Function_Body", Tags);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Matches);
      P : constant Public_Part := Decode_Public (X);
      V : constant Private_Part := Decode_Private (W);
   begin
      pragma Assert (Clauses_Hold (P, V));
      pragma Assert (Clause_Holds (Value_Digests_Clause, P, V));
      pragma Assert (Value_Digests (V));
      pragma Assert (Index_Bound (V, V.Value_Digests));
      pragma Assert (Byte_Length (Signed_Length (V)) > 0);
      pragma Assert (Signed_Length (V) /= 0);
   end Lemma_Count_In_Range;

   ------------------------
   -- Lemma_Item_No_Wrap --
   ------------------------

   --  The field the permutation puts in slot S, when the slots are
   --  distinct.
   function Field_At (V : Private_Part; S : Slot) return Field is
     (if Slot_Of (V, 0) = S then 0
      elsif Slot_Of (V, 1) = S then 1
      elsif Slot_Of (V, 2) = S then 2
      else 3)
   with Global => null;

   --  A length that cannot carry a start below 128 past 4,096: at most
   --  264, or at most 128 modulo 256.
   function Short (L : Index_12) return Boolean is
     (L >= 1 and then (L <= 264 or else L mod 256 in 1 .. 128))
   with Global => null;

   procedure Lemma_Item_No_Wrap (P : Public_Part; V : Private_Part) is
   begin
      --  The first byte of each field is its key's.
      pragma Assert (Got (V, Digest_Id_Field, 0) = 16#68#);
      pragma Assert (Got (V, Random_Field, 0) = 16#66#);
      pragma Assert (Want_Identifier (P, 0) = 16#71#);
      pragma Assert (Got (V, Identifier_Field, 0) = 16#71#);
      pragma Assert (Want_Value (P, 0) = 16#6C#);
      pragma Assert (Got (V, Value_Field, 0) = 16#6C#);

      --  So every field starts inside the item, in its own slot.
      pragma Assert (for all F in Field => Field_Start (V, F) < 128);
      pragma Assert (Slots_Distinct (V));
      pragma Assert
        (for all S in Slot => Slot_Of (V, Field_At (V, S)) = S);
      pragma Assert (for all S in Slot => V.Starts (S) < 128);

      --  The lengths, field by field, then slot by slot.
      pragma Assert (Field_Length (V, Digest_Id_Field) in 10 .. 14);
      pragma Assert (Field_Length (V, Random_Field) in 8 .. 264);
      pragma Assert
        (Field_Length (V, Identifier_Field) mod 256 = Natural (P.Id_Len));
      pragma Assert
        (Field_Length (V, Value_Field) mod 256 = Natural (P.Value_Len));
      pragma Assert (for all F in Field => Short (Field_Length (V, F)));
      pragma Assert
        (for all S in Slot =>
           V.Lengths (S) = Field_Length (V, Field_At (V, S)));
      pragma Assert (for all S in Slot => Short (V.Lengths (S)));

      --  No sum passes 4,096.
      pragma Assert (5 + V.Lengths (0) < 4_096);
      pragma Assert (V.Starts (1) = 5 + V.Lengths (0));
      pragma Assert (V.Starts (1) + V.Lengths (1) < 4_096);
      pragma Assert (V.Starts (2) = V.Starts (1) + V.Lengths (1));
      pragma Assert (V.Starts (2) + V.Lengths (2) < 4_096);
      pragma Assert (V.Starts (3) = V.Starts (2) + V.Lengths (2));
      pragma Assert (V.Starts (3) + V.Lengths (3) < 4_096);
      pragma Assert
        (Byte_Length (Item_Length (V)) = V.Starts (3) + V.Lengths (3));

      --  Every slot ends below 128, the last by the third premise; so
      --  each length is the public length, not only modulo 256.
      pragma Assert (for all S in 0 .. 2 => V.Lengths (S) < 128);
      pragma Assert (V.Lengths (3) < 128);
      pragma Assert (Field_Length (V, Identifier_Field) < 128);
      pragma Assert (Field_Length (V, Value_Field) < 128);
   end Lemma_Item_No_Wrap;

end Mdoc_Relation.Hash;
