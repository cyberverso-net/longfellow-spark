pragma SPARK_Mode (On);

package body Mdoc_Relation.Hash.Conditions is

   --  The byte at preimage position Q, from Q = N on, is 16#80#, zero,
   --  a byte of the length or a byte of the zero blocks.
   procedure Lemma_Padding_Byte
     (V : Private_Part; N : Message_Length; Q : Preimage_Index)
   with
     Global => null,
     Pre    => Padded_From (V, N) and then Q >= N,
     Post   =>
       (if Q = N then Preimage_Byte (V, Q) = 16#80#
        elsif Q < 64 * Natural (V.Count) - 2 then Preimage_Byte (V, Q) = 0
        elsif Q = 64 * Natural (V.Count) - 2 then
          Preimage_Byte (V, Q) = Unsigned_8 ((8 * N) / 256)
          and then Preimage_Byte (V, Q) < 16#50#
        elsif Q = 64 * Natural (V.Count) - 1 then
          Preimage_Byte (V, Q) = Unsigned_8 ((8 * N) mod 256)
          and then Preimage_Byte (V, Q) mod 8 = 0
        else Preimage_Byte (V, Q) = 0);

   --  N, the length of the signed message, is read by the contract
   --  only: the precondition puts the padding from N on, and the
   --  postcondition's cases are counted from it. The body proves the
   --  one case the precondition does not state, a byte of the zero
   --  blocks, from Zero_Tail, which does not depend on N. A build
   --  without assertions drops the contract, so the body is all that
   --  remains and N is not read there.
   procedure Lemma_Padding_Byte
     (V : Private_Part; N : Message_Length; Q : Preimage_Index)
   is
      pragma Unreferenced (N);
   begin
      if Q >= 64 * Natural (V.Count) then
         pragma Assert (Q / 64 >= Natural (V.Count));
         pragma Assert (Q = 64 * (Q / 64) + Q mod 64);
         pragma Assert (Preimage_Byte (V, 64 * (Q / 64) + Q mod 64) = 0);
      end if;
   end Lemma_Padding_Byte;

   --  A window that reaches position N or beyond cannot match a pattern
   --  the padding cannot hold.
   procedure Lemma_Safe_Pattern
     (V       : Private_Part;
      N       : Message_Length;
      K       : Index_12;
      Offset  : Window_Offset;
      Pattern : Byte_Array)
   with
     Global => null,
     Pre    => Padded_From (V, N) and then Padding_Safe (Pattern)
               and then Pattern'Length <= 100 - Offset
               and then Matches (V, K, Offset, Pattern),
     Post   => 25 + K + Offset + Pattern'Length <= N;

   procedure Lemma_Safe_Pattern
     (V       : Private_Part;
      N       : Message_Length;
      K       : Index_12;
      Offset  : Window_Offset;
      Pattern : Byte_Array)
   is
      Q0 : constant Natural := 25 + K + Offset;
   begin
      if Q0 + Pattern'Length > N then
         if Q0 >= N then
            --  The first byte lies in the padding or past the windows.
            pragma Assert (Mso_At (V, K, Offset) = Pattern (Pattern'First));
            if K + Offset < Max_Mso_Len then
               pragma Assert (Mso_At (V, K, Offset) = Preimage_Byte (V, Q0));
               Lemma_Padding_Byte (V, N, Q0);
            end if;
         else
            --  Byte N, 16#80#, lies inside the window.
            pragma Assert
              (Mso_At (V, K, Offset + (N - Q0))
               = Pattern (Pattern'First + (N - Q0)));
            if K + Offset + (N - Q0) < Max_Mso_Len then
               pragma Assert
                 (Mso_At (V, K, Offset + (N - Q0)) = Preimage_Byte (V, N));
               Lemma_Padding_Byte (V, N, N);
            end if;
         end if;
      end if;
   end Lemma_Safe_Pattern;

   --  The key of y, 22 58 20: its first byte can be the high byte of a
   --  length and its second the low byte, so the third, in the zero
   --  blocks or past the windows, refuses it.
   procedure Lemma_Y_Key (V : Private_Part; N : Message_Length; K : Index_12)
   with
     Global => null,
     Pre    => Padded_From (V, N)
               and then Matches (V, K, 65, Device_Key_Y_Key),
     Post   => 25 + K + 65 + 3 <= N;

   procedure Lemma_Y_Key (V : Private_Part; N : Message_Length; K : Index_12)
   is
      Q0 : constant Natural := 25 + K + 65;
   begin
      pragma Assert (Mso_At (V, K, 65) = 16#22#);
      pragma Assert (Mso_At (V, K, 66) = 16#58#);
      pragma Assert (Mso_At (V, K, 67) = 16#20#);
      if Q0 + 3 > N then
         if Q0 < N then
            --  Byte N, 16#80#, is the second or the third.
            if K + 65 + (N - Q0) < Max_Mso_Len then
               pragma Assert
                 (Mso_At (V, K, 65 + (N - Q0)) = Preimage_Byte (V, N));
               Lemma_Padding_Byte (V, N, N);
            end if;
         elsif K + 65 < Max_Mso_Len then
            Lemma_Padding_Byte (V, N, Q0);
            if Q0 = 64 * Natural (V.Count) - 2 and then K + 66 < Max_Mso_Len
            then
               Lemma_Padding_Byte (V, N, Q0 + 1);
               if K + 67 < Max_Mso_Len then
                  Lemma_Padding_Byte (V, N, Q0 + 2);
               end if;
            end if;
         end if;
      end if;
   end Lemma_Y_Key;

   procedure Fact_Padding
     (V : Private_Part; N : Message_Length; K : Index_12)
   is
   begin
      if Matches (V, K, 0, Valid_From_Key) then
         Lemma_Safe_Pattern (V, N, K, 0, Valid_From_Key);
      end if;
      if Matches (V, K, 0, Valid_Until_Key) then
         Lemma_Safe_Pattern (V, N, K, 0, Valid_Until_Key);
      end if;
      if Matches (V, K, 0, Device_Key_Key) then
         Lemma_Safe_Pattern (V, N, K, 0, Device_Key_Key);
      end if;
      if Matches (V, K, 0, Value_Digests_Key) then
         Lemma_Safe_Pattern (V, N, K, 0, Value_Digests_Key);
      end if;
      if Matches (V, K, 65, Device_Key_Y_Key) then
         Lemma_Y_Key (V, N, K);
      end if;
   end Fact_Padding;

end Mdoc_Relation.Hash.Conditions;
