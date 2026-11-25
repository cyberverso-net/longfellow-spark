pragma SPARK_Mode (On);

package body Gadgets.Bits is

   --  The bridge of G1: the statement is the contract, proved in Lean
   --  (LongfellowSpark.Model.output_is_bit); register row L3.
   procedure Lemma_Output_Is_Bit (V : Element) with
     SPARK_Mode => Off
   is
   begin
      null;
   end Lemma_Output_Is_Bit;

   procedure Lemma_Unpack (C : Coefficients; P : Packed_Word) is
      U : constant Word_Bits := Unpack (C, P);
   begin
      for J in Bit_Index loop
         Lemma_Output_Is_Bit (U (J));
         pragma Loop_Invariant (for all I in 0 .. J => Is_Bit (U (I)));
      end loop;
   end Lemma_Unpack;

   function Interpolate return Coefficients is
      type Poly is array (Power_Index) of Element;
      R : Coefficients := [others => [others => Zero]];
   begin
      for I in Nibble loop
         declare
            N : Poly := [0 => One, others => Zero];
            D : Element := One;
            W : Element;
         begin
            --  N = the product over J /= I of (X + P_J), of degree 15;
            --  D = the product of (P_I + P_J).
            for J in Nibble loop
               if J /= I then
                  for M in reverse Power_Index loop
                     N (M) :=
                       Add (Mul (Point (J), N (M)),
                            (if M = 0 then Zero else N (M - 1)));
                  end loop;
                  D := Mul (D, Add (Point (I), Point (J)));
               end if;
            end loop;
            W := Inv (D);
            for K in Pluck_Index loop
               if (I / 2 ** K) mod 2 = 1 then
                  for M in Power_Index loop
                     R (K, M) := Add (R (K, M), Mul (W, N (M)));
                  end loop;
               end if;
            end loop;
         end;
      end loop;
      return R;
   end Interpolate;

end Gadgets.Bits;
