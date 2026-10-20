--  No_Fft_P256: the Extend formal of Ligero_Prover for the P-256
--  instances, which use the Lagrange encoder (Use_Fft => False, ADR
--  0057) and never call it. It copies the row into the first entries
--  and zeroes the others, which is what the formal's contract asks; it
--  computes no parity. Block 4 of Phase D decides the encoder of P-256.
--
--  Proof status: Silver, and the formal's postcondition.

pragma SPARK_Mode (On);

with Field_P256;
with Sumcheck_Algebra_P256;

package No_Fft_P256 is

   subtype Element_Array is Sumcheck_Algebra_P256.Element_Array;

   procedure Extend (Row : Element_Array; Enc : out Element_Array) with
     Global => null,
     Pre    => Row'First = 0 and then Enc'First = 0
               and then Row'Length >= 1
               and then Row'Length <= Enc'Length
               and then Enc'Length <= 2**16,
     Post   =>
       (for all X in 0 .. Row'Last => Field_P256.Same (Enc (X), Row (X)));

end No_Fft_P256;
