--  Circuit_Checker_GF2_128: the circuit checker over GF(2^128), for the
--  hash circuit, with the limits of ADR 0093 measured on the registered
--  one-attribute pair. Proof status: that of Circuit_Checker.

pragma SPARK_Mode (On);

with Circuit_Checker;
with Sumcheck_Algebra_GF2_128;
with Packed_Circuits_GF2_128;

package Circuit_Checker_GF2_128 is new Circuit_Checker
  (SA                 => Sumcheck_Algebra_GF2_128,
   PC                 => Packed_Circuits_GF2_128,
   Max_Form           => 3,
   Max_Terms_Per_Wire => 128,
   Max_Slots          => 128,
   Max_Layer_Slots    => 2 ** 22,
   Max_Vars           => 2 ** 22);
