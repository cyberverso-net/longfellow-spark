--  Circuit_Check_GF2_128: the checker on two files over GF(2^128).
--  Proof status: that of Circuit_Check.

pragma SPARK_Mode (On);

with Circuit_Check;
with Sumcheck_Algebra_GF2_128;
with Packed_Circuits_GF2_128;
with Circuit_Reader_GF2_128;
with Circuit_Checker_GF2_128;

package Circuit_Check_GF2_128 is new Circuit_Check
  (SA => Sumcheck_Algebra_GF2_128,
   PC => Packed_Circuits_GF2_128,
   CR => Circuit_Reader_GF2_128,
   CK => Circuit_Checker_GF2_128);
