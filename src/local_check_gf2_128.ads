--  Local_Check_GF2_128: Local_Check over GF(2^128), the field of the
--  hash circuit (ADR 0093). Proof status: that of Local_Check.

pragma SPARK_Mode (On);

with Local_Check;
with Sumcheck_Algebra_GF2_128;

package Local_Check_GF2_128 is new Local_Check
  (SA => Sumcheck_Algebra_GF2_128);
