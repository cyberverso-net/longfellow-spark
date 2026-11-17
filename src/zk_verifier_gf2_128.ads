--  Zk_Verifier over GF(2^128) (ADR 0035): a library-level instance,
--  proved by GNATprove with make prove (partition verifier). What is
--  proved, tested and trusted is stated in the header of Zk_Verifier.

pragma SPARK_Mode (On);

with Zk_Verifier;
with Ligero_Verifier_GF2_128;
with Packed_HQuad_GF2_128;

package Zk_Verifier_GF2_128 is new Zk_Verifier
  (LV => Ligero_Verifier_GF2_128,
   PH => Packed_HQuad_GF2_128);
