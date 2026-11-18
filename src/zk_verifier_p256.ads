--  Zk_Verifier over the P-256 base field (ADR 0035): a library-level
--  instance, proved by GNATprove with make prove (partition verifier).
--  What is proved, tested and trusted is stated in the header of
--  Zk_Verifier.

pragma SPARK_Mode (On);

with Zk_Verifier;
with Ligero_Verifier_P256;
with Packed_HQuad_P256;

package Zk_Verifier_P256 is new Zk_Verifier
  (LV => Ligero_Verifier_P256,
   PH => Packed_HQuad_P256);
