pragma SPARK_Mode (On);

with Zk_Verifier;
with Ligero_Verifier_P256;
with Packed_HQuad_P256;

package Zk_Verifier_P256 is new Zk_Verifier
  (LV => Ligero_Verifier_P256,
   PH => Packed_HQuad_P256);
