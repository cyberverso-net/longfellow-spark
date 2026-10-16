pragma SPARK_Mode (On);

with Zk_Verifier;
with Ligero_Verifier_P256;

package Zk_Verifier_P256 is new Zk_Verifier (Ligero_Verifier_P256);
