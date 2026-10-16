pragma SPARK_Mode (On);

with Ligero_Proof;
with Sumcheck_Algebra_P256;

package Ligero_Proof_P256 is new Ligero_Proof (Sumcheck_Algebra_P256);
