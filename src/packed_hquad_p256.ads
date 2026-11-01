--  Packed_HQuad over the P-256 base field. HQ is the verifier's instance
--  of Sumcheck_HQuad, the one the prover uses: the kernels are proved
--  once, with Sumcheck_Verifier_P256.

pragma SPARK_Mode (On);

with Packed_HQuad;
with Sumcheck_Algebra_P256;
with Packed_Circuits_P256;
with Sumcheck_Verifier_P256;

package Packed_HQuad_P256 is new Packed_HQuad
  (SA => Sumcheck_Algebra_P256,
   PC => Packed_Circuits_P256,
   HQ => Sumcheck_Verifier_P256.HQ);
