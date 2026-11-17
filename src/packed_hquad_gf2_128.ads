--  Packed_HQuad over the binary field GF(2^128). HQ is the verifier's
--  instance of Sumcheck_HQuad, the one the prover uses: the kernels are
--  proved once, with Sumcheck_Verifier_GF2_128. Proof status and
--  documentation: see Packed_HQuad and docs/guide/03-sumcheck.md,
--  Section 4.2.

pragma SPARK_Mode (On);

with Packed_HQuad;
with Sumcheck_Algebra_GF2_128;
with Packed_Circuits_GF2_128;
with Sumcheck_Verifier_GF2_128;

package Packed_HQuad_GF2_128 is new Packed_HQuad
  (SA => Sumcheck_Algebra_GF2_128,
   PC => Packed_Circuits_GF2_128,
   HQ => Sumcheck_Verifier_GF2_128.HQ);
