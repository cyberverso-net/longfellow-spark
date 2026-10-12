--  Sumcheck_Algebra over GF(2^128) (ADR 0024). A library-level
--  generic instantiation: GNATprove analyses this instance, with the
--  contracts of GF2_128 visible, and make prove counts its checks.

pragma SPARK_Mode (On);

with Sumcheck_Algebra;
with Field_GF2_128;

package Sumcheck_Algebra_GF2_128 is new Sumcheck_Algebra (Field_GF2_128.Sig);
