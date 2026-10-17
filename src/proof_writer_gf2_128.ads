--  Proof_Writer over GF(2^128) (ADR 0049). A library-level generic
--  instantiation: GNATprove analyses this instance and make prove
--  counts its checks.

pragma SPARK_Mode (On);

with Proof_Writer;
with Ligero_Verifier_GF2_128;

package Proof_Writer_GF2_128 is new Proof_Writer (Ligero_Verifier_GF2_128);
