--  Proof_Writer over the P-256 base field (ADR 0049). A library-level
--  generic instantiation: GNATprove analyses this instance and make
--  prove counts its checks.

pragma SPARK_Mode (On);

with Proof_Writer;
with Ligero_Verifier_P256;

package Proof_Writer_P256 is new Proof_Writer (Ligero_Verifier_P256);
