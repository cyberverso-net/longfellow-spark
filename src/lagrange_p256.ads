--  Lagrange over the P-256 base field (ADR 0036): a library-level
--  instance, proved by GNATprove with make prove.

pragma SPARK_Mode (On);

with Lagrange;
with Field_P256;

package Lagrange_P256 is new Lagrange (Field_P256.Sig);
