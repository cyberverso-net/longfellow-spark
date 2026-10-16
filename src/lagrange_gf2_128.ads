--  Lagrange over GF(2^128) (ADR 0036): a library-level instance, proved
--  by GNATprove with make prove.

pragma SPARK_Mode (On);

with Lagrange;
with Field_GF2_128;

package Lagrange_GF2_128 is new Lagrange (Field_GF2_128.Sig);
