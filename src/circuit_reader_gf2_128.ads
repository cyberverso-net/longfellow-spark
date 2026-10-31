--  Circuit_Reader over GF(2^128) (ADR 0046): FieldID 4 of
--  lib/proto/circuit_io.h, a binary field. A library-level generic
--  instantiation: GNATprove analyses this instance and make prove
--  counts its checks.

pragma SPARK_Mode (On);

with Circuit_Reader;
with Sumcheck_Algebra_GF2_128;
with Packed_Circuits_GF2_128;

package Circuit_Reader_GF2_128 is new Circuit_Reader
  (SA        => Sumcheck_Algebra_GF2_128,
   PC        => Packed_Circuits_GF2_128,
   Field_Id  => 4,
   Is_Binary => True);
