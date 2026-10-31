--  Circuit_Reader over the P-256 base field (ADR 0046): FieldID 1 of
--  lib/proto/circuit_io.h, a prime field. A library-level generic
--  instantiation: GNATprove analyses this instance and make prove
--  counts its checks.

pragma SPARK_Mode (On);

with Circuit_Reader;
with Sumcheck_Algebra_P256;
with Packed_Circuits_P256;

package Circuit_Reader_P256 is new Circuit_Reader
  (SA        => Sumcheck_Algebra_P256,
   PC        => Packed_Circuits_P256,
   Field_Id  => 1,
   Is_Binary => False);
