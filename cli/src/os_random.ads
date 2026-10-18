--  Os_Random: the operating system's random generator as a byte stream
--  for the prover (ADR 0050): Fill reads /dev/urandom, the realisation
--  of the system's cryptographically secure generator on macOS and
--  Linux at this date. Outside the proof perimeter (SPARK_Mode Off):
--  it does input and output on a device file, which SPARK does not
--  model; the trust model lists it as trusted for the zero-knowledge
--  property of the proofs longfellow_prove makes without --seed.

pragma SPARK_Mode (Off);

with Bytes; use Bytes;

package Os_Random is

   --  Fill B with fresh bytes from the system generator; raises
   --  Program_Error when the device cannot be read.
   procedure Fill (B : out Byte_Array);

end Os_Random;
