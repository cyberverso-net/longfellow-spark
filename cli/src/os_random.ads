--  Os_Random: the operating system's random generator as a byte stream
--  for the prover (ADR 0050): Fill reads /dev/urandom, the system's
--  cryptographically secure generator on macOS and Linux.
--
--  Documentation: docs/guide/07-prover.md, Section 3.2.
--
--  Proof status: outside SPARK (SPARK_Mode Off), since it does input
--  and output on a device file, which SPARK does not model; compiled
--  with the run-time checks on (register row T7). Trusted: that the
--  bytes are fresh and unpredictable (register rows C1 and P4), on
--  which the zero knowledge of the proofs the command-line provers make
--  without --seed depends.

pragma SPARK_Mode (Off);

with Bytes; use Bytes;

package Os_Random is

   --  Fill B with fresh bytes from the system generator; raises
   --  Program_Error when the device cannot be read.
   procedure Fill (B : out Byte_Array);

end Os_Random;
