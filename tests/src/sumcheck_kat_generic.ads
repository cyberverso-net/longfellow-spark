--  Sumcheck_KAT_Generic: the known-answer harness for one instance of
--  Sumcheck_Algebra. Test code, outside the proof perimeter.
--
--  Reads the vector files of gen_sumcheck_vectors.py (tiers 1 and 2,
--  format in the generator's docstring) and the recorded upstream runs
--  of tier 3 (format in ADR 0027), and checks every case against the
--  library. Besides the recorded expectations it re-checks at run time
--  the Lagrange constants (d * inv (d) = One with the library's Mul) and
--  that Bindeq agrees with Eq on every index, the algebraic facts that
--  are tested rather than proved (ADR 0023, ADR 0025).
--
--  Tier 3: the circuit block is followed by public, pad_base, g,
--  layer_challenges, proof, alpha_input, optional claim lines,
--  constraint and lqc lines; at end the core runs with the recorded
--  challenges and its constraints are compared per constraint as sets
--  of (variable, coefficient) pairs, zero coefficients ignored.

pragma SPARK_Mode (Off);

with Sumcheck_Algebra;
with Sumcheck_Expression;
with Sumcheck_Verifier;

generic
   with package SA is new Sumcheck_Algebra (<>);
   with package SE is new Sumcheck_Expression (SA => SA);
   with package SV is new Sumcheck_Verifier (SA => SA, SE => SE);
   Field_Name : String;
   with function To_Element (S : String) return SA.Element;
   with function Image (E : SA.Element) return String;
package Sumcheck_KAT_Generic is

   --  Runs every case of the file; counts are accumulated.
   procedure Run_File (Path : String; Passed, Failed : in out Natural);

end Sumcheck_KAT_Generic;
