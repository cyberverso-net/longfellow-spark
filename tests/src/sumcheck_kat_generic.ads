--  Sumcheck_KAT_Generic: the known-answer harness for one instance of
--  Sumcheck_Algebra. Test code, outside the proof perimeter.
--
--  Reads the vector files of gen_sumcheck_vectors.py (format in the
--  generator's docstring) and checks every case against the library.
--  Besides the recorded expectations it re-checks at run time the
--  Lagrange constants (d * inv (d) = One with the library's Mul) and
--  that Bindeq agrees with Eq on every index, the algebraic facts that
--  are tested rather than proved (ADR 0023, ADR 0025).

pragma SPARK_Mode (Off);

with Sumcheck_Algebra;

generic
   with package SA is new Sumcheck_Algebra (<>);
   Field_Name : String;
   with function To_Element (S : String) return SA.Element;
   with function Image (E : SA.Element) return String;
package Sumcheck_KAT_Generic is

   --  Runs every case of the file; counts are accumulated.
   procedure Run_File (Path : String; Passed, Failed : in out Natural);

end Sumcheck_KAT_Generic;
