--  Kat_Sections: the checks of a harness counted by section, so that a
--  reader can recompute every count a chapter of the guide gives for a
--  part of a test, not only the total. Test code, outside the proof
--  perimeter.
--
--  A harness counts its checks in two counters, passed and failed. It
--  opens a section (a vector file, or a group of checks that need no
--  file) with Start, giving the counters as they are; then, after each
--  step, Count names the part of the section that step belongs to (a
--  kind of line, a tier) and gives the counters again: the checks
--  counted since the previous Start or Count belong to that part. Print
--  writes every section with its total and, when it has two parts or
--  more, each part, in the order they were first met. The harness's
--  own total and exit status are untouched.

pragma SPARK_Mode (Off);

package Kat_Sections is

   --  Opens Section; the counters are Passed and Failed now. A section
   --  started again (the same file given twice) adds to its counts.
   procedure Start (Section : String; Passed, Failed : Natural);

   --  The checks counted since the previous Start or Count belong to
   --  Part of the open section. A part with no check is not recorded.
   procedure Count (Part : String; Passed, Failed : Natural);

   --  The first blank-separated word of Line, the kind of a line of most
   --  vector files ("mul", "bytes", "verify"); "" for a blank line.
   function Kind_Of (Line : String) return String;

   --  Writes the counts by section on standard output.
   procedure Print;

end Kat_Sections;
