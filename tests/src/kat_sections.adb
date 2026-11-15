pragma SPARK_Mode (Off);

with Ada.Containers.Indefinite_Vectors;
with Ada.Text_IO;

package body Kat_Sections is

   type Tally is record
      Passed, Failed : Natural := 0;
   end record;

   type Entry_Rec (Section_Len, Part_Len : Natural) is record
      Section : String (1 .. Section_Len);
      Part    : String (1 .. Part_Len);
      Counts  : Tally;
   end record;

   package Entry_Vectors is new Ada.Containers.Indefinite_Vectors
     (Index_Type => Positive, Element_Type => Entry_Rec);

   --  One entry per section (Part empty, its total) and one per part of
   --  a section, in the order they were first met.
   Entries : Entry_Vectors.Vector;
   Current : Natural := 0;   --  the entry of the open section, 0 if none
   Mark    : Tally;          --  the counters at the previous Start or Count

   function Find (Section, Part : String) return Natural is
   begin
      for I in Entries.First_Index .. Entries.Last_Index loop
         if Entries (I).Section = Section and then Entries (I).Part = Part
         then
            return I;
         end if;
      end loop;
      return 0;
   end Find;

   function Find_Or_Add (Section, Part : String) return Positive is
      I : constant Natural := Find (Section, Part);
   begin
      if I /= 0 then
         return I;
      end if;
      Entries.Append
        (Entry_Rec'(Section_Len => Section'Length,
                    Part_Len    => Part'Length,
                    Section     => Section,
                    Part        => Part,
                    Counts      => (0, 0)));
      return Entries.Last_Index;
   end Find_Or_Add;

   procedure Start (Section : String; Passed, Failed : Natural) is
   begin
      Current := Find_Or_Add (Section, "");
      Mark := (Passed, Failed);
   end Start;

   procedure Count (Part : String; Passed, Failed : Natural) is
      Delta_P : constant Natural := Passed - Mark.Passed;
      Delta_F : constant Natural := Failed - Mark.Failed;
   begin
      Mark := (Passed, Failed);
      if Current = 0 or else (Delta_P = 0 and then Delta_F = 0) then
         return;
      end if;
      declare
         Section : constant String := Entries (Current).Section;
         P       : constant Positive := Find_Or_Add (Section, Part);
      begin
         Entries (Current).Counts.Passed :=
           Entries (Current).Counts.Passed + Delta_P;
         Entries (Current).Counts.Failed :=
           Entries (Current).Counts.Failed + Delta_F;
         if Part'Length > 0 then
            Entries (P).Counts.Passed := Entries (P).Counts.Passed + Delta_P;
            Entries (P).Counts.Failed := Entries (P).Counts.Failed + Delta_F;
         end if;
      end;
   end Count;

   function Kind_Of (Line : String) return String is
      I : Natural := Line'First;
      J : Natural;
   begin
      while I <= Line'Last and then Line (I) = ' ' loop
         I := I + 1;
      end loop;
      J := I;
      while J <= Line'Last and then Line (J) /= ' ' loop
         J := J + 1;
      end loop;
      return Line (I .. J - 1);
   end Kind_Of;

   function Line (Name : String; T : Tally) return String is
     (Name & ": passed" & T.Passed'Image & ", failed" & T.Failed'Image);

   procedure Print is
      package TIO renames Ada.Text_IO;
   begin
      TIO.Put_Line ("checks by section:");
      for I in Entries.First_Index .. Entries.Last_Index loop
         if Entries (I).Part = "" then
            declare
               Section : constant String := Entries (I).Section;
               Parts   : Natural := 0;
            begin
               TIO.Put_Line ("  " & Line (Section, Entries (I).Counts));
               for J in I + 1 .. Entries.Last_Index loop
                  if Entries (J).Section = Section then
                     Parts := Parts + 1;
                  end if;
               end loop;
               if Parts >= 2 then
                  for J in I + 1 .. Entries.Last_Index loop
                     if Entries (J).Section = Section then
                        TIO.Put_Line
                          ("    " & Line (Entries (J).Part,
                                          Entries (J).Counts));
                     end if;
                  end loop;
               end if;
            end;
         end if;
      end loop;
   end Print;

end Kat_Sections;
