--  CIRCUIT_KAT: known-answer test harness for the LFC2 circuit loader
--  (Phase B, ADR 0048): tier 1, the two upstream circuit files parsed
--  by the independent reference of gen_circuit_vectors.py; tier 2, the
--  Appendix B.3 circuits written in LFC2 in two encodings, and the
--  malformed cases with the status each must give.
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads
--  the vector files given as arguments (default: circuit_summary.txt,
--  circuit_lfc2.txt and mdoc_summary.txt under tests/vectors/) and
--  checks every case
--  against Circuit_Reader on the field of the current "field" line.
--  Built with -gnata, so the library's executable contracts run.
--
--  File format: '#' comments and blank lines are skipped; otherwise
--  one case per line, fields separated by blanks, bytes as hex,
--  elements as big-endian hex integers (32 digits on GF(2^128), 64 on
--  P-256), the identifier as 64 hex digits in memory order; statuses
--  are the lower-case values of Circuit_Status:
--    field <gf2_128|p256>
--    lfc2 <name> <status> <bytes>        Read gives this status (bytes
--        as hex, - for none)
--    file <name> <status> <path>         Read of the file's bytes does
--    summary <name> <nl> <nt> <noutput> <ninput> <npublic> <sfb> <id>
--        the last circuit loaded (named name) has these
--    layer <name> <j> <logw> <nw> <nterms>
--    term <name> <i> <g> <h0> <h1> <k>   term i (1-based) of it
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Characters.Handling;
with Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with GF2_128;
with P256_Field;
with Circuit_Status;
with Circuit_Reader;
with Circuit_Reader_GF2_128;
with Circuit_Reader_P256;

procedure Circuit_KAT is

   package TIO renames Ada.Text_IO;

   Default_Summary : constant String := "tests/vectors/circuit_summary.txt";
   Default_Lfc2    : constant String := "tests/vectors/circuit_lfc2.txt";
   Default_Mdoc    : constant String := "tests/vectors/mdoc_summary.txt";

   type Field_Kind is (None, GF, P);
   Current_Field : Field_Kind := None;

   Passed  : Natural := 0;
   Failed  : Natural := 0;
   Line_No : Natural := 0;

   Parse_Error : exception;

   function Hex_Digit (C : Character) return Unsigned_8 is
   begin
      case C is
         when '0' .. '9' =>
            return Unsigned_8 (Character'Pos (C) - Character'Pos ('0'));
         when 'a' .. 'f' =>
            return Unsigned_8 (Character'Pos (C) - Character'Pos ('a') + 10);
         when 'A' .. 'F' =>
            return Unsigned_8 (Character'Pos (C) - Character'Pos ('A') + 10);
         when others =>
            raise Parse_Error with "bad hex digit '" & C & "'";
      end case;
   end Hex_Digit;

   type Byte_Array_Access is access Byte_Array;
   procedure Free is
     new Ada.Unchecked_Deallocation (Byte_Array, Byte_Array_Access);

   function To_Bytes (S : String) return Byte_Array_Access is
      R : Byte_Array_Access;
   begin
      if S'Length mod 2 /= 0 then
         raise Parse_Error with "odd number of hex digits";
      end if;
      R := new Byte_Array (0 .. S'Length / 2 - 1);
      for I in R'Range loop
         R (I) := Shift_Left (Hex_Digit (S (S'First + 2 * I)), 4)
                  or Hex_Digit (S (S'First + 2 * I + 1));
      end loop;
      return R;
   end To_Bytes;

   function Read_File (Path : String) return Byte_Array_Access is
      use Ada.Streams;
      use Ada.Streams.Stream_IO;
      F    : File_Type;
      Size : constant Natural := Natural (Ada.Directories.Size (Path));
      S    : Stream_Element_Array (1 .. Stream_Element_Offset (Size));
      Last : Stream_Element_Offset;
      R    : Byte_Array_Access;
   begin
      Open (F, In_File, Path);
      Read (F, S, Last);
      Close (F);
      if Natural (Last) /= Size then
         raise Parse_Error with "short read of " & Path;
      end if;
      R := new Byte_Array (0 .. Size - 1);
      for I in S'Range loop
         R (Natural (I) - 1) := Unsigned_8 (S (I));
      end loop;
      return R;
   end Read_File;

   function To_Id (S : String) return Bytes_32 is
      R : Bytes_32;
   begin
      if S'Length /= 64 then
         raise Parse_Error with "expected 64 hex digits, got '" & S & "'";
      end if;
      for I in R'Range loop
         R (I) := Shift_Left (Hex_Digit (S (S'First + 2 * I)), 4)
                  or Hex_Digit (S (S'First + 2 * I + 1));
      end loop;
      return R;
   end To_Id;

   function GF_To_Element (S : String) return GF2_128.Element is
      R : GF2_128.Element := GF2_128.Zero;
      L : GF2_128.Limb_Index;
   begin
      if S'Length /= 32 then
         raise Parse_Error with "expected 32 hex digits, got '" & S & "'";
      end if;
      for I in 0 .. 31 loop
         L := (if I < 16 then 1 else 0);
         R.Limbs (L) := Shift_Left (R.Limbs (L), 4)
                        or Unsigned_64 (Hex_Digit (S (S'First + I)));
      end loop;
      return R;
   end GF_To_Element;

   function P_To_Element (S : String) return P256_Field.Element is
      R : P256_Field.Limb_Array := [others => 0];
      L : P256_Field.Limb_Index;
   begin
      if S'Length /= 64 then
         raise Parse_Error with "expected 64 hex digits, got '" & S & "'";
      end if;
      for I in 0 .. 63 loop
         L := P256_Field.Limb_Index (3 - I / 16);
         R (L) := Shift_Left (R (L), 4)
                  or Unsigned_64 (Hex_Digit (S (S'First + I)));
      end loop;
      if not P256_Field.Is_Canonical (R) then
         raise Parse_Error with "value not below p: " & S;
      end if;
      return P256_Field.From_Canonical (R);
   end P_To_Element;

   function Status_Name (St : Circuit_Status.Status) return String is
     (Ada.Characters.Handling.To_Lower (St'Image));

   --  Blank-separated fields of a line, as index bounds into it.
   Max_Fields : constant := 64;
   type Field_Bounds is record
      Lo, Hi : Natural;
   end record;
   type Field_Array is array (1 .. Max_Fields) of Field_Bounds;

   procedure Split
     (Line : String; Fields : out Field_Array; Count : out Natural)
   is
      I : Natural := Line'First;
      J : Natural;
   begin
      Count  := 0;
      Fields := [others => (0, 0)];
      while I <= Line'Last loop
         if Line (I) = ' ' then
            I := I + 1;
         else
            J := I;
            while J < Line'Last and then Line (J + 1) /= ' ' loop
               J := J + 1;
            end loop;
            if Count = Fields'Length then
               raise Parse_Error with "too many fields";
            end if;
            Count := Count + 1;
            Fields (Count) := (I, J);
            I := J + 1;
         end if;
      end loop;
   end Split;

   procedure Report_Failure (Msg : String) is
   begin
      Failed := Failed + 1;
      TIO.Put_Line ("FAIL line" & Line_No'Image & ": " & Msg);
   end Report_Failure;

   --  The checks of one field: the loader, the current circuit.
   generic
      with package CR is new Circuit_Reader (<>);
      with function To_Element (S : String) return CR.SA.Element;
   package Field_Checks is
      procedure Load (Name : String; Want : String; B : Byte_Array);
      procedure Summary
        (Name  : String;
         F     : access function (K : Positive) return String;
         Count : Natural);
      procedure Layer
        (Name  : String;
         F     : access function (K : Positive) return String;
         Count : Natural);
      procedure Term
        (Name  : String;
         F     : access function (K : Positive) return String;
         Count : Natural);
      procedure Release;
   end Field_Checks;

   package body Field_Checks is
      use type CR.SA.Element;
      use type CR.Circuit_Access;
      use type Circuit_Status.Status;

      Current      : CR.Circuit_Access := null;
      Current_H    : CR.Header := CR.Null_Header;
      Current_Name : String (1 .. 80) := [others => ' '];
      Name_Len     : Natural := 0;

      procedure Release is
      begin
         if Current /= null then
            CR.Free (Current);
         end if;
         Name_Len := 0;
      end Release;

      procedure Load (Name : String; Want : String; B : Byte_Array) is
         C  : CR.Circuit_Access;
         H  : CR.Header;
         St : Circuit_Status.Status;
      begin
         Release;
         CR.Read (B, C, H, St);
         if Status_Name (St) /= Want then
            Report_Failure ("load " & Name & ": got " & Status_Name (St)
                            & ", expected " & Want);
            if C /= null then
               CR.Free (C);
            end if;
            return;
         end if;
         if (St = Circuit_Status.Ok) /= (C /= null) then
            Report_Failure ("load " & Name & ": status and circuit disagree");
            if C /= null then
               CR.Free (C);
            end if;
            return;
         end if;
         Passed := Passed + 1;
         if C /= null then
            Current   := C;
            Current_H := H;
            if Name'Length > Current_Name'Length then
               raise Parse_Error with "name too long";
            end if;
            Current_Name (1 .. Name'Length) := Name;
            Name_Len := Name'Length;
         end if;
      end Load;

      procedure Need (Name : String) is
      begin
         if Current = null or else Current_Name (1 .. Name_Len) /= Name then
            raise Parse_Error with "no loaded circuit named " & Name;
         end if;
      end Need;

      procedure Summary
        (Name  : String;
         F     : access function (K : Positive) return String;
         Count : Natural)
      is
      begin
         if Count /= 9 then
            raise Parse_Error with "summary expects 8 fields";
         end if;
         Need (Name);
         declare
            NL : constant Natural := Natural'Value (F (3));
            NT : constant Natural := Natural'Value (F (4));
            Id : constant Bytes_32 := To_Id (F (9));
         begin
            if Current.Last_Layer + 1 /= NL then
               Report_Failure (Name & ": layer count"
                               & Natural'Image (Current.Last_Layer + 1)
                               & ", expected" & NL'Image);
            elsif Current.NT /= NT then
               Report_Failure (Name & ": term count" & Current.NT'Image
                               & ", expected" & NT'Image);
            elsif Current.Noutput /= Natural'Value (F (5))
              or else Current.Ninput /= Natural'Value (F (6))
              or else Current.Npublic /= Natural'Value (F (7))
            then
               Report_Failure (Name & ": header counts differ");
            elsif Current_H.Subfield_Boundary /= Natural'Value (F (8)) then
               Report_Failure (Name & ": subfield boundary"
                               & Current_H.Subfield_Boundary'Image);
            elsif Current_H.Id /= Id then
               Report_Failure (Name & ": identifier differs");
            elsif Current_H.Field_Id /= CR.Field_Id then
               Report_Failure (Name & ": field identifier");
            else
               Passed := Passed + 1;
            end if;
         end;
      end Summary;

      procedure Layer
        (Name  : String;
         F     : access function (K : Positive) return String;
         Count : Natural)
      is
      begin
         if Count /= 6 then
            raise Parse_Error with "layer expects 5 fields";
         end if;
         Need (Name);
         declare
            J : constant Natural := Natural'Value (F (3));
         begin
            if J > Current.Last_Layer then
               raise Parse_Error with "layer index out of range";
            end if;
            declare
               L : constant CR.SA.Layer := Current.Layers (J);
            begin
               if L.Logw /= Natural'Value (F (4))
                 or else L.NW_In /= Natural'Value (F (5))
                 or else L.Last + 1 - L.First /= Natural'Value (F (6))
               then
                  Report_Failure
                    (Name & ": layer" & J'Image & " differs: logw"
                     & L.Logw'Image & " nw" & L.NW_In'Image
                     & " terms" & Natural'Image (L.Last + 1 - L.First));
               else
                  Passed := Passed + 1;
               end if;
            end;
         end;
      end Layer;

      procedure Term
        (Name  : String;
         F     : access function (K : Positive) return String;
         Count : Natural)
      is
      begin
         if Count /= 7 then
            raise Parse_Error with "term expects 6 fields";
         end if;
         Need (Name);
         declare
            I : constant Positive := Positive'Value (F (3));
         begin
            if I > Current.NT then
               raise Parse_Error with "term index out of range";
            end if;
            declare
               T : constant CR.SA.Term := Current.Terms (I);
            begin
               if T.G /= Natural'Value (F (4))
                 or else T.H0 /= Natural'Value (F (5))
                 or else T.H1 /= Natural'Value (F (6))
                 or else T.K /= To_Element (F (7))
               then
                  Report_Failure (Name & ": term" & I'Image & " differs");
               else
                  Passed := Passed + 1;
               end if;
            end;
         end;
      end Term;
   end Field_Checks;

   package GF_Checks is
     new Field_Checks (Circuit_Reader_GF2_128, GF_To_Element);
   package P_Checks is
     new Field_Checks (Circuit_Reader_P256, P_To_Element);

   procedure Check_Case (Line : String) is
      Fields : Field_Array;
      Count  : Natural;

      function F (K : Positive) return String is
      begin
         if K > Count then
            raise Parse_Error with "missing field" & K'Image;
         end if;
         return Line (Fields (K).Lo .. Fields (K).Hi);
      end F;

      procedure Load (Name, Want : String; B : Byte_Array_Access) is
      begin
         case Current_Field is
            when GF   => GF_Checks.Load (Name, Want, B.all);
            when P    => P_Checks.Load (Name, Want, B.all);
            when None => raise Parse_Error with "no field line yet";
         end case;
      end Load;
   begin
      Split (Line, Fields, Count);
      if Count = 0 then
         return;
      end if;
      declare
         Op : constant String := F (1);
      begin
         if Op = "field" then
            if F (2) = "gf2_128" then
               Current_Field := GF;
            elsif F (2) = "p256" then
               Current_Field := P;
            else
               raise Parse_Error with "unknown field " & F (2);
            end if;
         elsif Op = "lfc2" or else Op = "file" then
            if Count /= 4 then
               raise Parse_Error with Op & " expects name, status, data";
            end if;
            declare
               B : Byte_Array_Access :=
                 (if Op /= "lfc2" then Read_File (F (4))
                  elsif F (4) = "-" then new Byte_Array (0 .. -1)
                  else To_Bytes (F (4)));
            begin
               Load (F (2), F (3), B);
               Free (B);
            end;
         elsif Op = "summary" then
            case Current_Field is
               when GF   => GF_Checks.Summary (F (2), F'Access, Count);
               when P    => P_Checks.Summary (F (2), F'Access, Count);
               when None => raise Parse_Error with "no field line yet";
            end case;
         elsif Op = "layer" then
            case Current_Field is
               when GF   => GF_Checks.Layer (F (2), F'Access, Count);
               when P    => P_Checks.Layer (F (2), F'Access, Count);
               when None => raise Parse_Error with "no field line yet";
            end case;
         elsif Op = "term" then
            case Current_Field is
               when GF   => GF_Checks.Term (F (2), F'Access, Count);
               when P    => P_Checks.Term (F (2), F'Access, Count);
               when None => raise Parse_Error with "no field line yet";
            end case;
         else
            raise Parse_Error with "unknown op " & Op;
         end if;
      end;
   exception
      when E : Parse_Error =>
         Report_Failure (Ada.Exceptions.Exception_Message (E));
      when E : others =>
         Report_Failure
           ("exception " & Ada.Exceptions.Exception_Information (E));
   end Check_Case;

   procedure Run_File (Path : String) is
      File : TIO.File_Type;
   begin
      TIO.Put_Line ("Circuit_Reader known-answer tests: " & Path);
      TIO.Open (File, TIO.In_File, Path);
      Line_No := 0;
      while not TIO.End_Of_File (File) loop
         declare
            Line : constant String := TIO.Get_Line (File);
         begin
            Line_No := Line_No + 1;
            if Line'Length > 0 and then Line (Line'First) /= '#' then
               Check_Case (Line);
            end if;
         end;
      end loop;
      TIO.Close (File);
      GF_Checks.Release;
      P_Checks.Release;
   end Run_File;

begin
   if Ada.Command_Line.Argument_Count = 0 then
      Run_File (Default_Summary);
      Run_File (Default_Lfc2);
      Run_File (Default_Mdoc);
   else
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         Run_File (Ada.Command_Line.Argument (I));
      end loop;
   end if;
   TIO.Put_Line ("passed" & Passed'Image & ", failed" & Failed'Image);
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end Circuit_KAT;
