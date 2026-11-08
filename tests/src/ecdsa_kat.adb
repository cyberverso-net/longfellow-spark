--  ECDSA_KAT: known-answer test harness for P256_Curve and Ecdsa_Witness
--  (block 6 of Phase D, ADR 0086).
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads the
--  vector file given as argument (default tests/vectors/ecdsa_witness.txt)
--  and checks every case against the library; the witness_file cases
--  compare the witness element by element with upstream's signature
--  witness files under tests/vectors/upstream/mdoc/. Built with -gnata,
--  so the library's executable contracts run. Not the constant-time
--  build.
--
--  File format: '#' comments and blank lines are skipped; otherwise one
--  case per line, fields separated by blanks, field elements and
--  256-bit integers as 64 hex digits, most significant first:
--    add <x1> <y1> <z1> <x2> <y2> <z2> <x3> <y3> <z3>
--    double <x> <y> <z> <x3> <y3> <z3>
--    affine <x> <y> <z> <ax> <ay>
--    scalar <k> <px> <py> <rx> <ry>
--    witness <name> <pkx> <pky> <e> <r> <s> <digest>
--    witness_reject <name> <s>
--    witness_file <name> <archive> <first> <pkx> <pky> <e> <r> <s>
--  Unknown operations are failures, so a vector file never passes
--  silently.
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Ada.Assertions;
with Interfaces;   use Interfaces;
with Bytes;
with Q256_Field;
with P256_Field;   use P256_Field;
with P256_Curve;
with Ecdsa_Witness;
with Sha256;

procedure ECDSA_KAT is

   package TIO renames Ada.Text_IO;
   package SAP renames Ecdsa_Witness.SAP;



   Default_Path : constant String := "tests/vectors/ecdsa_witness.txt";
   Mdoc_Dir     : constant String := "tests/vectors/upstream/mdoc/";

   Passed  : Natural := 0;
   Failed  : Natural := 0;
   Line_No : Natural := 0;

   Parse_Error : exception;

   function Hex_Digit (C : Character) return Unsigned_64 is
   begin
      case C is
         when '0' .. '9' =>
            return Unsigned_64 (Character'Pos (C) - Character'Pos ('0'));
         when 'a' .. 'f' =>
            return Unsigned_64 (Character'Pos (C) - Character'Pos ('a') + 10);
         when 'A' .. 'F' =>
            return Unsigned_64 (Character'Pos (C) - Character'Pos ('A') + 10);
         when others =>
            raise Parse_Error with "bad hex digit '" & C & "'";
      end case;
   end Hex_Digit;

   --  64 big-endian hex digits; the first 16 form Limbs (3).
   function To_Limbs (S : String) return Limb_Array is
      R : Limb_Array := [others => 0];
      L : Limb_Index;
   begin
      if S'Length /= 64 then
         raise Parse_Error with "expected 64 hex digits, got '" & S & "'";
      end if;
      for I in 0 .. 63 loop
         L := Limb_Index (3 - I / 16);
         R (L) := Shift_Left (R (L), 4) or Hex_Digit (S (S'First + I));
      end loop;
      return R;
   end To_Limbs;

   function To_Element (S : String) return Element is
      L : constant Limb_Array := To_Limbs (S);
   begin
      if not Is_Canonical (L) then
         raise Parse_Error with "value not below p: " & S;
      end if;
      return From_Canonical (L);
   end To_Element;

   function Image (L : Limb_Array) return String is
      Hex : constant String := "0123456789abcdef";
      S   : String (1 .. 64);
      V   : Unsigned_64;
   begin
      for I in 0 .. 63 loop
         V := L (Limb_Index (3 - I / 16));
         S (I + 1) :=
           Hex (Integer (Shift_Right (V, 60 - 4 * (I mod 16)) and 15) + 1);
      end loop;
      return S;
   end Image;

   function Elem_Image (E : Element) return String is
     (Image (To_Canonical (E)));

   subtype Point is P256_Curve.Point;
   subtype Affine_Point is P256_Curve.Affine_Point;
   use type P256_Curve.Point;
   use type P256_Curve.Affine_Point;

   function Point_Image (P : Point) return String is
     (Elem_Image (P.X) & " " & Elem_Image (P.Y) & " " & Elem_Image (P.Z));

   --  The SHA-256 of the elements' 32-byte little-endian encodings.
   function Digest_Of (W : SAP.Element_Array) return String is
      Ctx : Sha256.Context := Sha256.Initial;
      D   : Bytes.Bytes_32;
      Hex : constant String := "0123456789abcdef";
      S   : String (1 .. 64);
   begin
      for I in W'Range loop
         Sha256.Update (Ctx, To_Bytes (W (I)));
      end loop;
      D := Sha256.Digest (Ctx);
      for I in 0 .. 31 loop
         S (2 * I + 1) := Hex (Integer (D (I) / 16) + 1);
         S (2 * I + 2) := Hex (Integer (D (I) mod 16) + 1);
      end loop;
      return S;
   end Digest_Of;

   type Element_Array_Access is access SAP.Element_Array;

   --  The elements of a signature witness file: 32-byte little-endian
   --  canonical encodings.
   function Read_Sig_File (Path : String) return Element_Array_Access is
      use Ada.Streams;
      use Ada.Streams.Stream_IO;
      F    : File_Type;
      Size : constant Natural := Natural (Ada.Directories.Size (Path));
      S    : Stream_Element_Array (1 .. Stream_Element_Offset (Size));
      Last : Stream_Element_Offset;
      R    : Element_Array_Access;
      B    : Bytes.Bytes_32;
      Ok   : Boolean;
   begin
      if Size mod 32 /= 0 then
         raise Parse_Error with "size of " & Path & " is not a multiple of 32";
      end if;
      Open (F, In_File, Path);
      Read (F, S, Last);
      Close (F);
      if Natural (Last) /= Size then
         raise Parse_Error with "short read of " & Path;
      end if;
      R := new SAP.Element_Array (0 .. Size / 32 - 1);
      for I in R'Range loop
         for K in 0 .. 31 loop
            B (K) := Unsigned_8 (S (Stream_Element_Offset (32 * I + K + 1)));
         end loop;
         From_Bytes (B, R (I), Ok);
         if not Ok then
            raise Parse_Error with "element" & I'Image & " of " & Path
              & " is not canonical";
         end if;
      end loop;
      return R;
   end Read_Sig_File;

   type Field_Bounds is record
      Lo, Hi : Natural;
   end record;
   type Field_Array is array (1 .. 10) of Field_Bounds;

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

   procedure Check (Ok : Boolean; Msg : String) is
   begin
      if Ok then
         Passed := Passed + 1;
      else
         Report_Failure (Msg);
      end if;
   end Check;

   procedure Check_Case (Line : String) is
      Fields : Field_Array;
      Count  : Natural;
   begin
      Split (Line, Fields, Count);
      if Count = 0 then
         return;
      end if;
      declare
         Op : constant String := Line (Fields (1).Lo .. Fields (1).Hi);
         function F (K : Positive) return String is
           (Line (Fields (K).Lo .. Fields (K).Hi));
         function Pt (K : Positive) return Point is
           (X => To_Element (F (K)), Y => To_Element (F (K + 1)),
            Z => To_Element (F (K + 2)));
      begin
         if Op = "add" then
            if Count /= 10 then
               raise Parse_Error with "add expects 9 values";
            end if;
            declare
               Got  : constant Point := P256_Curve.Add (Pt (2), Pt (5));
               Want : constant Point := Pt (8);
            begin
               Check (Got = Want, "add expected " & Point_Image (Want)
                      & " got " & Point_Image (Got));
            end;
         elsif Op = "double" then
            if Count /= 7 then
               raise Parse_Error with "double expects 6 values";
            end if;
            declare
               Got  : constant Point := P256_Curve.Double (Pt (2));
               Want : constant Point := Pt (5);
            begin
               Check (Got = Want, "double expected " & Point_Image (Want)
                      & " got " & Point_Image (Got));
            end;
         elsif Op = "affine" then
            if Count /= 6 then
               raise Parse_Error with "affine expects 5 values";
            end if;
            declare
               Got  : constant Affine_Point := P256_Curve.Affine (Pt (2));
               Want : constant Affine_Point :=
                 (X => To_Element (F (5)), Y => To_Element (F (6)));
            begin
               Check (Got = Want, "affine expected " & Elem_Image (Want.X) & " "
                      & Elem_Image (Want.Y) & " got " & Elem_Image (Got.X) & " "
                      & Elem_Image (Got.Y));
            end;
         elsif Op = "scalar" then
            if Count /= 6 then
               raise Parse_Error with "scalar expects 5 values";
            end if;
            declare
               K    : constant Limb_Array := To_Limbs (F (2));
               P    : constant Point :=
                 (X => To_Element (F (3)), Y => To_Element (F (4)), Z => One);
               R    : constant Point := P256_Curve.Scalar_Mul (K, P);
               Got  : constant Affine_Point := P256_Curve.Affine (R);
               Want : constant Affine_Point :=
                 (X => To_Element (F (5)), Y => To_Element (F (6)));
            begin
               Check (Got = Want, "scalar " & F (2) & " expected "
                      & Elem_Image (Want.X) & " " & Elem_Image (Want.Y) & " got "
                      & Elem_Image (Got.X) & " " & Elem_Image (Got.Y));
            end;
         elsif Op = "witness" then
            if Count /= 8 then
               raise Parse_Error with "witness expects 7 fields";
            end if;
            declare
               Pk : constant Affine_Point :=
                 (X => To_Element (F (3)), Y => To_Element (F (4)));
               W  : SAP.Element_Array (0 .. Ecdsa_Witness.Count + 1) :=
                 [others => Zero];
               Marker : constant Element := Of_Natural (12345);
            begin
               --  Two sentinels around the witness check the frame.
               W (0) := Marker;
               W (W'Last) := Marker;
               Ecdsa_Witness.Push_Legacy
                 (Pk, To_Limbs (F (5)), To_Limbs (F (6)), To_Limbs (F (7)),
                  W, 1);
               if W (0) /= Marker or else W (W'Last) /= Marker then
                  Report_Failure ("witness " & F (2) & " wrote outside its range");
               else
                  declare
                     D : constant String :=
                       Digest_Of (W (1 .. Ecdsa_Witness.Count));
                  begin
                     Check (D = F (8), "witness " & F (2) & " expected digest "
                            & F (8) & " got " & D);
                  end;
               end if;
            end;
         elsif Op = "witness_reject" then
            if Count /= 3 then
               raise Parse_Error with "witness_reject expects 2 fields";
            end if;
            declare
               S  : constant Limb_Array := To_Limbs (F (3));
               Pk : constant Affine_Point := (X => One, Y => One);
               W  : SAP.Element_Array (0 .. Ecdsa_Witness.Count - 1) :=
                 [others => Zero];
            begin
               if Q256_Field.Is_Canonical (Ecdsa_Witness.To_Q (S)) then
                  Report_Failure ("witness_reject " & F (2)
                                  & ": s accepted as canonical");
               else
                  --  The precondition of Push_Legacy refuses it: with the
                  --  executable contracts on, the call must raise.
                  begin
                     Ecdsa_Witness.Push_Legacy (Pk, S, S, S, W, 0);
                     Report_Failure ("witness_reject " & F (2)
                                     & ": Push_Legacy accepted s >= q");
                  exception
                     when Ada.Assertions.Assertion_Error =>
                        Passed := Passed + 1;
                  end;
               end if;
            end;
         elsif Op = "witness_file" then
            if Count /= 9 then
               raise Parse_Error with "witness_file expects 8 fields";
            end if;
            declare
               Pk    : constant Affine_Point :=
                 (X => To_Element (F (5)), Y => To_Element (F (6)));
               First : constant Natural := Natural'Value (F (4));
               File  : constant Element_Array_Access :=
                 Read_Sig_File (Mdoc_Dir & F (3) & "_sig_witness.bin");
               W     : SAP.Element_Array (0 .. Ecdsa_Witness.Count - 1) :=
                 [others => Zero];
               Bad   : Natural := Ecdsa_Witness.Count;
            begin
               Ecdsa_Witness.Push_Legacy
                 (Pk, To_Limbs (F (7)), To_Limbs (F (8)), To_Limbs (F (9)),
                  W, 0);
               if First + Ecdsa_Witness.Count - 1 > File'Last then
                  raise Parse_Error with "file too short for " & F (3);
               end if;
               for I in W'Range loop
                  if Bad = Ecdsa_Witness.Count
                    and then W (I) /= File (First + I)
                  then
                     Bad := I;
                  end if;
               end loop;
               if Bad = Ecdsa_Witness.Count then
                  Passed := Passed + 1;
               else
                  Report_Failure
                    ("witness_file " & F (2) & " "
                     & F (3) (F (3)'First .. F (3)'First + 7)
                     & ": first difference at element"
                     & Natural'Image (First + Bad) & " of the file: ours "
                     & Elem_Image (W (Bad)) & " file "
                     & Elem_Image (File (First + Bad)));
               end if;
            end;
         else
            raise Parse_Error with "unknown operation '" & Op & "'";
         end if;
      end;
   exception
      when E : others =>
         Report_Failure
           (Ada.Exceptions.Exception_Name (E) & ": "
            & Ada.Exceptions.Exception_Message (E));
   end Check_Case;

   procedure Run_File (Path : String) is
      File : TIO.File_Type;
   begin
      TIO.Put_Line ("P256_Curve and Ecdsa_Witness known-answer tests: " & Path);
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
   end Run_File;

begin
   if Ada.Command_Line.Argument_Count = 0 then
      Run_File (Default_Path);
   else
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         Run_File (Ada.Command_Line.Argument (I));
      end loop;
   end if;

   TIO.Put_Line ("passed" & Passed'Image & ", failed" & Failed'Image);
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end ECDSA_KAT;
