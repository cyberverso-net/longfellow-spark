pragma SPARK_Mode (Off);

with Ada.Exceptions;
with Ada.Text_IO;

package body Sumcheck_KAT_Generic is

   package TIO renames Ada.Text_IO;
   use SA;
   use type SA.Element;

   Line_No : Natural := 0;
   N_Pass  : Natural := 0;
   N_Fail  : Natural := 0;

   Parse_Error : exception;

   --  Blank-separated fields of a line, as index bounds into it.
   type Field_Bounds is record
      Lo, Hi : Natural;
   end record;
   Max_Fields : constant := 4096;
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
      N_Fail := N_Fail + 1;
      TIO.Put_Line
        ("FAIL " & Field_Name & " line" & Line_No'Image & ": " & Msg);
   end Report_Failure;

   procedure Check (Ok : Boolean; Msg : String) is
   begin
      if Ok then
         N_Pass := N_Pass + 1;
      else
         Report_Failure (Msg);
      end if;
   end Check;

   --  The circuit block under construction.
   Max_Layers : constant := 64;
   Max_Terms  : constant := 4096;
   Max_Wires  : constant := 4096;

   type Layer_Rec is record
      Logw, NW_In, First, Last : Natural;
   end record;
   type Layer_Buf is array (0 .. Max_Layers - 1) of Layer_Rec;
   type Term_Buf is array (1 .. Max_Terms) of Term;
   type Wire_Buf is array (0 .. Max_Wires - 1) of Element;
   type Segment_Rec is record
      Given  : Boolean := False;
      Length : Natural := 0;
      First  : Natural := 0;   --  offset into Expected
   end record;
   type Segment_Buf is array (0 .. Max_Layers) of Segment_Rec;

   In_Circuit : Boolean := False;
   C_Name     : String (1 .. 64);
   C_Name_Len : Natural;
   C_Noutput, C_Ninput, C_Npublic, C_NL : Natural;
   Layers     : Layer_Buf;
   Terms      : Term_Buf;
   N_Terms    : Natural;
   Cur_Layer  : Integer;        --  layer whose terms are being read, or -1
   Terms_Left : Natural;
   Witness    : Wire_Buf;
   Have_Witness : Boolean;
   Expected   : Wire_Buf;
   N_Expected : Natural;
   Segments   : Segment_Buf;
   Expect_Ok  : Boolean;
   Have_Expect : Boolean;

   function Nat (S : String) return Natural is
   begin
      return Natural'Value (S);
   exception
      when others => raise Parse_Error with "bad number '" & S & "'";
   end Nat;

   procedure Finish_Circuit is
      Name : constant String := C_Name (1 .. C_Name_Len);
   begin
      if not Have_Witness or else not Have_Expect then
         raise Parse_Error with "circuit " & Name & " incomplete";
      end if;
      if Cur_Layer /= C_NL - 1 or else Terms_Left /= 0 then
         raise Parse_Error with "circuit " & Name & ": layers incomplete";
      end if;
      declare
         Raw : Raw_Circuit (Last_Layer => C_NL - 1, NT => N_Terms);
      begin
         Raw.Noutput := C_Noutput;
         Raw.Ninput  := C_Ninput;
         Raw.Npublic := C_Npublic;
         for J in 0 .. C_NL - 1 loop
            Raw.Layers (J) := (Logw  => Layers (J).Logw,
                               NW_In => Layers (J).NW_In,
                               First => Layers (J).First,
                               Last  => Layers (J).Last);
         end loop;
         for I in 1 .. N_Terms loop
            Raw.Terms (I) := Terms (I);
         end loop;
         Check (Well_Formed (Raw), "circuit " & Name & " not well formed");
         if not Well_Formed (Raw) then
            return;
         end if;
         declare
            C     : constant Circuit := Raw;   --  predicate checked here
            W     : Element_Array (0 .. C_Ninput - 1);
            Wires : Element_Array (0 .. Total_Wires (C) - 1) :=
              [others => Zero];
            Ok    : Boolean;
         begin
            for I in W'Range loop
               W (I) := Witness (I);
            end loop;
            Eval_Circuit (C, W, Wires, Ok);
            Check (Ok = Expect_Ok,
                   "circuit " & Name & ": status " & Ok'Image
                   & ", expected " & Expect_Ok'Image);
            for J in 0 .. C_NL loop
               if Segments (J).Given then
                  declare
                     Size : constant Natural := Seg_Size (C, J);
                     Base : constant Natural := Off (C, J);
                     Good : Boolean := Segments (J).Length = Size;
                  begin
                     if Good then
                        for G in 0 .. Size - 1 loop
                           if Wires (Base + G)
                             /= Expected (Segments (J).First + G)
                           then
                              Good := False;
                              TIO.Put_Line
                                ("  wire" & G'Image & " of segment" & J'Image
                                 & ": got " & Image (Wires (Base + G))
                                 & " expected "
                                 & Image (Expected (Segments (J).First + G)));
                           end if;
                        end loop;
                     end if;
                     Check (Good, "circuit " & Name & ": segment" & J'Image);
                  end;
               end if;
            end loop;
         end;
      end;
   end Finish_Circuit;

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

      function E (K : Positive) return Element is (To_Element (F (K)));

      --  Elements at fields From .. From + N - 1 as an array 0 .. N - 1.
      function Elements (From, N : Natural) return Element_Array is
         R : Element_Array (0 .. N - 1);
      begin
         for I in R'Range loop
            R (I) := E (From + I);
         end loop;
         return R;
      end Elements;

   begin
      Split (Line, Fields, Count);
      if Count = 0 then
         return;
      end if;
      declare
         Op : constant String := F (1);
      begin
         if Op = "field" then
            if F (2) /= Field_Name then
               raise Parse_Error with "file is for field " & F (2);
            end if;
         elsif Op = "const" then
            declare
               Which : constant String := F (2);
               V     : constant Element := E (3);
               D0    : constant Element := (Zero - One) * (Zero - P2);
               D1    : constant Element := (One - Zero) * (One - P2);
               D2    : constant Element := (P2 - Zero) * (P2 - One);
            begin
               if Which = "p2" then
                  Check (V = P2, "P2 differs from the library constant");
               elsif Which = "l0inv" then
                  Check (V = L0_Den_Inv and then D0 * L0_Den_Inv = One,
                         "L0_Den_Inv: constant or d0 * inv /= 1");
               elsif Which = "l1inv" then
                  Check (V = L1_Den_Inv and then D1 * L1_Den_Inv = One,
                         "L1_Den_Inv: constant or d1 * inv /= 1");
               elsif Which = "l2inv" then
                  Check (V = L2_Den_Inv and then D2 * L2_Den_Inv = One,
                         "L2_Den_Inv: constant or d2 * inv /= 1");
               else
                  raise Parse_Error with "unknown constant " & Which;
               end if;
            end;
         elsif Op = "eq" then
            declare
               N    : constant Natural := Nat (F (2));
               X    : constant Natural := Nat (F (3));
               R    : constant Element_Array := Elements (4, N);
               Want : constant Element := E (4 + N);
               Got  : constant Element := Eq (R, X, N);
            begin
               Check (Got = Want, "eq n=" & N'Image & " x=" & X'Image
                      & " got " & Image (Got) & " expected " & Image (Want));
            end;
         elsif Op = "eq2" then
            declare
               N     : constant Natural := Nat (F (2));
               X     : constant Natural := Nat (F (3));
               Alpha : constant Element := E (4);
               G0    : constant Element_Array := Elements (5, N);
               G1    : constant Element_Array := Elements (5 + N, N);
               Want  : constant Element := E (5 + 2 * N);
               Got   : constant Element := Eq2 (X, N, G0, G1, Alpha);
            begin
               Check (Got = Want, "eq2 n=" & N'Image & " x=" & X'Image
                      & " got " & Image (Got) & " expected " & Image (Want));
            end;
         elsif Op = "bindeq" then
            declare
               N    : constant Natural := Nat (F (2));
               C    : constant Element_Array := Elements (3, N);
               Want : constant Element_Array := Elements (3 + N, 2 ** N);
               B    : Element_Array (0 .. 2 ** N - 1);
               Good : Boolean := True;
               Agrees : Boolean := True;
            begin
               Bindeq (C, B);
               for I in B'Range loop
                  Good := Good and then B (I) = Want (I);
                  Agrees := Agrees and then B (I) = Eq (C, I, N);
               end loop;
               Check (Good, "bindeq n=" & N'Image & " differs from the file");
               Check (Agrees, "bindeq n=" & N'Image & " disagrees with eq");
            end;
         elsif Op = "bind" then
            declare
               Len  : constant Natural := Nat (F (2));
               X    : constant Element := E (3);
               A    : constant Element_Array := Elements (4, Len);
               Want : constant Element_Array :=
                 Elements (4 + Len, (Len + 1) / 2);
               B    : Element_Array (0 .. (Len + 1) / 2 - 1);
            begin
               Bind (A, X, B);
               Check (B = Want, "bind len=" & Len'Image);
            end;
         elsif Op = "lagrange" then
            declare
               R    : constant Element := E (2);
               Want : constant Basis := [E (3), E (4), E (5)];
               Got  : constant Basis := Lagrange_Basis (R);
            begin
               Check (Got = Want, "lagrange r=" & Image (R));
            end;
         elsif Op = "circuit" then
            if In_Circuit then
               raise Parse_Error with "nested circuit";
            end if;
            In_Circuit := True;
            C_Name_Len := Natural'Min (F (2)'Length, C_Name'Length);
            C_Name (1 .. C_Name_Len) :=
              F (2) (F (2)'First .. F (2)'First + C_Name_Len - 1);
            C_Noutput := Nat (F (3));
            C_Ninput  := Nat (F (4));
            C_Npublic := Nat (F (5));
            C_NL      := Nat (F (6));
            N_Terms   := 0;
            Cur_Layer := -1;
            Terms_Left := 0;
            Have_Witness := False;
            Have_Expect := False;
            N_Expected := 0;
            Segments := [others => (False, 0, 0)];
         elsif Op = "layer" then
            if not In_Circuit or else Terms_Left /= 0
              or else Nat (F (2)) /= Cur_Layer + 1
            then
               raise Parse_Error with "unexpected layer";
            end if;
            Cur_Layer := Cur_Layer + 1;
            Layers (Cur_Layer) := (Logw  => Nat (F (3)),
                                   NW_In => Nat (F (4)),
                                   First => N_Terms + 1,
                                   Last  => N_Terms + Nat (F (5)));
            Terms_Left := Nat (F (5));
         elsif Op = "term" then
            if not In_Circuit or else Terms_Left = 0 then
               raise Parse_Error with "unexpected term";
            end if;
            N_Terms := N_Terms + 1;
            Terms (N_Terms) := (K  => E (5),
                                G  => Nat (F (2)),
                                H0 => Nat (F (3)),
                                H1 => Nat (F (4)));
            Terms_Left := Terms_Left - 1;
         elsif Op = "witness" then
            if not In_Circuit or else Count - 1 /= C_Ninput then
               raise Parse_Error with "witness length";
            end if;
            for I in 0 .. C_Ninput - 1 loop
               Witness (I) := E (2 + I);
            end loop;
            Have_Witness := True;
         elsif Op = "wires" then
            declare
               J : constant Natural := Nat (F (2));
               N : constant Natural := Count - 2;
            begin
               if not In_Circuit or else J > C_NL then
                  raise Parse_Error with "unexpected wires";
               end if;
               Segments (J) := (True, N, N_Expected);
               for I in 0 .. N - 1 loop
                  Expected (N_Expected + I) := E (3 + I);
               end loop;
               N_Expected := N_Expected + N;
            end;
         elsif Op = "expect" then
            if not In_Circuit then
               raise Parse_Error with "unexpected expect";
            end if;
            if F (2) = "ok" then
               Expect_Ok := True;
            elsif F (2) = "fail" then
               Expect_Ok := False;
            else
               raise Parse_Error with "expect ok|fail";
            end if;
            Have_Expect := True;
         elsif Op = "end" then
            if not In_Circuit then
               raise Parse_Error with "unexpected end";
            end if;
            In_Circuit := False;
            Finish_Circuit;
         else
            raise Parse_Error with "unknown operation '" & Op & "'";
         end if;
      end;
   exception
      when Ex : others =>
         --  Parse errors and contract violations (assertion failures
         --  raised inside the library) both count as failures.
         In_Circuit := False;
         Report_Failure
           (Ada.Exceptions.Exception_Name (Ex) & ": "
            & Ada.Exceptions.Exception_Message (Ex));
   end Check_Case;

   procedure Run_File (Path : String; Passed, Failed : in out Natural) is
      File : TIO.File_Type;
   begin
      TIO.Put_Line ("Sumcheck_Algebra (" & Field_Name
                    & ") known-answer tests: " & Path);
      N_Pass := 0;
      N_Fail := 0;
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
      if In_Circuit then
         Report_Failure ("file ends inside a circuit block");
         In_Circuit := False;
      end if;
      Passed := Passed + N_Pass;
      Failed := Failed + N_Fail;
   end Run_File;

end Sumcheck_KAT_Generic;
