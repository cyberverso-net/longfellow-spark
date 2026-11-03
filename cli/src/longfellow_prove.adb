--  longfellow_prove: the command-line prover of Phase C (ADR 0049, ADR
--  0050). Outside the proof perimeter (SPARK_Mode Off): it parses the
--  command line, reads the circuit file and the inputs file (a JSON
--  array of decimal strings, the format of the upstream test data:
--  on GF(2^128) the integer's little-endian bytes are the element, on
--  P-256 the integer is reduced modulo p), chooses the randomness
--  source and writes the proof file; the proving is the SPARK library.
--
--  A circuit file in Pinned_Circuits is loaded without recomputing its
--  identifier, checked once already (ADR 0074); --check-circuit-id
--  recomputes it all the same.
--
--  Randomness: the operating system's generator (Os_Random) unless
--  --seed N is given, which selects Simple_Rng of the upstream
--  reference test and makes the proof reproducible, and predictable:
--  a test option, never the default.
--
--  Exit status: 0 when the proof is written; 1 on a prover status
--  (printed in lower case: input_length, not_satisfied,
--  not_in_subfield, config_invalid, exhausted); 2 on a usage or file
--  error, with the message on standard error.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Characters.Handling;
with Ada.Numerics.Big_Numbers.Big_Integers;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with Transcript;
with Ligero_Geometry;
with Prover_Status;
with Circuit_Status;
with Circuit_Reader;
with Zk_Prover;
with Cli_Random;
with Circuit_Reader_GF2_128;
with Circuit_Reader_P256;
with Pinned_Circuits;
with Zk_Prover_Cli_GF2_128;
with Zk_Prover_Cli_P256;

procedure Longfellow_Prove is

   package TIO renames Ada.Text_IO;
   package CL renames Ada.Command_Line;
   package BI renames Ada.Numerics.Big_Numbers.Big_Integers;
   use type BI.Big_Integer;

   Usage_Error : exception;

   Usage : constant String :=
     "usage: longfellow_prove --field gf2_128|p256 --circuit FILE"
     & " --inputs FILE.json --label STRING --rate-inv N --nreq N --ncol N"
     & " --out FILE [--seed N] [--check-circuit-id]";

   type String_Access is access String;

   Field_Arg, Circuit_Arg, Inputs_Arg, Label_Arg, Out_Arg : String_Access;
   Rate_Inv, Nreq, Ncol : Natural := 0;
   Seeded : Boolean := False;
   Full_Id : Boolean := False;
   Seed   : Unsigned_64 := 0;

   type Byte_Array_Access is access Byte_Array;

   function Read_File (Path : String) return Byte_Array_Access is
      use Ada.Streams;
      use Ada.Streams.Stream_IO;
      F    : File_Type;
      Size : Natural;
      R    : Byte_Array_Access;
   begin
      if not Ada.Directories.Exists (Path) then
         raise Usage_Error with "no such file: " & Path;
      end if;
      Size := Natural (Ada.Directories.Size (Path));
      declare
         S    : Stream_Element_Array (1 .. Stream_Element_Offset (Size));
         Last : Stream_Element_Offset;
      begin
         Open (F, In_File, Path);
         Read (F, S, Last);
         Close (F);
         if Natural (Last) /= Size then
            raise Usage_Error with "short read of " & Path;
         end if;
         R := new Byte_Array (0 .. Size - 1);
         for I in S'Range loop
            R (Natural (I) - 1) := Unsigned_8 (S (I));
         end loop;
      end;
      return R;
   end Read_File;

   procedure Write_File (Path : String; B : Byte_Array) is
      use Ada.Streams;
      use Ada.Streams.Stream_IO;
      F : File_Type;
      S : Stream_Element_Array (1 .. Stream_Element_Offset (B'Length));
   begin
      for I in B'Range loop
         S (Stream_Element_Offset (I - B'First + 1)) := Stream_Element (B (I));
      end loop;
      Create (F, Out_File, Path);
      Write (F, S);
      Close (F);
   exception
      when others =>
         raise Usage_Error with "cannot write " & Path;
   end Write_File;

   function To_Label (S : String) return Byte_Array is
      R : Byte_Array (0 .. S'Length - 1);
   begin
      for I in R'Range loop
         R (I) := Character'Pos (S (S'First + I));
      end loop;
      return R;
   end To_Label;

   function Lower (S : String) return String
     renames Ada.Characters.Handling.To_Lower;

   --  The decimal strings of a JSON array of strings, in order. The
   --  grammar accepted is exactly that: '[', strings of decimal digits
   --  in double quotes separated by commas, ']', with blanks between.
   type Decimal_List is array (Positive range <>) of String_Access;
   type Decimal_List_Access is access Decimal_List;

   procedure Free_String is
     new Ada.Unchecked_Deallocation (String, String_Access);
   procedure Free_List is
     new Ada.Unchecked_Deallocation (Decimal_List, Decimal_List_Access);
   procedure Free_Bytes is
     new Ada.Unchecked_Deallocation (Byte_Array, Byte_Array_Access);

   --  The strings of a list, then the list.
   procedure Free_Decimals (D : in out Decimal_List_Access) is
   begin
      for S of D.all loop
         Free_String (S);
      end loop;
      Free_List (D);
   end Free_Decimals;

   function Parse_Inputs (Text : Byte_Array) return Decimal_List_Access is
      Max  : constant := 2**20;
      Tmp  : Decimal_List_Access := new Decimal_List (1 .. Max);
      N    : Natural := 0;
      P    : Natural := Text'First;

      function At_End return Boolean is (P > Text'Last);
      function Cur return Character is (Character'Val (Text (P)));

      procedure Skip_Blanks is
      begin
         while not At_End and then Cur in ' ' | ASCII.HT | ASCII.LF | ASCII.CR
         loop
            P := P + 1;
         end loop;
      end Skip_Blanks;

      procedure Expect (C : Character) is
      begin
         Skip_Blanks;
         if At_End or else Cur /= C then
            raise Usage_Error with "inputs: expected '" & C & "'";
         end if;
         P := P + 1;
      end Expect;
   begin
      Expect ('[');
      Skip_Blanks;
      if not At_End and then Cur = ']' then
         P := P + 1;
         Free_List (Tmp);
         return new Decimal_List (1 .. 0);
      end if;
      loop
         Expect ('"');
         declare
            Start : constant Natural := P;
         begin
            while not At_End and then Cur in '0' .. '9' loop
               P := P + 1;
            end loop;
            if P = Start then
               raise Usage_Error with "inputs: a decimal string is expected";
            end if;
            if N = Max then
               raise Usage_Error with "inputs: too many inputs";
            end if;
            N := N + 1;
            Tmp (N) := new String (1 .. P - Start);
            for K in Start .. P - 1 loop
               Tmp (N) (K - Start + 1) := Character'Val (Text (K));
            end loop;
         end;
         Expect ('"');
         Skip_Blanks;
         if At_End then
            raise Usage_Error with "inputs: unterminated array";
         end if;
         if Cur = ']' then
            P := P + 1;
            exit;
         end if;
         Expect (',');
      end loop;
      Skip_Blanks;
      if not At_End then
         raise Usage_Error with "inputs: trailing characters";
      end if;
      --  The list at its length; the provisional one of 2^20 entries,
      --  16 MB, is freed.
      declare
         R : constant Decimal_List_Access := new Decimal_List'(Tmp (1 .. N));
      begin
         Free_List (Tmp);
         return R;
      end;
   end Parse_Inputs;

   --  The decimal strings of the inputs file, its bytes freed once read.
   function Parse_Inputs_File (Path : String) return Decimal_List_Access is
      B : Byte_Array_Access := Read_File (Path);
      D : constant Decimal_List_Access := Parse_Inputs (B.all);
   begin
      Free_Bytes (B);
      return D;
   end Parse_Inputs_File;

   --  The little-endian bytes of a non-negative integer, Size of them;
   --  the integer must fit.
   function LE_Bytes (V : BI.Big_Integer; Size : Positive) return Byte_Array is
      R : Byte_Array (0 .. Size - 1) := [others => 0];
      X : BI.Big_Integer := V;
      B : constant BI.Big_Integer := BI.To_Big_Integer (256);
   begin
      for I in R'Range loop
         R (I) := Unsigned_8 (BI.To_Integer (X mod B));
         X := X / B;
      end loop;
      if X /= BI.To_Big_Integer (0) then
         raise Usage_Error with "inputs: a value does not fit the field";
      end if;
      return R;
   end LE_Bytes;

   P256_Modulus : constant BI.Big_Integer :=
     BI.From_String
       ("115792089210356248762697446949407573530086143415290314195533631308"
        & "867097853951");

   generic
      with package ZKP is new Zk_Prover (<>);
      with package CR is new Circuit_Reader
        (SA => ZKP.LPR.LV.ST.SA, others => <>);
      Reduce : Boolean;
   function Run return CL.Exit_Status;

   function Run return CL.Exit_Status is
      pragma Suppress (Predicate_Check);
      use type Circuit_Status.Status;
      use type Prover_Status.Status;
      package F renames ZKP.LPR.LV.ST.SA.F;
      procedure Read_Circuit is new Pinned_Circuits.Read (CR);

      Cfg : constant Ligero_Geometry.Config :=
        (Rate_Inv => Rate_Inv, Num_Queries => Nreq, Encoded_Len => Ncol);
      C   : CR.Circuit_Access;
      H   : CR.Header;
      CSt : Circuit_Status.Status;
      PSt : Prover_Status.Status;
      Len : Natural;
   begin
      if not Ligero_Geometry.Valid (Cfg) then
         TIO.Put_Line ("config_invalid");
         return 1;
      end if;
      declare
         B : constant Byte_Array_Access := Read_File (Circuit_Arg.all);
      begin
         Read_Circuit (B.all, Full_Id, C, H, CSt);
      end;
      if CSt /= Circuit_Status.Ok then
         TIO.Put_Line ("circuit " & Lower (CSt'Image));
         return 1;
      end if;
      --  The predicate of the circuit, checked once here, where the
      --  circuit enters the program; the calls below do not check it
      --  again (ADR 0072). The loader proves it, so this test is the
      --  run-time guard of the boundary, not a new property.
      if not ZKP.LPR.LV.ST.SA.Well_Formed (C.all) then
         TIO.Put_Line
           ("circuit " & Lower (Circuit_Status.Not_Well_Formed'Image));
         CR.Free (C);
         return 1;
      end if;
      if not ZKP.Config_Fits (Cfg, ZKP.Shape_Of (C.all)) then
         TIO.Put_Line ("config_invalid");
         CR.Free (C);
         return 1;
      end if;
      if C.Ninput = 0 then
         TIO.Put_Line ("circuit has no inputs");
         CR.Free (C);
         return 1;
      end if;
      declare
         Dec    : Decimal_List_Access := Parse_Inputs_File (Inputs_Arg.all);
         Inputs : ZKP.Element_Array (0 .. Dec'Length - 1);
         Ok     : Boolean;
      begin
         for I in Inputs'Range loop
            declare
               V : BI.Big_Integer := BI.From_String (Dec (I + 1).all);
            begin
               if Reduce then
                  V := V mod P256_Modulus;
               end if;
               F.From_Bytes (LE_Bytes (V, F.Serialized_Size), Inputs (I), Ok);
               if not Ok then
                  raise Usage_Error with "inputs: value" & I'Image
                    & " is not a field element";
               end if;
            end;
         end loop;
         Free_Decimals (Dec);
         declare
            Label : constant Byte_Array := To_Label (Label_Arg.all);
            Max   : constant Natural :=
              ZKP.Max_Proof_Len
                (Cfg, ZKP.Shape_Of (C.all), H.Subfield_Boundary);
            Out_B : constant Byte_Array_Access :=
              new Byte_Array (0 .. Max - 1);
         begin
            if Seeded then
               Cli_Random.Set_Seed (Seed);
            end if;
            ZKP.Prove (Label, H.Id, H.Subfield_Boundary, Cfg, C.all,
                       Inputs, Out_B.all, Len, PSt);
            CR.Free (C);
            if PSt /= Prover_Status.Ok then
               TIO.Put_Line (Lower (PSt'Image));
               return 1;
            end if;
            Write_File (Out_Arg.all, Out_B (0 .. Len - 1));
            TIO.Put_Line ("ok:" & Len'Image & " bytes written to "
                          & Out_Arg.all);
            return 0;
         end;
      end;
   end Run;

   function Run_GF is new Run
     (ZKP => Zk_Prover_Cli_GF2_128, CR => Circuit_Reader_GF2_128,
      Reduce => False);

   function Run_P is new Run
     (ZKP => Zk_Prover_Cli_P256, CR => Circuit_Reader_P256,
      Reduce => True);

   procedure Parse_Arguments is
      I : Positive := 1;

      function Value return String is
      begin
         if I + 1 > CL.Argument_Count then
            raise Usage_Error with CL.Argument (I) & " needs a value";
         end if;
         I := I + 2;
         return CL.Argument (I - 1);
      end Value;

      function Number return Natural is
         S : constant String := Value;
      begin
         return Natural'Value (S);
      exception
         when others =>
            raise Usage_Error with "not a number: " & S;
      end Number;
   begin
      while I <= CL.Argument_Count loop
         declare
            Opt : constant String := CL.Argument (I);
         begin
            if Opt = "--field" then
               Field_Arg := new String'(Value);
            elsif Opt = "--circuit" then
               Circuit_Arg := new String'(Value);
            elsif Opt = "--inputs" then
               Inputs_Arg := new String'(Value);
            elsif Opt = "--label" then
               Label_Arg := new String'(Value);
            elsif Opt = "--out" then
               Out_Arg := new String'(Value);
            elsif Opt = "--rate-inv" then
               Rate_Inv := Number;
            elsif Opt = "--nreq" then
               Nreq := Number;
            elsif Opt = "--ncol" then
               Ncol := Number;
            elsif Opt = "--seed" then
               declare
                  S : constant String := Value;
               begin
                  Seed   := Unsigned_64'Value (S);
                  Seeded := True;
               exception
                  when others =>
                     raise Usage_Error with "not a seed: " & S;
               end;
            elsif Opt = "--check-circuit-id" then
               Full_Id := True;
               I := I + 1;
            elsif Opt = "--help" or else Opt = "-h" then
               TIO.Put_Line (Usage);
               CL.Set_Exit_Status (0);
               raise Usage_Error with "";
            else
               raise Usage_Error with "unknown option " & Opt;
            end if;
         end;
      end loop;
      if Field_Arg = null or else Circuit_Arg = null or else Inputs_Arg = null
        or else Label_Arg = null or else Out_Arg = null
        or else Rate_Inv = 0 or else Nreq = 0 or else Ncol = 0
      then
         raise Usage_Error with "missing argument";
      end if;
      --  The precondition of the transcript on the label, checked here:
      --  the library units run without run-time checks (ADR 0068).
      if Label_Arg'Length > Transcript.Max_Payload then
         raise Usage_Error with "label too long";
      end if;
   end Parse_Arguments;

begin
   Parse_Arguments;
   if Field_Arg.all = "gf2_128" then
      CL.Set_Exit_Status (Run_GF);
   elsif Field_Arg.all = "p256" then
      CL.Set_Exit_Status (Run_P);
   else
      raise Usage_Error with "unknown field " & Field_Arg.all;
   end if;
exception
   when E : Usage_Error =>
      if Ada.Exceptions.Exception_Message (E) /= "" then
         TIO.Put_Line (TIO.Standard_Error,
                       "longfellow_prove: "
                       & Ada.Exceptions.Exception_Message (E));
         TIO.Put_Line (TIO.Standard_Error, Usage);
         CL.Set_Exit_Status (2);
      end if;
   when E : Program_Error =>
      TIO.Put_Line (TIO.Standard_Error,
                    "longfellow_prove: "
                    & Ada.Exceptions.Exception_Message (E));
      CL.Set_Exit_Status (2);
end Longfellow_Prove;
