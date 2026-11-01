--  FIRST_STEP_BENCH: the first step of a layer from the packed form
--  (ADR 0080, block 2) against the expanded path, on one circuit file.
--  For every layer: the terms, the runs of equal hands, the bytes of
--  the expanded layer and of the working array the packed path
--  allocates (one entry per run), and the time of Bind_Quad on the
--  expanded layer against Bind_Quad_Packed on the packed form, the
--  median of three calls each, with pseudo-random challenges; then the
--  sums over the layers. The two values are compared on every call.
--
--  Measurement code, outside the proof perimeter: SPARK_Mode is Off.
--  Built in the release project cli/ (assertions off, -O3), the build
--  whose times mean something: the assertion-enabled build of tests/
--  executes the loop invariants and the ghost references of the
--  kernels, at a cost quadratic in the table of eq and in the layer,
--  so circuit_kat compares the two paths there on the small layers
--  only. Not run by make check. Documentation: docs/guide/03-sumcheck.md
--  (Section 3.5), docs/guide/performance.md.
--
--  Usage: first_step_bench --field gf2_128|p256 --circuit FILE
--  Exit status: 0 when every layer agrees, 1 when a layer disagrees or
--  the file does not load, 2 on a usage error.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Real_Time;
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
with Packed_HQuad;
with Packed_HQuad_GF2_128;
with Packed_HQuad_P256;

procedure First_Step_Bench is

   package CL renames Ada.Command_Line;
   package TIO renames Ada.Text_IO;

   Usage_Error : exception;

   Usage : constant String :=
     "usage: first_step_bench --field gf2_128|p256 --circuit FILE";

   type String_Access is access String;
   Field_Arg, Circuit_Arg : String_Access;

   type Byte_Array_Access is access Byte_Array;
   procedure Free is
     new Ada.Unchecked_Deallocation (Byte_Array, Byte_Array_Access);

   --  The whole file, read through a heap buffer: a circuit file is
   --  several megabytes.
   function Read_File (Path : String) return Byte_Array_Access is
      use Ada.Streams;
      use Ada.Streams.Stream_IO;
      type Buffer_Access is access Stream_Element_Array;
      procedure Free_Buffer is
        new Ada.Unchecked_Deallocation (Stream_Element_Array, Buffer_Access);
      F    : File_Type;
      Size : Natural;
      S    : Buffer_Access;
      Last : Stream_Element_Offset;
      R    : Byte_Array_Access;
   begin
      if not Ada.Directories.Exists (Path) then
         raise Usage_Error with "no such file: " & Path;
      end if;
      Size := Natural (Ada.Directories.Size (Path));
      S := new Stream_Element_Array (1 .. Stream_Element_Offset (Size));
      Open (F, In_File, Path);
      Read (F, S.all, Last);
      Close (F);
      if Natural (Last) /= Size then
         Free_Buffer (S);
         raise Usage_Error with "short read of " & Path;
      end if;
      R := new Byte_Array (0 .. Size - 1);
      for I in S'Range loop
         R (Natural (I) - 1) := Unsigned_8 (S (I));
      end loop;
      Free_Buffer (S);
      return R;
   end Read_File;

   --  Pseudo-random challenges, the same sequence on every run.
   Seed : Unsigned_64 := 16#9E37_79B9_7F4A_7C15#;

   function Next return Unsigned_64 is
   begin
      Seed := Seed * 6364136223846793005 + 1442695040888963407;
      return Seed;
   end Next;

   function GF_Random return GF2_128.Element is
      R : GF2_128.Element := GF2_128.Zero;
   begin
      R.Limbs (0) := Next;
      R.Limbs (1) := Next;
      return R;
   end GF_Random;

   --  Below p: the top four bits of the most significant limb are 0.
   function P_Random return P256_Field.Element is
      R : P256_Field.Limb_Array := [others => 0];
   begin
      for L in R'Range loop
         R (L) := Next;
      end loop;
      R (R'Last) := Shift_Right (R (R'Last), 4);
      return P256_Field.From_Canonical (R);
   end P_Random;

   --  The measurement of one field.
   generic
      with package CR is new Circuit_Reader (<>);
      with package PQ is new Packed_HQuad
        (SA => CR.SA, PC => CR.PC, others => <>);
      with function Random_Element return CR.SA.Element;
   procedure Bench (B : Byte_Array; Agreed : out Boolean);

   procedure Bench (B : Byte_Array; Agreed : out Boolean) is
      package SA renames CR.SA;
      use type Circuit_Status.Status;
      use type Ada.Real_Time.Time;
      use type SA.Element;
      use type CR.Circuit_Access;
      use type CR.Packed_Access;

      C  : CR.Circuit_Access;
      P  : CR.Packed_Access;
      H  : CR.Header;
      St : Circuit_Status.Status;

      G0, G1, HC0, HC1    : SA.Element_Array (0 .. SA.Max_Logw - 1);
      Alpha, Beta, V1, V2 : SA.Element;
      Logv, Logw, First, Last, NR : Natural;

      Term_Bytes : constant Long_Long_Integer :=
        Long_Long_Integer (SA.Term_Array'Component_Size / 8);

      type Micros is array (1 .. 3) of Long_Long_Integer;

      function Median (M : Micros) return Long_Long_Integer is
        (Long_Long_Integer'Max
           (Long_Long_Integer'Min (M (1), M (2)),
            Long_Long_Integer'Min
              (Long_Long_Integer'Max (M (1), M (2)), M (3))));

      function Elapsed (T0 : Ada.Real_Time.Time) return Long_Long_Integer
      is (Long_Long_Integer
            (Ada.Real_Time.To_Duration (Ada.Real_Time.Clock - T0)
             * 1_000_000));

      function Ceil_Log2 (N : Natural) return Natural is
         L : Natural := 0;
      begin
         while 2**L < N loop
            L := L + 1;
         end loop;
         return L;
      end Ceil_Log2;

      Sum_Terms, Sum_Runs, Sum_Layer, Sum_Work, Max_Layer, Max_Work,
      Sum_Exp, Sum_Pck : Long_Long_Integer := 0;
   begin
      Agreed := True;
      CR.Read (B, C, H, St);
      if St /= Circuit_Status.Ok or else C = null then
         TIO.Put_Line ("the circuit does not load: "
                       & Circuit_Status.Status'Image (St));
         Agreed := False;
         return;
      end if;
      CR.Read_Packed (B, False, [others => 0], P, H, St);
      if St /= Circuit_Status.Ok or else P = null then
         TIO.Put_Line ("the packed form does not load: "
                       & Circuit_Status.Status'Image (St));
         CR.Free (C);
         Agreed := False;
         return;
      end if;
      TIO.Put_Line
        ("packed form"
         & Long_Long_Integer'Image (Long_Long_Integer (P.all'Size) / 8)
         & " bytes, expanded"
         & Long_Long_Integer'Image (Long_Long_Integer (C.all'Size) / 8)
         & " bytes," & Natural'Image (P.Last_Layer + 1) & " layers");
      for J in 0 .. P.Last_Layer loop
         First := P.Layers (J).First;
         Last  := P.Layers (J).Last;
         Logw  := P.Layers (J).Logw;
         Logv  := (if J = 0 then Ceil_Log2 (P.Noutput)
                   else P.Layers (J - 1).Logw);
         for R in G0'Range loop
            G0 (R)  := Random_Element;
            G1 (R)  := Random_Element;
            HC0 (R) := Random_Element;
            HC1 (R) := Random_Element;
         end loop;
         Alpha := Random_Element;
         Beta  := Random_Element;
         if Logv > SA.Max_Bindeq_Log or else Logw > SA.Max_Bindeq_Log then
            TIO.Put_Line ("layer" & J'Image & ": beyond the tables (Logv"
                          & Logv'Image & ", Logw" & Logw'Image
                          & "), not timed");
         else
            PQ.Layer_Runs (P.all, J, NR);
            declare
               TE, TP      : Micros;
               T0          : Ada.Real_Time.Time;
               Terms       : constant Natural := Last + 1 - First;
               Layer_Bytes : constant Long_Long_Integer :=
                 Long_Long_Integer (Terms) * Term_Bytes;
               Work_Bytes  : constant Long_Long_Integer :=
                 Long_Long_Integer (NR) * Term_Bytes;
            begin
               for R in Micros'Range loop
                  T0 := Ada.Real_Time.Clock;
                  PQ.HQ.Bind_Quad (C.Terms (First .. Last), Logv, G0, G1,
                                   HC0, HC1, Logw, Alpha, Beta, V1);
                  TE (R) := Elapsed (T0);
                  T0 := Ada.Real_Time.Clock;
                  PQ.Bind_Quad_Packed (P.all, J, Logv, G0, G1, HC0, HC1,
                                       Logw, Alpha, Beta, V2);
                  TP (R) := Elapsed (T0);
                  if V1 /= V2 then
                     TIO.Put_Line ("layer" & J'Image
                                   & ": the two paths disagree");
                     Agreed := False;
                  end if;
               end loop;
               TIO.Put_Line
                 ("layer" & J'Image & ":" & Terms'Image & " terms,"
                  & NR'Image & " runs; layer" & Layer_Bytes'Image
                  & " bytes, working array" & Work_Bytes'Image
                  & " bytes; Bind_Quad" & Median (TE)'Image
                  & " us, Bind_Quad_Packed" & Median (TP)'Image & " us");
               Sum_Terms := Sum_Terms + Long_Long_Integer (Terms);
               Sum_Runs  := Sum_Runs + Long_Long_Integer (NR);
               Sum_Layer := Sum_Layer + Layer_Bytes;
               Sum_Work  := Sum_Work + Work_Bytes;
               Max_Layer := Long_Long_Integer'Max (Max_Layer, Layer_Bytes);
               Max_Work  := Long_Long_Integer'Max (Max_Work, Work_Bytes);
               Sum_Exp   := Sum_Exp + Median (TE);
               Sum_Pck   := Sum_Pck + Median (TP);
            end;
         end if;
      end loop;
      TIO.Put_Line
        ("all layers:" & Sum_Terms'Image & " terms," & Sum_Runs'Image
         & " runs; layers" & Sum_Layer'Image & " bytes (largest"
         & Max_Layer'Image & "), working arrays" & Sum_Work'Image
         & " bytes (largest" & Max_Work'Image & "); Bind_Quad"
         & Sum_Exp'Image & " us, Bind_Quad_Packed" & Sum_Pck'Image
         & " us");
      CR.Free_Packed (P);
      CR.Free (C);
   end Bench;

   procedure GF_Bench is
     new Bench (Circuit_Reader_GF2_128, Packed_HQuad_GF2_128, GF_Random);
   procedure P_Bench is
     new Bench (Circuit_Reader_P256, Packed_HQuad_P256, P_Random);

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
   begin
      while I <= CL.Argument_Count loop
         declare
            Opt : constant String := CL.Argument (I);
         begin
            if Opt = "--field" then
               Field_Arg := new String'(Value);
            elsif Opt = "--circuit" then
               Circuit_Arg := new String'(Value);
            elsif Opt = "--help" then
               TIO.Put_Line (Usage);
               raise Usage_Error with "";
            else
               raise Usage_Error with "unknown option " & Opt;
            end if;
         end;
      end loop;
      if Field_Arg = null or else Circuit_Arg = null then
         raise Usage_Error with "missing argument";
      end if;
   end Parse_Arguments;

   B      : Byte_Array_Access;
   Agreed : Boolean;
begin
   Parse_Arguments;
   B := Read_File (Circuit_Arg.all);
   if Field_Arg.all = "gf2_128" then
      GF_Bench (B.all, Agreed);
   elsif Field_Arg.all = "p256" then
      P_Bench (B.all, Agreed);
   else
      Free (B);
      raise Usage_Error with "unknown field " & Field_Arg.all;
   end if;
   Free (B);
   if not Agreed then
      CL.Set_Exit_Status (1);
   end if;
exception
   when E : Usage_Error =>
      if Ada.Exceptions.Exception_Message (E) /= "" then
         TIO.Put_Line (TIO.Standard_Error,
                       "first_step_bench: "
                       & Ada.Exceptions.Exception_Message (E));
         TIO.Put_Line (TIO.Standard_Error, Usage);
      end if;
      CL.Set_Exit_Status (2);
   when E : others =>
      TIO.Put_Line (TIO.Standard_Error,
                    "first_step_bench: "
                    & Ada.Exceptions.Exception_Information (E));
      CL.Set_Exit_Status (1);
end First_Step_Bench;
