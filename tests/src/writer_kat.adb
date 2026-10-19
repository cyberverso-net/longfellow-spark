--  WRITER_KAT: the round-trip harness of the proof writers (Phase C,
--  block 2, ADR 0053): every proof of the repository is read by
--  Zk_Verifier.Read_Proof on its circuit and written back by
--  Proof_Writer; the bytes must be identical. A mismatch is reported at
--  its first offset with the section it falls in.
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads
--  the vector files given as arguments (default: writer.txt under
--  tests/vectors/). Built with -gnata, so the library's executable
--  contracts run.
--
--  File format: '#' comments and blank lines are skipped; otherwise
--    roundtrip <name> <field> <circuit> <proof> <rate_inv> <nreq> <ncol>
--  with <circuit> and <proof> as hex:<bytes> or path:<file relative to
--  the repository root>.
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with Ligero_Geometry;
with Verifier_Status;
with Circuit_Status;
with Field_Signature;
with Field_GF2_128;
with Field_P256;
with Sumcheck_Algebra;
with Sumcheck_Expression;
with Sumcheck_Verifier;
with Sumcheck_Transcript;
with Ligero_Proof;
with Lagrange;
with Ligero_Verifier;
with Zk_Verifier;
with Circuit_Reader;
with Proof_Writer;
with Sumcheck_Algebra_GF2_128;
with Sumcheck_Algebra_P256;
with Sumcheck_Expression_GF2_128;
with Sumcheck_Expression_P256;
with Sumcheck_Verifier_GF2_128;
with Sumcheck_Verifier_P256;
with Sumcheck_Transcript_GF2_128;
with Sumcheck_Transcript_P256;
with Ligero_Proof_GF2_128;
with Ligero_Proof_P256;
with Lagrange_GF2_128;
with Lagrange_P256;
with Ligero_Verifier_GF2_128;
with Ligero_Verifier_P256;
with Zk_Verifier_GF2_128;
with Zk_Verifier_P256;
with Circuit_Reader_GF2_128;
with Circuit_Reader_P256;
with Proof_Writer_GF2_128;
with Proof_Writer_P256;

procedure Writer_KAT is

   package TIO renames Ada.Text_IO;

   Default_File : constant String := "tests/vectors/writer.txt";

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

   --  hex:<bytes> or path:<file>.
   function Load (Spec : String) return Byte_Array_Access is
   begin
      if Spec'Length > 4 and then Spec (Spec'First .. Spec'First + 3) = "hex:"
      then
         return To_Bytes (Spec (Spec'First + 4 .. Spec'Last));
      elsif Spec'Length > 5
        and then Spec (Spec'First .. Spec'First + 4) = "path:"
      then
         return Read_File (Spec (Spec'First + 5 .. Spec'Last));
      else
         raise Parse_Error with "expected hex: or path:, got " & Spec;
      end if;
   end Load;

   Max_Fields : constant := 16;
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

   generic
      with package FS is new Field_Signature (<>);
      with package SA is new Sumcheck_Algebra (F => FS);
      with package SE is new Sumcheck_Expression (SA => SA);
      with package SV is new Sumcheck_Verifier (SA => SA, SE => SE);
      with package ST is new Sumcheck_Transcript
        (SA => SA, SE => SE, SV => SV);
      with package LP is new Ligero_Proof (SA => SA);
      with package L is new Lagrange (F => FS);
      with package LV is new Ligero_Verifier (ST => ST, LP => LP, L => L);
      with package ZK is new Zk_Verifier (LV => LV);
      with package CR is new Circuit_Reader (SA => SA, others => <>);
      with package PW is new Proof_Writer (LV => LV);
   procedure Round_Trip
     (Name : String; Circ, Proof : Byte_Array; Cfg : Ligero_Geometry.Config);

   procedure Round_Trip
     (Name : String; Circ, Proof : Byte_Array; Cfg : Ligero_Geometry.Config)
   is
      use type Circuit_Status.Status;
      use type Verifier_Status.Status;
      C   : CR.Circuit_Access;
      H   : CR.Header;
      CSt : Circuit_Status.Status;
      VSt : Verifier_Status.Status;
   begin
      CR.Read (Circ, C, H, CSt);
      if CSt /= Circuit_Status.Ok then
         Report_Failure (Name & ": circuit " & CSt'Image);
         return;
      end if;
      declare
         G    : constant Ligero_Geometry.Valid_Geometry :=
           ZK.Geometry_Of (Cfg, C.all);
         Root : Bytes_32;
         Sum  : SV.Sumcheck_Proof (Last => SV.Proof_Total (C.all) - 1);
         Lig  : LP.Proof
           (Ldt_Last    => G.Block_Len - 1,
            Linear_Last => G.Dblock_Len - 1,
            Low_Last    => G.Num_Queries - 1,
            High_Last   => G.Dblock_Len - G.Block_Len - 1,
            Nonce_Last  => G.Num_Queries - 1,
            Col_Last    => LP.Opened (G) - 1,
            Path_Last   => 2 * Ligero_Geometry.Num_Leaves (G) - 1);
      begin
         ZK.Read_Proof (Proof, C.all, G, Root, Sum, Lig, VSt);
         if VSt /= Verifier_Status.Ok then
            Report_Failure (Name & ": read " & VSt'Image);
            CR.Free (C);
            return;
         end if;
         declare
            Len : constant Natural :=
              PW.Proof_Len (C.all, G, H.Subfield_Boundary, Lig.Path_Count);
            SL  : constant Natural := 32 + PW.Sumcheck_Len (C.all);
            FL  : constant Natural := SL + LP.Fixed_Len (G);
            Out_B : Byte_Array (0 .. Len - 1);
         begin
            if Len /= Proof'Length then
               Report_Failure (Name & ": written length" & Len'Image
                               & ", file" & Proof'Length'Image);
               CR.Free (C);
               return;
            end if;
            PW.Write_Proof (C.all, G, H.Subfield_Boundary, Root, Sum, Lig,
                            Out_B);
            for I in Out_B'Range loop
               if Out_B (I) /= Proof (I) then
                  Report_Failure
                    (Name & ": byte" & I'Image & " differs ("
                     & (if I < 32 then "root"
                        elsif I < SL then "sumcheck part"
                        elsif I < FL then "polynomials and nonces"
                        else "columns or path") & ")");
                  CR.Free (C);
                  return;
               end if;
            end loop;
            TIO.Put_Line ("  " & Name & ": " & Len'Image & " bytes identical");
            Passed := Passed + 1;
         end;
      end;
      CR.Free (C);
   end Round_Trip;

   procedure Trip_GF is new Round_Trip
     (FS => Field_GF2_128.Sig,
      SA => Sumcheck_Algebra_GF2_128, SE => Sumcheck_Expression_GF2_128,
      SV => Sumcheck_Verifier_GF2_128, ST => Sumcheck_Transcript_GF2_128,
      LP => Ligero_Proof_GF2_128, L => Lagrange_GF2_128,
      LV => Ligero_Verifier_GF2_128, ZK => Zk_Verifier_GF2_128,
      CR => Circuit_Reader_GF2_128, PW => Proof_Writer_GF2_128);
   procedure Trip_P is new Round_Trip
     (FS => Field_P256.Sig,
      SA => Sumcheck_Algebra_P256, SE => Sumcheck_Expression_P256,
      SV => Sumcheck_Verifier_P256, ST => Sumcheck_Transcript_P256,
      LP => Ligero_Proof_P256, L => Lagrange_P256,
      LV => Ligero_Verifier_P256, ZK => Zk_Verifier_P256,
      CR => Circuit_Reader_P256, PW => Proof_Writer_P256);

   procedure Check_Line (Line : String) is
      Fields : Field_Array;
      Count  : Natural;

      function F (K : Positive) return String is
      begin
         if K > Count then
            raise Parse_Error with "missing field" & K'Image;
         end if;
         return Line (Fields (K).Lo .. Fields (K).Hi);
      end F;
   begin
      Split (Line, Fields, Count);
      if Count = 0 then
         return;
      end if;
      if F (1) /= "roundtrip" or else Count /= 8 then
         raise Parse_Error with "expected roundtrip with 7 fields";
      end if;
      declare
         Circ  : Byte_Array_Access := Load (F (4));
         Proof : Byte_Array_Access := Load (F (5));
         Cfg   : constant Ligero_Geometry.Config :=
           (Rate_Inv    => Natural'Value (F (6)),
            Num_Queries => Natural'Value (F (7)),
            Encoded_Len => Natural'Value (F (8)));
      begin
         if not Ligero_Geometry.Valid (Cfg) then
            raise Parse_Error with "configuration not valid";
         end if;
         if F (3) = "gf2_128" then
            Trip_GF (F (2), Circ.all, Proof.all, Cfg);
         elsif F (3) = "p256" then
            Trip_P (F (2), Circ.all, Proof.all, Cfg);
         else
            raise Parse_Error with "unknown field " & F (3);
         end if;
         Free (Circ);
         Free (Proof);
      end;
   exception
      when E : Parse_Error =>
         Report_Failure (Ada.Exceptions.Exception_Message (E));
      when E : others =>
         Report_Failure
           ("exception " & Ada.Exceptions.Exception_Information (E));
   end Check_Line;

   procedure Run_File (Path : String) is
      File : TIO.File_Type;
   begin
      TIO.Put_Line ("Proof_Writer round trips: " & Path);
      TIO.Open (File, TIO.In_File, Path);
      Line_No := 0;
      while not TIO.End_Of_File (File) loop
         declare
            Line : constant String := TIO.Get_Line (File);
         begin
            Line_No := Line_No + 1;
            if Line'Length > 0 and then Line (Line'First) /= '#' then
               Check_Line (Line);
            end if;
         end;
      end loop;
      TIO.Close (File);
   end Run_File;

begin
   if Ada.Command_Line.Argument_Count = 0 then
      Run_File (Default_File);
   else
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         Run_File (Ada.Command_Line.Argument (I));
      end loop;
   end if;
   TIO.Put_Line ("passed" & Passed'Image & ", failed" & Failed'Image);
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end Writer_KAT;
