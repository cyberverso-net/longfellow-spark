--  INTEROP_KAT: the interop harness of Phase B (ADR 0048, tier 3): the
--  proofs produced by the upstream prover on the upstream circuits,
--  verified end to end by Zk_Verifier on the circuit loaded from its
--  LFC2 file, under the circuit's identifier, the label and the Ligero
--  configuration of the upstream reference test; then the same proof
--  with one byte altered in its root, in its sumcheck part and in its
--  Ligero part, each refused.
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads
--  the vector files given as arguments (default: interop.txt under
--  tests/vectors/). Built in the release project cli/ (assertions off):
--  the verdicts it checks come from the same binary code the project
--  delivers, and the executable contracts of stage 3, which the
--  assertion-enabled build of tests/ runs on the Appendix B.3 circuits,
--  would take the better part of an hour on a circuit of thousands of
--  inputs (ADR 0048). Documentation: docs/guide/06-circuits.md.
--
--  File format: '#' comments and blank lines are skipped; otherwise
--    interop <name> <field> <circuit> <proof> <label> <rate_inv> <nreq>
--            <ncol> <npublic> <public inputs...> <status>
--            <root refusal> <sumcheck refusal> <ligero refusal>
--  with the paths relative to the repository root, the public inputs
--  as big-endian hex integers, the statuses lower-case values of
--  Verifier_Status: the verdict on the proof, then the statuses of the
--  three altered copies, recorded when first observed so that a change
--  of status shows even where the proof is still refused.
--
--  Then the list of Pinned_Circuits (ADR 0074): for each entry, the
--  file has the recorded digest, a full Read recomputes the recorded
--  identifier, Read_Pinned gives the same circuit and header, and
--  Read_Pinned under another identifier refuses the file.
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Calendar;
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
with Pinned_Circuits;
with Sha256;

procedure Interop_KAT is

   package TIO renames Ada.Text_IO;

   Default_File : constant String := "tests/vectors/interop.txt";

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

   function To_Label (S : String) return Byte_Array is
      R : Byte_Array (0 .. S'Length - 1);
   begin
      for I in R'Range loop
         R (I) := Character'Pos (S (S'First + I));
      end loop;
      return R;
   end To_Label;

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

   function Status_Name (St : Verifier_Status.Status) return String is
     (Ada.Characters.Handling.To_Lower (St'Image));

   function Seconds (From : Ada.Calendar.Time) return String is
      use type Ada.Calendar.Time;
      D : constant Duration := Ada.Calendar.Clock - From;
   begin
      return Duration'Image (D) (1 .. 6) & " s";
   end Seconds;

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

   --  One field: load the circuit, verify the proof, then the three
   --  altered copies.
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
      with function To_Element (S : String) return SA.Element;
   procedure Check_Case
     (Name  : String;
      F     : access function (K : Positive) return String;
      Count : Natural);

   procedure Check_Case
     (Name  : String;
      F     : access function (K : Positive) return String;
      Count : Natural)
   is
      use type Circuit_Status.Status;
      use type Verifier_Status.Status;
      Npublic : constant Natural := Natural'Value (F (10));
      Want    : constant String := F (11 + Npublic);
      Cfg     : constant Ligero_Geometry.Config :=
        (Rate_Inv    => Natural'Value (F (7)),
         Num_Queries => Natural'Value (F (8)),
         Encoded_Len => Natural'Value (F (9)));
      Label   : constant Byte_Array := To_Label (F (6));
      Pub     : SA.Element_Array (0 .. Npublic - 1);
      C       : CR.Circuit_Access;
      H       : CR.Header;
      CSt     : Circuit_Status.Status;
      Proof   : Byte_Array_Access;
      VSt     : Verifier_Status.Status;
      T0      : Ada.Calendar.Time;
   begin
      if Count /= 14 + Npublic then
         raise Parse_Error with "interop: field count";
      end if;
      for I in Pub'Range loop
         Pub (I) := To_Element (F (11 + I));
      end loop;
      if not Ligero_Geometry.Valid (Cfg) then
         raise Parse_Error with "interop: configuration not valid";
      end if;
      declare
         Bytes_C : Byte_Array_Access := Read_File (F (4));
      begin
         T0 := Ada.Calendar.Clock;
         CR.Read (Bytes_C.all, C, H, CSt);
         Free (Bytes_C);
      end;
      if CSt /= Circuit_Status.Ok then
         Report_Failure (Name & ": circuit " & CSt'Image);
         return;
      end if;
      TIO.Put_Line ("  " & Name & ": circuit loaded, " & Seconds (T0)
                    & "," & C.NT'Image & " terms");
      Proof := Read_File (F (5));
      T0 := Ada.Calendar.Clock;
      ZK.Verify (Label, H.Id, Cfg, C.all, Pub, Proof.all, VSt);
      TIO.Put_Line ("  " & Name & ": verify " & Status_Name (VSt) & ", "
                    & Seconds (T0));
      if Status_Name (VSt) /= Want then
         Report_Failure (Name & ": got " & Status_Name (VSt)
                         & ", expected " & Want);
      else
         Passed := Passed + 1;
      end if;
      if VSt = Verifier_Status.Ok then
         --  One byte altered in the root, the sumcheck part, the Ligero
         --  part (its last byte, a path digest).
         declare
            Offsets : constant array (1 .. 3) of Natural :=
              [0, 32 + ZK.Sumcheck_Len (ZK.Shape_Of (C.all)) / 2, Proof'Last];
         begin
            for K in Offsets'Range loop
               declare
                  Alt : Byte_Array := Proof.all;
               begin
                  Alt (Offsets (K)) := Alt (Offsets (K)) xor 1;
                  T0 := Ada.Calendar.Clock;
                  ZK.Verify (Label, H.Id, Cfg, C.all, Pub, Alt, VSt);
                  TIO.Put_Line ("  " & Name & ": byte" & Offsets (K)'Image
                                & " altered, " & Status_Name (VSt) & ", "
                                & Seconds (T0));
                  if Status_Name (VSt) /= F (11 + Npublic + K) then
                     Report_Failure (Name & ": altered proof gives "
                                     & Status_Name (VSt) & ", recorded "
                                     & F (11 + Npublic + K));
                  else
                     Passed := Passed + 1;
                  end if;
               end;
            end loop;
         end;
      end if;
      Free (Proof);
      CR.Free (C);
   end Check_Case;

   procedure Check_GF is new Check_Case
     (FS => Field_GF2_128.Sig,
      SA => Sumcheck_Algebra_GF2_128, SE => Sumcheck_Expression_GF2_128,
      SV => Sumcheck_Verifier_GF2_128, ST => Sumcheck_Transcript_GF2_128,
      LP => Ligero_Proof_GF2_128, L => Lagrange_GF2_128,
      LV => Ligero_Verifier_GF2_128, ZK => Zk_Verifier_GF2_128,
      CR => Circuit_Reader_GF2_128, To_Element => GF_To_Element);
   procedure Check_P is new Check_Case
     (FS => Field_P256.Sig,
      SA => Sumcheck_Algebra_P256, SE => Sumcheck_Expression_P256,
      SV => Sumcheck_Verifier_P256, ST => Sumcheck_Transcript_P256,
      LP => Ligero_Proof_P256, L => Lagrange_P256,
      LV => Ligero_Verifier_P256, ZK => Zk_Verifier_P256,
      CR => Circuit_Reader_P256, To_Element => P_To_Element);

   --  One entry of Pinned_Circuits against its file.
   generic
      with package CR is new Circuit_Reader (<>);
   procedure Check_Pin (E : Pinned_Circuits.Entry_Index);

   procedure Check_Pin (E : Pinned_Circuits.Entry_Index) is
      use type Circuit_Status.Status;
      use type CR.Header;
      use type CR.Raw_Circuit;
      Name : constant String := "pin" & E'Image;
      B    : Byte_Array_Access := Read_File (Pinned_Circuits.Path (E));
      Ctx  : Sha256.Context := Sha256.Initial;
      C1, C2 : CR.Circuit_Access;
      H1, H2 : CR.Header;
      S1, S2 : Circuit_Status.Status;
      Other  : Bytes_32 := Pinned_Circuits.Id (E);
   begin
      Sha256.Update (Ctx, B.all);
      if Sha256.Digest (Ctx) /= Pinned_Circuits.File_Digest (E) then
         Report_Failure (Name & ": the file digest differs");
      end if;
      CR.Read (B.all, C1, H1, S1);
      CR.Read_Pinned (B.all, Pinned_Circuits.Id (E), C2, H2, S2);
      if S1 /= Circuit_Status.Ok or else S2 /= Circuit_Status.Ok then
         Report_Failure (Name & ": read " & S1'Image & ", pinned "
                         & S2'Image);
      elsif H1.Id /= Pinned_Circuits.Id (E) then
         Report_Failure (Name & ": the recomputed identifier differs");
      elsif H1 /= H2 or else C1.all /= C2.all then
         Report_Failure (Name & ": Read_Pinned gives another circuit");
      else
         Passed := Passed + 1;
         TIO.Put_Line ("  " & Name & ": " & Pinned_Circuits.Path (E)
                       & "," & C1.NT'Image & " terms, identifier checked");
      end if;
      CR.Free (C1);
      CR.Free (C2);
      Other (0) := Other (0) xor 1;
      CR.Read_Pinned (B.all, Other, C2, H2, S2);
      if S2 /= Circuit_Status.Id_Mismatch then
         Report_Failure (Name & ": another identifier gives " & S2'Image);
         CR.Free (C2);
      else
         Passed := Passed + 1;
      end if;
      Free (B);
   end Check_Pin;

   procedure Check_Pin_GF is new Check_Pin (Circuit_Reader_GF2_128);
   procedure Check_Pin_P is new Check_Pin (Circuit_Reader_P256);

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
      if F (1) /= "interop" then
         raise Parse_Error with "unknown op " & F (1);
      end if;
      if F (3) = "gf2_128" then
         Check_GF (F (2), F'Access, Count);
      elsif F (3) = "p256" then
         Check_P (F (2), F'Access, Count);
      else
         raise Parse_Error with "unknown field " & F (3);
      end if;
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
      TIO.Put_Line ("Interop tests: " & Path);
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
   TIO.Put_Line ("Pinned circuits");
   Line_No := 0;
   for E in Pinned_Circuits.Entry_Index loop
      if Pinned_Circuits.Binary (E) then
         Check_Pin_GF (E);
      else
         Check_Pin_P (E);
      end if;
   end loop;
   TIO.Put_Line ("passed" & Passed'Image & ", failed" & Failed'Image);
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end Interop_KAT;
