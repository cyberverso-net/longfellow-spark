--  longfellow_verify: verify a Longfellow ZK proof against a circuit
--  file (Phase B, ADR 0046). Outside the proof perimeter (SPARK_Mode is
--  Off: file input and output); everything it calls is the SPARK
--  library.
--
--    longfellow_verify --field gf2_128|p256 --circuit FILE --proof FILE
--                      --label STRING --rate-inv N --nreq N --ncol N
--                      [--public HEX]...
--
--  Loads the LFC2 circuit (Circuit_Reader), runs Zk_Verifier.Verify on
--  the proof bytes under the circuit's identifier, the label and the
--  Ligero configuration, with the public inputs given as big-endian
--  hex integers (32 digits on GF(2^128), 64 on P-256), and prints the
--  status. Exit status: 0 when the proof is accepted, 1 when it is
--  refused or the circuit is not accepted (the status is printed), 2
--  on a usage or file error. Documentation: docs/guide/06-circuits.md,
--  README "Verifying a proof".

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Characters.Handling;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;
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

procedure Longfellow_Verify is

   package TIO renames Ada.Text_IO;
   package CL renames Ada.Command_Line;

   Usage_Error : exception;

   Usage : constant String :=
     "usage: longfellow_verify --field gf2_128|p256 --circuit FILE"
     & " --proof FILE --label STRING --rate-inv N --nreq N --ncol N"
     & " [--public HEX]...";

   --  The arguments.
   Max_Public : constant := 4096;
   type String_Access is access String;
   Field_Arg, Circuit_Arg, Proof_Arg, Label_Arg : String_Access;
   Rate_Inv, Nreq, Ncol : Natural := 0;
   Public : array (1 .. Max_Public) of String_Access;
   Npublic : Natural := 0;

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
            raise Usage_Error with "bad hex digit '" & C & "'";
      end case;
   end Hex_Digit;

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
         raise Usage_Error with "a GF(2^128) element is 32 hex digits: " & S;
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
         raise Usage_Error with "a P-256 element is 64 hex digits: " & S;
      end if;
      for I in 0 .. 63 loop
         L := P256_Field.Limb_Index (3 - I / 16);
         R (L) := Shift_Left (R (L), 4)
                  or Unsigned_64 (Hex_Digit (S (S'First + I)));
      end loop;
      if not P256_Field.Is_Canonical (R) then
         raise Usage_Error with "value not below p: " & S;
      end if;
      return (Limbs => R);
   end P_To_Element;

   function Lower (S : String) return String
     renames Ada.Characters.Handling.To_Lower;

   --  The verification on one field: 0 accepted, 1 refused.
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
   function Run return CL.Exit_Status;

   function Run return CL.Exit_Status is
      use type Circuit_Status.Status;
      use type Verifier_Status.Status;
      Cfg : constant Ligero_Geometry.Config :=
        (Rate_Inv => Rate_Inv, Num_Queries => Nreq, Encoded_Len => Ncol);
      Pub : SA.Element_Array (0 .. Npublic - 1);
      C   : CR.Circuit_Access;
      H   : CR.Header;
      CSt : Circuit_Status.Status;
      VSt : Verifier_Status.Status;
   begin
      if not Ligero_Geometry.Valid (Cfg) then
         raise Usage_Error with "configuration outside the supported bounds";
      end if;
      for I in Pub'Range loop
         Pub (I) := To_Element (Public (I + 1).all);
      end loop;
      declare
         B : constant Byte_Array_Access := Read_File (Circuit_Arg.all);
      begin
         CR.Read (B.all, C, H, CSt);
      end;
      if CSt /= Circuit_Status.Ok then
         TIO.Put_Line ("circuit " & Lower (CSt'Image));
         return 1;
      end if;
      declare
         P : constant Byte_Array_Access := Read_File (Proof_Arg.all);
      begin
         ZK.Verify (To_Label (Label_Arg.all), H.Id, Cfg, C.all, Pub, P.all,
                    VSt);
      end;
      CR.Free (C);
      TIO.Put_Line (Lower (VSt'Image));
      return (if VSt = Verifier_Status.Ok then 0 else 1);
   end Run;

   function Run_GF is new Run
     (FS => Field_GF2_128.Sig,
      SA => Sumcheck_Algebra_GF2_128, SE => Sumcheck_Expression_GF2_128,
      SV => Sumcheck_Verifier_GF2_128, ST => Sumcheck_Transcript_GF2_128,
      LP => Ligero_Proof_GF2_128, L => Lagrange_GF2_128,
      LV => Ligero_Verifier_GF2_128, ZK => Zk_Verifier_GF2_128,
      CR => Circuit_Reader_GF2_128, To_Element => GF_To_Element);
   function Run_P is new Run
     (FS => Field_P256.Sig,
      SA => Sumcheck_Algebra_P256, SE => Sumcheck_Expression_P256,
      SV => Sumcheck_Verifier_P256, ST => Sumcheck_Transcript_P256,
      LP => Ligero_Proof_P256, L => Lagrange_P256,
      LV => Ligero_Verifier_P256, ZK => Zk_Verifier_P256,
      CR => Circuit_Reader_P256, To_Element => P_To_Element);

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
            elsif Opt = "--proof" then
               Proof_Arg := new String'(Value);
            elsif Opt = "--label" then
               Label_Arg := new String'(Value);
            elsif Opt = "--rate-inv" then
               Rate_Inv := Number;
            elsif Opt = "--nreq" then
               Nreq := Number;
            elsif Opt = "--ncol" then
               Ncol := Number;
            elsif Opt = "--public" then
               if Npublic = Max_Public then
                  raise Usage_Error with "too many public inputs";
               end if;
               Npublic := Npublic + 1;
               Public (Npublic) := new String'(Value);
            elsif Opt = "--help" or else Opt = "-h" then
               TIO.Put_Line (Usage);
               CL.Set_Exit_Status (0);
               raise Usage_Error with "";
            else
               raise Usage_Error with "unknown option " & Opt;
            end if;
         end;
      end loop;
      if Field_Arg = null or else Circuit_Arg = null or else Proof_Arg = null
        or else Label_Arg = null or else Rate_Inv = 0 or else Nreq = 0
        or else Ncol = 0
      then
         raise Usage_Error with "missing argument";
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
                       "longfellow_verify: "
                       & Ada.Exceptions.Exception_Message (E));
         TIO.Put_Line (TIO.Standard_Error, Usage);
         CL.Set_Exit_Status (2);
      end if;
end Longfellow_Verify;
