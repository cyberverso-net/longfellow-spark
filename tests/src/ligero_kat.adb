--  LIGERO_KAT: known-answer test harness for stage 5 (ADR 0040): the
--  Merkle tree (tier 1 from Appendix B.1.1, tier 2 from the generator's
--  independent reference, negative cases), the geometry, the Lagrange
--  code at the queried columns and the Ligero proof reader of Section
--  7.4 on both fields; the verifier on the Appendix B.3 proofs runs in
--  sumcheck_kat, where the constraints of the core are.
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Reads
--  the vector files given as arguments (default: merkle.txt,
--  ligero_geometry.txt, lagrange_gf2_128.txt, lagrange_p256.txt and
--  ligero_proof.txt under tests/vectors/) and checks every case
--  against the library.
--  Built with -gnata, so the library's executable contracts run; a
--  contract violation surfaces here as a failure with the offending
--  line.
--
--  File format: '#' comments and blank lines are skipped; otherwise
--  one case per line, fields separated by blanks, digests as 64 hex
--  digits in memory order, field elements as big-endian hex integers
--  (32 digits for GF(2^128), 64 for P-256), a "field" line naming the
--  field of the element lines that follow:
--    build <n> <n leaves> <root>
--        Merkle.Build of the leaves has this root
--    verify <n> <root> <k> <k indices> <k leaves> <m> <m path> <ok>
--        Merkle.Verify succeeds (ok = 1) or fails (ok = 0)
--    geometry <rate_inv> <nreq> <ncol> <nw> <nq> <valid> [<block>
--        <dblock> <wr> <nwrow> <nqt> <nrow>]
--        Ligero_Geometry.Valid, then Make has these fields
--    table <k> <m> <m columns> <k inv_d> <k*m entries>
--        Lagrange.Build gives these inverses and entries
--    eval <k> <m> <m columns> <k coeffs> <c> <expected>
--        Lagrange.Evaluate at column c of the table
--    read <rate_inv> <nreq> <ncol> <nw> <nq> <status> <bytes>
--        [<n> <n elements> <nreq nonces> <m> <m path digests>]
--        Ligero_Proof.Read gives this status (ok, encoding); when ok
--        it consumes every byte and finds these polynomials and opened
--        columns (in order), nonces and path
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Command_Line;
with Ada.Exceptions;
with Ada.Text_IO;
with Interfaces; use Interfaces;
with Bytes;      use Bytes;
with Merkle;     use Merkle;
with GF2_128;
with P256_Field;
with Ligero_Geometry;
with Lagrange;
with Lagrange_GF2_128;
with Lagrange_P256;
with Verifier_Status;
with Ligero_Proof;
with Ligero_Proof_GF2_128;
with Ligero_Proof_P256;

procedure Ligero_KAT is

   package TIO renames Ada.Text_IO;

   Default_Merkle   : constant String := "tests/vectors/merkle.txt";
   Default_Geometry : constant String := "tests/vectors/ligero_geometry.txt";
   Default_Lag_GF   : constant String := "tests/vectors/lagrange_gf2_128.txt";
   Default_Lag_P    : constant String := "tests/vectors/lagrange_p256.txt";
   Default_Read     : constant String := "tests/vectors/ligero_proof.txt";

   --  The field of the element lines of the current file.
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

   function To_Digest (S : String) return Digest is
      R : Digest;
   begin
      if S'Length /= 64 then
         raise Parse_Error with "expected 64 hex digits, got '" & S & "'";
      end if;
      for I in R'Range loop
         R (I) :=
           Shift_Left (Hex_Digit (S (S'First + 2 * I)), 4)
           or Hex_Digit (S (S'First + 2 * I + 1));
      end loop;
      return R;
   end To_Digest;

   --  GF(2^128): 32 big-endian hex digits; the first 16 form Limbs (1).
   function GF_To_Element (S : String) return GF2_128.Element is
      R : GF2_128.Element := GF2_128.Zero;
      L : GF2_128.Limb_Index;
   begin
      if S'Length /= 32 then
         raise Parse_Error with "expected 32 hex digits, got '" & S & "'";
      end if;
      for I in 0 .. 31 loop
         L := (if I < 16 then 1 else 0);
         R.Limbs (L) :=
           Shift_Left (R.Limbs (L), 4) or Unsigned_64 (Hex_Digit (S (S'First + I)));
      end loop;
      return R;
   end GF_To_Element;

   function GF_Image (E : GF2_128.Element) return String is
      Hex : constant String := "0123456789abcdef";
      S   : String (1 .. 32);
      V   : Unsigned_64;
   begin
      for I in 0 .. 31 loop
         V := E.Limbs ((if I < 16 then 1 else 0));
         S (I + 1) :=
           Hex (Integer (Shift_Right (V, 60 - 4 * (I mod 16)) and 15) + 1);
      end loop;
      return S;
   end GF_Image;

   --  P-256: 64 big-endian hex digits; the first 16 form Limbs (3).
   function P_To_Element (S : String) return P256_Field.Element is
      R : P256_Field.Limb_Array := [others => 0];
      L : P256_Field.Limb_Index;
   begin
      if S'Length /= 64 then
         raise Parse_Error with "expected 64 hex digits, got '" & S & "'";
      end if;
      for I in 0 .. 63 loop
         L := P256_Field.Limb_Index (3 - I / 16);
         R (L) := Shift_Left (R (L), 4) or Unsigned_64 (Hex_Digit (S (S'First + I)));
      end loop;
      if not P256_Field.Is_Canonical (R) then
         raise Parse_Error with "value not below p: " & S;
      end if;
      return (Limbs => R);
   end P_To_Element;

   function P_Image (E : P256_Field.Element) return String is
      Hex : constant String := "0123456789abcdef";
      S   : String (1 .. 64);
      V   : Unsigned_64;
   begin
      for I in 0 .. 63 loop
         V := E.Limbs (P256_Field.Limb_Index (3 - I / 16));
         S (I + 1) :=
           Hex (Integer (Shift_Right (V, 60 - 4 * (I mod 16)) and 15) + 1);
      end loop;
      return S;
   end P_Image;

   function Image (D : Digest) return String is
      Hex : constant String := "0123456789abcdef";
      S   : String (1 .. 64);
   begin
      for I in D'Range loop
         S (2 * I + 1) := Hex (Integer (Shift_Right (D (I), 4)) + 1);
         S (2 * I + 2) := Hex (Integer (D (I) and 15) + 1);
      end loop;
      return S;
   end Image;

   --  Blank-separated fields of a line, as index bounds into it.
   Max_Fields : constant := 4096;
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

   --  The table and eval lines, for one Lagrange instance.
   generic
      with package LG is new Lagrange (<>);
      with function To_Element (S : String) return LG.Element;
      with function Image (E : LG.Element) return String;
      --  Build, or the last table built for the same k and columns: the
      --  lines of one case share a table (with the field contracts
      --  executed, before ADR 0044, a P-256 inverse cost seconds).
      with procedure Build_Cached
        (K : Positive; Cols : LG.Column_Array; T : out LG.Table;
         Inv : out LG.Element_Array; Ok : out Boolean);
   procedure Check_Lagrange_Line (Op : String; Fld : access function (K : Positive) return String; Count : Natural);

   procedure Check_Lagrange_Line (Op : String; Fld : access function (K : Positive) return String; Count : Natural) is
      use type LG.Element;
      K    : constant Positive := Positive'Value (Fld (2));
      M    : constant Positive := Positive'Value (Fld (3));
      Cols : LG.Column_Array (0 .. M - 1);
      T    : LG.Table (0 .. K - 1, 0 .. M - 1);
      Inv  : LG.Element_Array (0 .. K - 1);
      Ok   : Boolean;
      Pos  : Natural := 4;
   begin
      for C in 0 .. M - 1 loop
         Cols (C) := Natural'Value (Fld (Pos + C));
      end loop;
      Pos := Pos + M;
      Build_Cached (K, Cols, T, Inv, Ok);
      if not Ok then
         Report_Failure (Op & ": Build failed (Matrix_Failed)");
         return;
      end if;
      if Op = "table" then
         if Count /= Pos + K + K * M - 1 then
            raise Parse_Error with "table: field count";
         end if;
         for I in 0 .. K - 1 loop
            if Inv (I) /= To_Element (Fld (Pos + I)) then
               Report_Failure
                 ("table k" & K'Image & ": inv_d" & I'Image & " got "
                  & Image (Inv (I)));
               return;
            end if;
         end loop;
         Pos := Pos + K;
         for I in 0 .. K - 1 loop
            for C in 0 .. M - 1 loop
               if T (I, C) /= To_Element (Fld (Pos + I * M + C)) then
                  Report_Failure
                    ("table k" & K'Image & ": entry" & I'Image & C'Image
                     & " got " & Image (T (I, C)));
                  return;
               end if;
            end loop;
         end loop;
         Passed := Passed + 1;
      else
         declare
            Coeffs : LG.Element_Array (0 .. K - 1);
            C      : Natural;
            Want   : LG.Element;
            Got    : LG.Element;
         begin
            if Count /= Pos + K + 1 then
               raise Parse_Error with "eval: field count";
            end if;
            for I in 0 .. K - 1 loop
               Coeffs (I) := To_Element (Fld (Pos + I));
            end loop;
            Pos := Pos + K;
            C    := Natural'Value (Fld (Pos));
            Want := To_Element (Fld (Pos + 1));
            Got  := LG.Evaluate (Coeffs, T, C);
            if Got = Want then
               Passed := Passed + 1;
            else
               Report_Failure
                 ("eval k" & K'Image & " column" & C'Image & " expected "
                  & Image (Want) & " got " & Image (Got));
            end if;
         end;
      end if;
   end Check_Lagrange_Line;

   generic
      with package LG is new Lagrange (<>);
   package Table_Cache is
      procedure Build_Cached
        (K : Positive; Cols : LG.Column_Array; T : out LG.Table;
         Inv : out LG.Element_Array; Ok : out Boolean);
   end Table_Cache;

   package body Table_Cache is
      type Entry_Type (Last_K, Last_M : Natural) is record
         Cols : LG.Column_Array (0 .. Last_M);
         T    : LG.Table (0 .. Last_K, 0 .. Last_M);
         Inv  : LG.Element_Array (0 .. Last_K);
      end record;
      type Entry_Access is access Entry_Type;
      Last : Entry_Access := null;

      procedure Build_Cached
        (K : Positive; Cols : LG.Column_Array; T : out LG.Table;
         Inv : out LG.Element_Array; Ok : out Boolean)
      is
         use type LG.Column_Array;
      begin
         if Last /= null and then Last.Last_K = K - 1
           and then Last.Cols = Cols
         then
            T   := Last.T;
            Inv := Last.Inv;
            Ok  := True;
            return;
         end if;
         LG.Build (K, Cols, T, Inv, Ok);
         if Ok then
            Last := new Entry_Type'(Last_K => K - 1, Last_M => Cols'Last,
                                    Cols => Cols, T => T, Inv => Inv);
         end if;
      end Build_Cached;
   end Table_Cache;

   package GF_Cache is new Table_Cache (Lagrange_GF2_128);
   package P_Cache is new Table_Cache (Lagrange_P256);

   procedure Check_GF is new Check_Lagrange_Line
     (Lagrange_GF2_128, GF_To_Element, GF_Image, GF_Cache.Build_Cached);
   procedure Check_P is new Check_Lagrange_Line
     (Lagrange_P256, P_To_Element, P_Image, P_Cache.Build_Cached);

   --  The read lines, for one proof instance.
   generic
      with package LPK is new Ligero_Proof (<>);
      with function To_Element (S : String) return LPK.Element;
      with function Image (E : LPK.Element) return String;
   procedure Check_Read_Line
     (Fld : access function (K : Positive) return String; Count : Natural);

   procedure Check_Read_Line
     (Fld : access function (K : Positive) return String; Count : Natural)
   is
      use Ligero_Geometry;
      use Verifier_Status;
      use type LPK.Element;
      Cfg : constant Config :=
        (Rate_Inv    => Natural'Value (Fld (2)),
         Num_Queries => Natural'Value (Fld (3)),
         Encoded_Len => Natural'Value (Fld (4)));
      NW      : constant Natural := Natural'Value (Fld (5));
      NQ      : constant Natural := Natural'Value (Fld (6));
      Want_Ok : constant Boolean := Fld (7) = "ok";
      Hex     : constant String  := Fld (8);
      B       : Byte_Array (0 .. Hex'Length / 2 - 1);
   begin
      if Fld (7) /= "ok" and then Fld (7) /= "encoding" then
         raise Parse_Error with "read: status must be ok or encoding";
      end if;
      if not Valid (Cfg) then
         raise Parse_Error with "read: the configuration is not valid";
      end if;
      for I in B'Range loop
         B (I) := Shift_Left (Hex_Digit (Hex (Hex'First + 2 * I)), 4)
                  or Hex_Digit (Hex (Hex'First + 2 * I + 1));
      end loop;
      declare
         G    : constant Valid_Geometry := Make (Cfg, NW, NQ);
         P    : LPK.Proof
           (Ldt_Last    => G.Block_Len - 1,
            Linear_Last => G.Dblock_Len - 1,
            Low_Last    => G.Num_Queries - 1,
            High_Last   => G.Dblock_Len - G.Block_Len - 1,
            Nonce_Last  => G.Num_Queries - 1,
            Col_Last    => LPK.Opened (G) - 1,
            Path_Last   => 2 * Num_Leaves (G) - 1);
         Next : Natural;
         St   : Status;
         Pos  : Natural := 9;
         N    : Natural;
         M    : Natural;

         function Elt (K : Natural) return LPK.Element is
           (To_Element (Fld (Pos + K)));

         procedure Compare (What : String; Es : LPK.SA.Element_Array) is
         begin
            for I in Es'Range loop
               if Es (I) /= Elt (I - Es'First) then
                  raise Parse_Error
                    with "read: " & What & " differs at" & I'Image & ": got "
                         & Image (Es (I));
               end if;
            end loop;
            Pos := Pos + Es'Length;
         end Compare;
      begin
         LPK.Read (B, 0, G, P, Next, St);
         if not Want_Ok then
            if St = Proof_Encoding then
               Passed := Passed + 1;
            else
               Report_Failure ("read: expected Proof_Encoding, got "
                               & St'Image);
            end if;
            return;
         end if;
         if St /= Ok then
            Report_Failure ("read: expected Ok, got " & St'Image);
            return;
         end if;
         if Next /= B'Length then
            Report_Failure ("read: consumed" & Next'Image & " of"
                            & B'Length'Image & " bytes");
            return;
         end if;
         N := Natural'Value (Fld (Pos));
         Pos := Pos + 1;
         if N /= LPK.Opened (G) + 2 * G.Dblock_Len + G.Num_Queries then
            raise Parse_Error with "read: element count";
         end if;
         Compare ("ldt_poly", P.Ldt_Poly);
         Compare ("linear_poly", P.Linear_Poly);
         Compare ("quad_poly_low", P.Quad_Low);
         Compare ("quad_poly_high", P.Quad_High);
         Compare ("queried_columns", P.Columns);
         N := Natural'Value (Fld (Pos));
         Pos := Pos + 1;
         if N /= G.Num_Queries then
            raise Parse_Error with "read: nonce count";
         end if;
         for K in P.Nonces'Range loop
            if P.Nonces (K) /= To_Digest (Fld (Pos + K)) then
               raise Parse_Error with "read: nonce" & K'Image & " differs";
            end if;
         end loop;
         Pos := Pos + N;
         M := Natural'Value (Fld (Pos));
         Pos := Pos + 1;
         if P.Path_Count /= M then
            Report_Failure ("read: path count" & P.Path_Count'Image
                            & ", expected" & M'Image);
            return;
         end if;
         for K in 0 .. M - 1 loop
            if P.Path (K) /= To_Digest (Fld (Pos + K)) then
               raise Parse_Error with "read: path digest" & K'Image
                                      & " differs";
            end if;
         end loop;
         Pos := Pos + M;
         if Count /= Pos - 1 then
            raise Parse_Error with "read: field count";
         end if;
         Passed := Passed + 1;
      end;
   end Check_Read_Line;

   procedure Read_GF is new Check_Read_Line
     (Ligero_Proof_GF2_128, GF_To_Element, GF_Image);
   procedure Read_P is new Check_Read_Line
     (Ligero_Proof_P256, P_To_Element, P_Image);

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

      function Nat (K : Positive) return Natural is
      begin
         return Natural'Value (F (K));
      end Nat;
   begin
      Split (Line, Fields, Count);
      if Count = 0 then
         return;
      end if;
      declare
         Op : constant String := F (1);
      begin
         if Op = "build" then
            declare
               N      : constant Natural := Nat (2);
               Leaves : Digest_Array (0 .. N - 1);
               Heap   : Digest_Array (0 .. 2 * N - 1);
               Want   : Digest;
            begin
               if N = 0 or else Count /= N + 3 then
                  raise Parse_Error with "build expects n, n leaves, root";
               end if;
               for I in 0 .. N - 1 loop
                  Leaves (I) := To_Digest (F (3 + I));
               end loop;
               Want := To_Digest (F (N + 3));
               Build (Leaves, Heap);
               if Heap (1) = Want then
                  Passed := Passed + 1;
               else
                  Report_Failure
                    ("build" & N'Image & " expected root " & Image (Want)
                     & " got " & Image (Heap (1)));
               end if;
            end;
         elsif Op = "verify" then
            declare
               N    : constant Natural := Nat (2);
               Root : constant Digest  := To_Digest (F (3));
               K    : constant Natural := Nat (4);
               Idx  : Index_Array (0 .. K - 1);
               Lvs  : Digest_Array (0 .. K - 1);
               M    : Natural;
               Pos  : Natural := 5;
               Ok   : Boolean;
               Want : Boolean;
            begin
               for I in 0 .. K - 1 loop
                  Idx (I) := Nat (Pos + I);
               end loop;
               Pos := Pos + K;
               for I in 0 .. K - 1 loop
                  Lvs (I) := To_Digest (F (Pos + I));
               end loop;
               Pos := Pos + K;
               M := Nat (Pos);
               Pos := Pos + 1;
               declare
                  Path : Digest_Array (0 .. M - 1);
               begin
                  for I in 0 .. M - 1 loop
                     Path (I) := To_Digest (F (Pos + I));
                  end loop;
                  Pos := Pos + M;
                  if Count /= Pos then
                     raise Parse_Error with "verify: field count";
                  end if;
                  Want := Nat (Pos) = 1;
                  Verify (N, Root, Idx, Lvs, Path, Ok);
                  if Ok = Want then
                     Passed := Passed + 1;
                  else
                     Report_Failure
                       ("verify" & N'Image & " k" & K'Image & " expected "
                        & Want'Image & " got " & Ok'Image);
                  end if;
               end;
            end;
         elsif Op = "field" then
            if F (2) = "gf2_128" then
               Current_Field := GF;
            elsif F (2) = "p256" then
               Current_Field := P;
            else
               raise Parse_Error with "unknown field " & F (2);
            end if;
         elsif Op = "geometry" then
            declare
               use Ligero_Geometry;
               C     : constant Config :=
                 (Rate_Inv => Nat (2), Num_Queries => Nat (3),
                  Encoded_Len => Nat (4));
               NW    : constant Natural := Nat (5);
               NQ    : constant Natural := Nat (6);
               Valid_Want : constant Boolean := Nat (7) = 1;
            begin
               if Valid (C) /= Valid_Want then
                  Report_Failure ("geometry: Valid got " & Valid (C)'Image);
               elsif not Valid_Want then
                  Passed := Passed + 1;
               else
                  declare
                     G : constant Valid_Geometry := Make (C, NW, NQ);
                  begin
                     if Count /= 13 then
                        raise Parse_Error with "geometry: field count";
                     end if;
                     if G.Block_Len = Nat (8) and then G.Dblock_Len = Nat (9)
                       and then G.Witnesses_Per_Row = Nat (10)
                       and then G.Num_Witness_Rows = Nat (11)
                       and then G.Num_Quad_Rows = Nat (12)
                       and then G.Total_Rows = Nat (13)
                     then
                        Passed := Passed + 1;
                     else
                        Report_Failure
                          ("geometry: got block" & G.Block_Len'Image
                           & " dblock" & G.Dblock_Len'Image & " wr"
                           & G.Witnesses_Per_Row'Image & " nwrow"
                           & G.Num_Witness_Rows'Image & " nqt"
                           & G.Num_Quad_Rows'Image & " nrow"
                           & G.Total_Rows'Image);
                     end if;
                  end;
               end if;
            end;
         elsif Op = "table" or else Op = "eval" then
            case Current_Field is
               when GF   => Check_GF (Op, F'Access, Count);
               when P    => Check_P (Op, F'Access, Count);
               when None => raise Parse_Error with "no field line";
            end case;
         elsif Op = "read" then
            case Current_Field is
               when GF   => Read_GF (F'Access, Count);
               when P    => Read_P (F'Access, Count);
               when None => raise Parse_Error with "no field line";
            end case;
         else
            raise Parse_Error with "unknown operation '" & Op & "'";
         end if;
      end;
   exception
      when E : others =>
         --  Parse errors and contract violations (assertion failures
         --  raised inside the library) both count as failures.
         Report_Failure
           (Ada.Exceptions.Exception_Name (E) & ": "
            & Ada.Exceptions.Exception_Message (E));
   end Check_Case;

   procedure Run_File (Path : String) is
      File : TIO.File_Type;
   begin
      TIO.Put_Line ("Ligero known-answer tests: " & Path);
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
      Run_File (Default_Merkle);
      Run_File (Default_Geometry);
      Run_File (Default_Lag_GF);
      Run_File (Default_Lag_P);
      Run_File (Default_Read);
   else
      for I in 1 .. Ada.Command_Line.Argument_Count loop
         Run_File (Ada.Command_Line.Argument (I));
      end loop;
   end if;

   TIO.Put_Line
     ("passed" & Passed'Image & ", failed" & Failed'Image);
   if Failed > 0 or else Passed = 0 then
      Ada.Command_Line.Set_Exit_Status (Ada.Command_Line.Failure);
   end if;
end Ligero_KAT;
