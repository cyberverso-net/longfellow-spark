--  CHECKER_KAT: the harness of the circuit checker (ADR 0093) on the
--  vectors of gen_checker_vectors.py: small circuits written by hand,
--  their honest certificates, which are accepted, and one hostile
--  certificate for each check of Circuit_Checker.Accepts and each status
--  of the certificate reader, each refused with its status.
--
--  Every certificate goes through Circuit_Check, the checker on two
--  files: the circuit's reader, the certificate's reader, the comparison
--  of the identifiers, the walk. The capacities are reached on small
--  instances of the checker, each with one limit low.
--
--  For every accepted certificate the facts are computed with
--  Layer_Coefficients and Next_Layer, digested as scripts/census.py
--  digests them (Checker_Facts), and compared with census.py's digest in
--  the vector file. Two circuits that differ
--  in one constant are accepted with the same slot counts and have
--  different facts (paragraph D of ADR 0093).
--
--  Test code, outside the proof perimeter: SPARK_Mode is Off. Built with
--  -gnata, so the library's executable contracts run. Reads the vector
--  file given as argument (default: tests/vectors/checker.txt).
--
--  Exit status: success only if at least one case ran and none failed.

pragma SPARK_Mode (Off);

with Ada.Characters.Handling;
with Ada.Command_Line;
with Ada.Containers.Indefinite_Ordered_Maps;
with Ada.Exceptions;
with Ada.Text_IO;
with Interfaces;    use Interfaces;
with Bytes;         use Bytes;
with GF2_128;
with Checker_Facts;
with Kat_Sections;
with Circuit_Status;
with Circuit_Certificates;
with Sumcheck_Algebra_GF2_128;
with Packed_Circuits_GF2_128;
with Circuit_Reader_GF2_128;
with Circuit_Checker;
with Circuit_Checker_GF2_128;
with Circuit_Check;
with Circuit_Check_GF2_128;
with Local_Check_GF2_128;

procedure Checker_KAT is

   package TIO renames Ada.Text_IO;
   package SA renames Sumcheck_Algebra_GF2_128;
   package PC renames Packed_Circuits_GF2_128;
   package CR renames Circuit_Reader_GF2_128;
   package CC renames Circuit_Certificates;
   package CK renames Circuit_Checker_GF2_128;

   use type SA.Element;
   use type Circuit_Status.Status;
   use type CC.Status;

   --  The small instances: one limit each, the others as the registered
   --  instance's.
   package Small_Terms is new Circuit_Checker
     (SA, PC, Max_Form => 3, Max_Terms_Per_Wire => 2, Max_Slots => 128,
      Max_Layer_Slots => 2 ** 22, Max_Vars => 2 ** 22);
   package Small_Slots is new Circuit_Checker
     (SA, PC, Max_Form => 3, Max_Terms_Per_Wire => 128, Max_Slots => 3,
      Max_Layer_Slots => 2 ** 22, Max_Vars => 2 ** 22);
   package Small_Pool is new Circuit_Checker
     (SA, PC, Max_Form => 3, Max_Terms_Per_Wire => 128, Max_Slots => 128,
      Max_Layer_Slots => 5, Max_Vars => 2 ** 22);
   package Small_Vars is new Circuit_Checker
     (SA, PC, Max_Form => 3, Max_Terms_Per_Wire => 128, Max_Slots => 128,
      Max_Layer_Slots => 2 ** 22, Max_Vars => 5);
   package Small_Inputs is new Circuit_Checker
     (SA, PC, Max_Form => 3, Max_Terms_Per_Wire => 128, Max_Slots => 128,
      Max_Layer_Slots => 2 ** 22, Max_Vars => 3);

   package Check_Terms is new Circuit_Check (SA, PC, CR, Small_Terms);
   package Check_Slots is new Circuit_Check (SA, PC, CR, Small_Slots);
   package Check_Pool is new Circuit_Check (SA, PC, CR, Small_Pool);
   package Check_Vars is new Circuit_Check (SA, PC, CR, Small_Vars);
   package Check_Inputs is new Circuit_Check (SA, PC, CR, Small_Inputs);

   Default_Path : constant String := "tests/vectors/checker.txt";

   --  The pool of the registered instance (Max_Layer_Slots).
   Pool_Size : constant := 2 ** 22;

   Passed  : Natural := 0;
   Failed  : Natural := 0;
   Line_No : Natural := 0;

   Parse_Error : exception;

   package Text_Maps is new Ada.Containers.Indefinite_Ordered_Maps
     (Key_Type => String, Element_Type => String);
   Circuits : Text_Maps.Map;   --  name -> the circuit's bytes, in hex
   type Bytes_Ptr is access Byte_Array;
   Honest_Cert : Bytes_Ptr;    --  the certificate of the case "honest"
   Facts    : Text_Maps.Map;   --  name -> census.py's digest, in hex

   function Lower (S : String) return String
     renames Ada.Characters.Handling.To_Lower;

   procedure Check (Ok : Boolean; Msg : String) is
   begin
      if Ok then
         Passed := Passed + 1;
      else
         Failed := Failed + 1;
         TIO.Put_Line ("FAIL line" & Line_No'Image & ": " & Msg);
      end if;
   end Check;

   function Hex_Digit (C : Character) return Unsigned_8 is
   begin
      case C is
         when '0' .. '9' =>
            return Character'Pos (C) - Character'Pos ('0');
         when 'a' .. 'f' =>
            return Character'Pos (C) - Character'Pos ('a') + 10;
         when others =>
            raise Parse_Error with "bad hex digit '" & C & "'";
      end case;
   end Hex_Digit;

   function From_Hex (S : String) return Byte_Array is
      R : Byte_Array (0 .. S'Length / 2 - 1);
   begin
      if S'Length mod 2 /= 0 then
         raise Parse_Error with "odd number of hex digits";
      end if;
      for I in R'Range loop
         R (I) := Shift_Left (Hex_Digit (S (S'First + 2 * I)), 4)
                  or Hex_Digit (S (S'First + 2 * I + 1));
      end loop;
      return R;
   end From_Hex;

   function To_Hex (B : Byte_Array) return String is
      Hex : constant String := "0123456789abcdef";
      R   : String (1 .. 2 * B'Length);
   begin
      for I in 0 .. B'Length - 1 loop
         R (2 * I + 1) := Hex (Integer (Shift_Right (B (B'First + I), 4)) + 1);
         R (2 * I + 2) := Hex (Integer (B (B'First + I) and 15) + 1);
      end loop;
      return R;
   end To_Hex;

   function Elt_Bytes (E : SA.Element) return Byte_Array is
     (GF2_128.To_Bytes (E));

   --  The facts, digested as scripts/census.py digests them.
   package Facts_Of is new Checker_Facts
     (SA, PC, CK, Pool_Size => Pool_Size, To_Bytes => Elt_Bytes);
   function Facts_Digest
     (P : PC.Packed_Circuit; K : CC.Certificate) return Bytes_32
     renames Facts_Of.Facts_Digest;

   -------------------------------------------------------------------
   --  One case
   -------------------------------------------------------------------

   generic
      with package Chk is new Circuit_Check (others => <>);
   procedure Run_Case
     (Name, Instance, Outcome, Status : String;
      Circuit, Cert : Byte_Array;
      Digest_Of : String);

   procedure Run_Case
     (Name, Instance, Outcome, Status : String;
      Circuit, Cert : Byte_Array;
      Digest_Of : String)
   is
      use type Chk.Outcome;
      R : Chk.Result;
   begin
      Chk.Check (Circuit, Cert, R);
      declare
         Got_Outcome : constant String := Lower (R.Outcome'Image);
         Got_Status  : constant String :=
           (case R.Outcome is
              when Chk.Certificate_Refused => Lower (R.Certificate'Image),
              when Chk.Walk_Refused        => Lower (R.Walk'Image),
              when Chk.Circuit_Refused     => Lower (R.Circuit'Image),
              when others                  => "-");
      begin
         Check (Got_Outcome = Outcome and then Got_Status = Status,
                Name & " on " & Instance & ": expected " & Outcome & " "
                & Status & ", got " & Got_Outcome & " " & Got_Status);
      end;
      --  The facts of an accepted certificate, against census.py's.
      if Digest_Of /= "" and then R.Outcome = Chk.Accepted then
         declare
            P   : CR.Packed_Access;
            H   : CR.Header;
            St  : Circuit_Status.Status;
            K   : CC.Cert_Access;
            KSt : CC.Status;
         begin
            CR.Read_Packed (Circuit, False, [others => 0], P, H, St);
            CC.Read (Cert, K, KSt);
            if St /= Circuit_Status.Ok or else KSt /= CC.Ok then
               Check (False, Name & ": the files read again are refused");
            else
               declare
                  D : constant String := To_Hex (Facts_Digest (P.all, K.all));
               begin
                  Check (D = Digest_Of,
                         Name & ": facts " & D & ", census.py " & Digest_Of);
               end;
            end if;
         end;
      end if;
   end Run_Case;

   procedure Run_Registered is new Run_Case (Circuit_Check_GF2_128);
   procedure Run_Terms is new Run_Case (Check_Terms);
   procedure Run_Slots is new Run_Case (Check_Slots);
   procedure Run_Pool is new Run_Case (Check_Pool);
   procedure Run_Vars is new Run_Case (Check_Vars);
   procedure Run_Inputs is new Run_Case (Check_Inputs);

   --  The facts of the accepted circuits, by name, for paragraph D.
   Accepted_Facts : Text_Maps.Map;

   -------------------------------------------------------------------
   --  A certificate built directly, not read
   -------------------------------------------------------------------

   --  The honest certificate of c1, copied into a record with one wire
   --  more after the spans: Spans_Ok refuses the tail, so the walk does
   --  (Cert_Mismatch); the copy without a tail is accepted.
   procedure Check_Built (Circuit, Cert : Byte_Array) is
      use type CK.Status;
      use type CC.Count_Array;
      P   : CR.Packed_Access;
      H   : CR.Header;
      St  : Circuit_Status.Status;
      K   : CC.Cert_Access;
      KSt : CC.Status;
      WSt : CK.Status;
   begin
      CR.Read_Packed (Circuit, False, [others => 0], P, H, St);
      CC.Read (Cert, K, KSt);
      if St /= Circuit_Status.Ok or else KSt /= CC.Ok then
         Check (False, "built: the honest files are refused");
         return;
      end if;
      declare
         Same_Size : constant CC.Certificate := K.all;
         Tail      : CC.Certificate (K.NL, K.NW + 1);
      begin
         CK.Walk (P.all, Same_Size, WSt);
         Check (WSt = CK.Accepted,
                "built: the copy is refused, " & Lower (WSt'Image));
         Tail.Circuit_Id := K.Circuit_Id;
         Tail.Layers := K.Layers;
         Tail.Counts := K.Counts & [1 => 0];
         Check (not CC.Spans_Ok (Tail), "built: Spans_Ok accepts a tail");
         CK.Walk (P.all, Tail, WSt);
         Check (WSt = CK.Cert_Mismatch,
                "built: a tail after the spans, " & Lower (WSt'Image));
      end;
   end Check_Built;

   -------------------------------------------------------------------
   --  Local_Check: the executable check of a product of two forms
   -------------------------------------------------------------------

   procedure Check_Local is
      package LC renames Local_Check_GF2_128;

      function E (V : Unsigned_8) return LC.Element is
         R  : LC.Element;
         Ok : Boolean;
      begin
         GF2_128.From_Bytes ([0 => V, others => 0], R, Ok);
         if not Ok then
            raise Program_Error;
         end if;
         return R;
      end E;

      --  A = 2 w1 + 3 w2, B = 5 w3; A * B = (2 * 5) w1 w3 + (3 * 5) w2 w3.
      A : constant LC.Form_Array :=
        [1 => (W => 1, C => E (2)), 2 => (W => 2, C => E (3)),
         others => (W => 0, C => SA.Zero)];
      B : constant LC.Form_Array :=
        [1 => (W => 3, C => E (5)), others => (W => 0, C => SA.Zero)];
      T : LC.Term_Array :=
        [1 => (H0 => 1, H1 => 3, K => SA."*" (E (2), E (5))),
         2 => (H0 => 3, H1 => 2, K => SA."*" (E (3), E (5))),
         others => (H0 => 0, H1 => 0, K => SA.Zero)];
      M : LC.Pair_Map := [others => [others => 1]];
      None : constant LC.Form_Array := [others => (W => 0, C => SA.Zero)];
   begin
      M (2, 1) := 2;
      Check (LC.Check_Product (T, 2, A, 2, B, 1, M),
             "local check: an honest factorisation refused");
      --  A changed coefficient.
      declare
         T2 : LC.Term_Array := T;
      begin
         T2 (1).K := SA."+" (T2 (1).K, SA.One);
         Check (not LC.Check_Product (T2, 2, A, 2, B, 1, M),
                "local check: a changed coefficient accepted");
      end;
      --  A pair mapped to the term of another monomial.
      declare
         M2 : LC.Pair_Map := M;
      begin
         M2 (1, 1) := 2;
         Check (not LC.Check_Product (T, 2, A, 2, B, 1, M2),
                "local check: a wrong monomial accepted");
      end;
      --  A map entry beyond the terms.
      declare
         M2 : LC.Pair_Map := M;
      begin
         M2 (2, 1) := 3;
         Check (not LC.Check_Product (T, 2, A, 2, B, 1, M2),
                "local check: a map entry beyond NT accepted");
      end;
      --  Empty forms: the product is zero, so no term, or a term whose
      --  constant is zero, passes, and a term with another constant does
      --  not.
      Check (LC.Check_Product (T, 0, None, 0, B, 1, M),
             "local check: an empty form with no term refused");
      T (1).K := SA.Zero;
      Check (LC.Check_Product (T, 1, None, 0, B, 1, M),
             "local check: an empty form with a zero term refused");
      T (1).K := E (7);
      Check (not LC.Check_Product (T, 1, A, 0, B, 1, M),
             "local check: an empty form with a nonzero term accepted");
   end Check_Local;

   procedure Check_Line (Line : String) is
      type Bounds is record
         Lo, Hi : Natural;
      end record;
      Fields : array (1 .. 7) of Bounds;
      Count  : Natural := 0;
      I      : Natural := Line'First;
      J      : Natural;
      function F (X : Positive) return String is
        (Line (Fields (X).Lo .. Fields (X).Hi));
   begin
      if Line'Length = 0 or else Line (Line'First) = '#' then
         return;
      end if;
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
      if Count = 0 then
         return;
      end if;
      if F (1) = "field" then
         if Count /= 2 or else F (2) /= "gf2_128" then
            raise Parse_Error with "only the field gf2_128 is checked";
         end if;
      elsif F (1) = "circuit" and then Count = 3 then
         Circuits.Include (F (2), F (3));
      elsif F (1) = "facts" and then Count = 3 then
         Facts.Include (F (2), F (3));
      elsif F (1) = "cert" and then Count = 7 then
         declare
            Name     : constant String := F (2);
            Circ     : constant String := F (3);
            Instance : constant String := F (4);
            Circuit  : constant Byte_Array := From_Hex (Circuits (Circ));
            Cert     : constant Byte_Array := From_Hex (F (7));
            Digest   : constant String :=
              (if Instance = "gf2_128" and then Facts.Contains (Circ)
               then Facts (Circ) else "");
         begin
            if Name = "honest" then
               Honest_Cert := new Byte_Array'(Cert);
            end if;
            if Instance = "gf2_128" then
               Run_Registered (Name, Instance, F (5), F (6), Circuit, Cert,
                               Digest);
               if F (5) = "accepted" then
                  Accepted_Facts.Include (Circ, Digest);
               end if;
            elsif Instance = "small_terms" then
               Run_Terms (Name, Instance, F (5), F (6), Circuit, Cert, "");
            elsif Instance = "small_slots" then
               Run_Slots (Name, Instance, F (5), F (6), Circuit, Cert, "");
            elsif Instance = "small_pool" then
               Run_Pool (Name, Instance, F (5), F (6), Circuit, Cert, "");
            elsif Instance = "small_vars" then
               Run_Vars (Name, Instance, F (5), F (6), Circuit, Cert, "");
            elsif Instance = "small_inputs" then
               Run_Inputs (Name, Instance, F (5), F (6), Circuit, Cert, "");
            else
               raise Parse_Error with "unknown instance " & Instance;
            end if;
         end;
      else
         raise Parse_Error with "unknown line";
      end if;
   end Check_Line;

   procedure Run_File (Path : String) is
      File : TIO.File_Type;
   begin
      Kat_Sections.Start (Path, Passed, Failed);
      TIO.Open (File, TIO.In_File, Path);
      Line_No := 0;
      while not TIO.End_Of_File (File) loop
         Line_No := Line_No + 1;
         declare
            Line : constant String := TIO.Get_Line (File);
         begin
            Check_Line (Line);
            Kat_Sections.Count (Kat_Sections.Kind_Of (Line), Passed, Failed);
         exception
            when E : Parse_Error =>
               Check (False, "parse error: "
                             & Ada.Exceptions.Exception_Message (E));
         end;
      end loop;
      TIO.Close (File);
   end Run_File;

begin
   if Ada.Command_Line.Argument_Count = 0 then
      Run_File (Default_Path);
   else
      for A in 1 .. Ada.Command_Line.Argument_Count loop
         Run_File (Ada.Command_Line.Argument (A));
      end loop;
   end if;
   --  Paragraph D: the circuit and its copy with one constant changed are
   --  both accepted, and their facts differ.
   Check (Accepted_Facts.Contains ("c1")
          and then Accepted_Facts.Contains ("c1_k")
          and then Accepted_Facts ("c1") /= Accepted_Facts ("c1_k"),
          "paragraph D: c1 and c1_k accepted with different facts");
   Kat_Sections.Count ("paragraph D", Passed, Failed);
   --  A certificate built directly, and the local check, need no file.
   Kat_Sections.Start ("no file", Passed, Failed);
   if Circuits.Contains ("c1") and then Honest_Cert /= null then
      Check_Built (From_Hex (Circuits ("c1")), Honest_Cert.all);
   else
      Check (False, "built: the honest certificate of c1 is not in the file");
   end if;
   Kat_Sections.Count ("built certificate", Passed, Failed);
   Check_Local;
   Kat_Sections.Count ("local check", Passed, Failed);
   Kat_Sections.Print;
   TIO.Put_Line ("checker_kat:" & Passed'Image & " passed," & Failed'Image
                 & " failed");
   Ada.Command_Line.Set_Exit_Status
     (if Failed = 0 and then Passed > 0 then Ada.Command_Line.Success
      else Ada.Command_Line.Failure);
end Checker_KAT;
