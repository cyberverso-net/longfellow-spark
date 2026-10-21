pragma SPARK_Mode (Off);

with Bytes;
with Interfaces; use Interfaces;
with Ada.Directories;
with Ada.Exceptions;
with Ada.Text_IO;
with Transcript;
with Ligero_Geometry;
with Verifier_Status;

package body Sumcheck_KAT_Generic is

   package TIO renames Ada.Text_IO;
   use SA;
   use type SA.Element;
   use type SV.Lqc_Triple;
   use type Bytes.Byte_Array;

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

   --  Tier 3 state.
   Max_Elems : constant := 8192;
   type Elem_Buf is array (0 .. Max_Elems - 1) of Element;
   type Nat_Buf is array (0 .. Max_Elems - 1) of Natural;
   Tier3        : Boolean;
   Pub_Buf      : Wire_Buf;
   Have_Public  : Boolean;
   Pad_Base_Val : Natural;
   Have_Pad     : Boolean;
   G_Buf        : Elem_Buf;
   Have_G       : Boolean;
   Chal_Buf     : Elem_Buf;      --  layer challenges, flat, in layer order
   Chal_Count   : Natural;
   Chal_Layers  : Natural;       --  layers whose challenges were read
   Proof_Buf    : Elem_Buf;
   Proof_Count  : Natural;
   Proof_Layers : Natural;
   Alpha_In     : Element;
   Have_Alpha   : Boolean;
   --  The zk_proof lines of the circuit (stage 4), kept until the
   --  recording of the same circuit ends.
   Max_Zk_Bytes   : constant := 65536;
   Zk_Name        : String (1 .. 64);
   Zk_Name_Len    : Natural := 0;
   Zk_Label       : Bytes.Byte_Array (0 .. 255);
   Zk_Label_Len   : Natural := 0;
   Zk_Root        : Bytes.Bytes_32;
   Zk_Id          : Bytes.Bytes_32;
   Zk_Sumcheck    : Bytes.Byte_Array (0 .. Max_Zk_Bytes - 1);
   Zk_Sumcheck_Len : Natural := 0;
   Have_Zk        : Boolean := False;
   Have_Zk_Sumcheck : Boolean := False;
   --  Stage 5: the Ligero part and the configuration (zk_ligero), the
   --  nonces of B.3.1 (zk_nonce).
   Zk_Ligero      : Bytes.Byte_Array (0 .. Max_Zk_Bytes - 1);
   Zk_Ligero_Len  : Natural := 0;
   Zk_Rate, Zk_Nreq, Zk_Ncol : Natural := 0;
   Have_Zk_Ligero : Boolean := False;
   Max_Nonces     : constant := 256;
   Zk_Nonces      : array (0 .. Max_Nonces - 1) of Bytes.Bytes_32;
   Zk_Nonce_Given : array (0 .. Max_Nonces - 1) of Boolean :=
     [others => False];
   --  DEFAULT_STATEMENT_HASH of zk/common.rs: 0xdeadbeef then zeros.
   Default_Statement_Hash : constant Bytes.Bytes_32 :=
     [16#de#, 16#ad#, 16#be#, 16#ef#, others => 0];
   --  Expected constraints: entries (constraint, variable, coefficient).
   Exp_Cons     : Nat_Buf;
   Exp_Var      : Nat_Buf;
   Exp_Coeff    : Elem_Buf;
   Exp_Terms    : Natural;
   Exp_B        : Elem_Buf;
   Exp_B_Given  : array (0 .. Max_Layers) of Boolean;
   Exp_B_Count  : Natural;
   Exp_Lqc      : array (0 .. Max_Layers - 1) of SV.Lqc_Triple;
   Exp_Lqc_Given : array (0 .. Max_Layers - 1) of Boolean;

   --  Hex bytes in memory order into Dest (0 .. Len - 1).
   procedure Hex_Into
     (S : String; Dest : out Bytes.Byte_Array; Len : out Natural)
   is
      function Digit (C : Character) return Unsigned_8 is
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
      end Digit;
   begin
      if S'Length mod 2 /= 0 then
         raise Parse_Error with "odd number of hex digits";
      end if;
      Len := S'Length / 2;
      if Len > Dest'Length then
         raise Parse_Error with "hex string too long";
      end if;
      Dest := [others => 0];
      for I in 0 .. Len - 1 loop
         Dest (Dest'First + I) :=
           Shift_Left (Digit (S (S'First + 2 * I)), 4)
           or Digit (S (S'First + 2 * I + 1));
      end loop;
   end Hex_Into;

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
            --  Phase D, M1: the bound quad by the bindeq tables agrees
            --  with the bound quad term by term, on every layer, under
            --  challenges that depend on the layer (ADR 0057's rule: the
            --  fast form is tested against the reference form).
            for J in 0 .. C.Last_Layer loop
               declare
                  Size : constant Natural := Seg_Size (C, J);
                  Logv : Natural := 0;
                  G0, G1, H0, H1 : Element_Array (0 .. Max_Logw - 1);
                  V : Element := P2;
                  Slow, Fast : Element;
               begin
                  while 2 ** Logv < Size loop
                     Logv := Logv + 1;
                  end loop;
                  for K in 0 .. Max_Logw - 1 loop
                     V := V * P2 + One;
                     G0 (K) := V;
                     G1 (K) := V * V;
                     H0 (K) := V + P2;
                     H1 (K) := V * P2;
                  end loop;
                  Slow := Eval_Bound_Quad
                    (Layer_Terms (C, J), Logv, G0, G1, H0, H1,
                     C.Layers (J).Logw, G0 (J), H1 (J));
                  Eval_Bound_Quad_T
                    (Layer_Terms (C, J), Logv, G0, G1, H0, H1,
                     C.Layers (J).Logw, G0 (J), H1 (J), Fast);
                  Check (Fast = Slow, "circuit " & Name & ": layer" & J'Image
                         & ", the bound quad by tables differs");
               end;
            end loop;
         end;
      end;
   end Finish_Circuit;

   --  Builds the circuit, runs the core with the recorded challenges and
   --  compares the emitted constraints with the recorded ones.
   --  Stage 4: the reader, the replay and the core on the replayed
   --  record, against the recording (ADR 0032).
   --  Stage 5 (ADR 0040): the Ligero part of the proof read (Section
   --  7.4), its nonces against B.3.1, then the Ligero verifier on the
   --  constraints of the core, in the transcript state the replay left.
   --  With a tier 3 recording of the upstream Ligero verifier
   --  (tests/vectors/upstream/ligero_<field>_<circuit>.txt) the steps
   --  run one by one and every intermediate value is compared; without
   --  it, Verify runs composed and must accept.
   procedure Check_Ligero
     (Name : String;
      C    : Circuit;
      A    : SV.Ligero_Terms;
      B    : Element_Array;
      Lqc  : SV.Lqc_Array)
   is
      use Ligero_Geometry;
      use Verifier_Status;
      Rec_Path : constant String :=
        "tests/vectors/upstream/ligero_" & Field_Name & "_" & Name & ".txt";
      NW  : Natural := C.Ninput - C.Npublic;
      Cfg : Ligero_Geometry.Config;
   begin
      if not Have_Zk_Ligero then
         Report_Failure ("tier 3 " & Name & ": no zk_ligero line");
         return;
      end if;
      for J in 0 .. C.Last_Layer loop
         NW := NW + 4 * C.Layers (J).Logw + 3;
      end loop;
      Cfg := (Rate_Inv => Zk_Rate, Num_Queries => Zk_Nreq,
              Encoded_Len => Zk_Ncol);
      if not Valid (Cfg) then
         Report_Failure ("tier 3 " & Name & ": configuration not valid");
         return;
      end if;
      declare
         G    : constant Valid_Geometry := Make (Cfg, NW, Lqc'Length);
         P    : LP.Proof
           (Ldt_Last    => G.Block_Len - 1,
            Linear_Last => G.Dblock_Len - 1,
            Low_Last    => G.Num_Queries - 1,
            High_Last   => G.Dblock_Len - G.Block_Len - 1,
            Nonce_Last  => G.Num_Queries - 1,
            Col_Last    => LP.Opened (G) - 1,
            Path_Last   => 2 * Num_Leaves (G) - 1);
         Next : Natural;
         St   : Verifier_Status.Status;
      begin
         LP.Read (Zk_Ligero (0 .. Zk_Ligero_Len - 1), 0, G, P, Next, St);
         if St /= Ok then
            Report_Failure ("tier 3 " & Name & ": Ligero reader status "
                            & St'Image);
            return;
         end if;
         Check (Next = Zk_Ligero_Len,
                "tier 3 " & Name & ": Ligero part consumed" & Next'Image
                & " of" & Zk_Ligero_Len'Image & " bytes");
         --  Tier 1: the nonces of Appendix B.3.1.
         for K in P.Nonces'Range loop
            if K < Max_Nonces and then Zk_Nonce_Given (K) then
               Check (P.Nonces (K) = Zk_Nonces (K),
                      "tier 3 " & Name & ": nonce" & K'Image
                      & " differs from B.3.1");
            end if;
         end loop;
         if not Ada.Directories.Exists (Rec_Path) then
            LV.Verify (Cfg, NW, B, Zk_Root, P, A, Default_Statement_Hash,
                       Lqc, St);
            Check (St = Ok, "tier 3 " & Name & ": Ligero verdict "
                   & St'Image);
            return;
         end if;
         --  The recording: one line per item, in the verifier's order.
         declare
            R_Uldt, R_Alphal, R_Alphaq, R_Uquad : Elem_Buf;
            N_Uldt, N_Alphal, N_Alphaq, N_Uquad : Natural := 0;
            R_Idx    : Nat_Buf;
            N_Idx    : Natural := 0;
            R_Ldt, R_Dot, R_Quad : Elem_Buf;   --  nreq yc then nreq yp
            N_Ldt, N_Dot, N_Quad : Natural := 0;
            R_Want, R_Proof : Element;
            Have_Sum : Boolean := False;
            Verdict  : Boolean := False;
            Ended    : Boolean := False;
            File     : TIO.File_Type;

            procedure Fill
              (Buf : in out Elem_Buf; N : in out Natural; S : String;
               From : Positive; Count : Natural)
            is
               Fields : Field_Array;
               Cnt    : Natural;
            begin
               Split (S, Fields, Cnt);
               if Cnt < From + Count - 1 then
                  raise Parse_Error with "recording line too short";
               end if;
               for I in 0 .. Count - 1 loop
                  Buf (N + I) :=
                    To_Element (S (Fields (From + I).Lo
                                   .. Fields (From + I).Hi));
               end loop;
               N := N + Count;
            end Fill;

            procedure Compare
              (What : String; Got : Element_Array; Buf : Elem_Buf;
               Off : Natural)
            is
               Same : Boolean := True;
            begin
               for I in Got'Range loop
                  if Got (I) /= Buf (Off + I - Got'First) then
                     Same := False;
                     TIO.Put_Line ("  " & What & I'Image & ": got "
                                   & Image (Got (I)) & " recorded "
                                   & Image (Buf (Off + I - Got'First)));
                  end if;
               end loop;
               Check (Same, "tier 3 " & Name & ": " & What);
            end Compare;
         begin
            TIO.Open (File, TIO.In_File, Rec_Path);
            while not TIO.End_Of_File (File) loop
               declare
                  S      : constant String := TIO.Get_Line (File);
                  Fields : Field_Array;
                  Cnt    : Natural;
               begin
                  if S'Length > 0 and then S (S'First) /= '#' then
                     Split (S, Fields, Cnt);
                     declare
                        Op : constant String :=
                          S (Fields (1).Lo .. Fields (1).Hi);
                     begin
                        if Op = "field" then
                           if S (Fields (2).Lo .. Fields (2).Hi)
                             /= Field_Name
                           then
                              raise Parse_Error with "recording field";
                           end if;
                        elsif Op = "ligero" then
                           if Cnt /= 5
                             or else S (Fields (2).Lo .. Fields (2).Hi) /= Name
                             or else Nat (S (Fields (3).Lo .. Fields (3).Hi))
                                     /= Zk_Rate
                             or else Nat (S (Fields (4).Lo .. Fields (4).Hi))
                                     /= Zk_Nreq
                             or else Nat (S (Fields (5).Lo .. Fields (5).Hi))
                                     /= Zk_Ncol
                           then
                              raise Parse_Error
                                with "recording: ligero line differs";
                           end if;
                        elsif Op = "geometry" then
                           Check
                             (Cnt = 9
                              and then Nat (S (Fields (2).Lo .. Fields (2).Hi))
                                       = G.Block_Len
                              and then Nat (S (Fields (3).Lo .. Fields (3).Hi))
                                       = G.Dblock_Len
                              and then Nat (S (Fields (4).Lo .. Fields (4).Hi))
                                       = G.Witnesses_Per_Row
                              and then Nat (S (Fields (5).Lo .. Fields (5).Hi))
                                       = NW
                              and then Nat (S (Fields (6).Lo .. Fields (6).Hi))
                                       = Lqc'Length
                              and then Nat (S (Fields (7).Lo .. Fields (7).Hi))
                                       = G.Num_Witness_Rows
                              and then Nat (S (Fields (8).Lo .. Fields (8).Hi))
                                       = G.Num_Quad_Rows
                              and then Nat (S (Fields (9).Lo .. Fields (9).Hi))
                                       = G.Total_Rows,
                              "tier 3 " & Name & ": recorded geometry");
                        elsif Op = "u_ldt" then
                           Fill (R_Uldt, N_Uldt, S, 2, Cnt - 1);
                        elsif Op = "alphal" then
                           Fill (R_Alphal, N_Alphal, S, 2, Cnt - 1);
                        elsif Op = "alphaq" then
                           if Cnt /= 5
                             or else Nat (S (Fields (2).Lo .. Fields (2).Hi))
                                     /= N_Alphaq / 3
                           then
                              raise Parse_Error with "recording: alphaq";
                           end if;
                           Fill (R_Alphaq, N_Alphaq, S, 3, 3);
                        elsif Op = "u_quad" then
                           Fill (R_Uquad, N_Uquad, S, 2, Cnt - 1);
                        elsif Op = "idx" then
                           for I in 2 .. Cnt loop
                              R_Idx (N_Idx) :=
                                Nat (S (Fields (I).Lo .. Fields (I).Hi));
                              N_Idx := N_Idx + 1;
                           end loop;
                        elsif Op = "ldt" then
                           Fill (R_Ldt, N_Ldt, S, 2, Cnt - 1);
                        elsif Op = "dot" then
                           Fill (R_Dot, N_Dot, S, 2, Cnt - 1);
                        elsif Op = "dot_sum" then
                           R_Want  := To_Element
                             (S (Fields (2).Lo .. Fields (2).Hi));
                           R_Proof := To_Element
                             (S (Fields (3).Lo .. Fields (3).Hi));
                           Have_Sum := True;
                        elsif Op = "quad" then
                           Fill (R_Quad, N_Quad, S, 2, Cnt - 1);
                        elsif Op = "verdict" then
                           Verdict := S (Fields (2).Lo .. Fields (2).Hi) = "ok";
                        elsif Op = "end" then
                           Ended := True;
                        else
                           raise Parse_Error
                             with "recording: unknown line " & Op;
                        end if;
                     end;
                  end if;
               end;
            end loop;
            TIO.Close (File);
            if not Ended or else not Have_Sum or else not Verdict
              or else N_Uldt /= Num_Wq_Rows (G) or else N_Alphal /= B'Length
              or else N_Alphaq /= 3 * Lqc'Length
              or else N_Uquad /= G.Num_Quad_Rows
              or else N_Idx /= G.Num_Queries
              or else N_Ldt /= 2 * G.Num_Queries
              or else N_Dot /= 2 * G.Num_Queries
              or else N_Quad /= 2 * G.Num_Queries
            then
               raise Parse_Error with "recording " & Rec_Path & " incomplete";
            end if;
            --  The steps of LigeroVerifier::verify, each compared.
            Transcript.Write_Bytes (Default_Statement_Hash);
            declare
               NQ   : constant Natural := G.Num_Queries;
               Ch   : LV.Challenges
                 (Ldt_Last    => Num_Wq_Rows (G) - 1,
                  Alphal_Last => B'Length - 1,
                  Alphaq_Last => 3 * Lqc'Length - 1,
                  Quad_Last   => G.Num_Quad_Rows - 1);
               Idx  : LV.Column_Indices (0 .. NQ - 1);
               Good : Boolean;
               Same : Boolean;
            begin
               LV.Draw_Challenges (G, B'Length, Lqc'Length, Ch);
               Compare ("u_ldt", Ch.U_Ldt, R_Uldt, 0);
               Compare ("alphal", Ch.Alphal, R_Alphal, 0);
               Compare ("alphaq", Ch.Alphaq, R_Alphaq, 0);
               Compare ("u_quad", Ch.U_Quad, R_Uquad, 0);
               LV.Absorb_Polynomials (G, P);
               LV.Choose_Columns (G, Idx);
               Same := True;
               for K in Idx'Range loop
                  if Idx (K) /= R_Idx (K) then
                     Same := False;
                     TIO.Put_Line ("  idx" & K'Image & ": got" & Idx (K)'Image
                                   & " recorded" & R_Idx (K)'Image);
                  end if;
               end loop;
               Check (Same, "tier 3 " & Name & ": idx");
               Check (not Transcript.Is_Exhausted,
                      "tier 3 " & Name & ": generator exhausted");
               LV.Verify_Merkle (G, Zk_Root, P, Idx, Good);
               Check (Good, "tier 3 " & Name & ": verify_merkle");
               declare
                  T_Block  : L.Table (0 .. G.Block_Len - 1, 0 .. NQ - 1);
                  T_Dblock : L.Table (0 .. G.Dblock_Len - 1, 0 .. NQ - 1);
                  Yc, Yp   : Element_Array (0 .. NQ - 1);
                  A_Full   : Element_Array (0 .. LV.Vector_Len (G) - 1);
                  Want, Pd : Element;
                  St_Dot   : Verifier_Status.Status;
               begin
                  LV.Build_Tables (G, Idx, T_Block, T_Dblock, Good);
                  Check (Good, "tier 3 " & Name & ": tables (Matrix_Failed)");
                  LV.Verify_LDT (G, P, Ch.U_Ldt, T_Block, Yc, Yp, Good);
                  Compare ("ldt yc", Yc, R_Ldt, 0);
                  Compare ("ldt yp", Yp, R_Ldt, NQ);
                  Check (Good, "tier 3 " & Name & ": verify_ldt");
                  LV.Build_A_Full (G, A, Lqc, Ch.Alphal, Ch.Alphaq, A_Full);
                  LV.Verify_Dot (G, B, P, A_Full, Ch.Alphal, T_Block,
                                 T_Dblock, Yc, Yp, Want, Pd, St_Dot);
                  Compare ("dot yc", Yc, R_Dot, 0);
                  Compare ("dot yp", Yp, R_Dot, NQ);
                  Check (Want = R_Want, "tier 3 " & Name & ": want_dot got "
                         & Image (Want));
                  Check (Pd = R_Proof, "tier 3 " & Name & ": proof_dot got "
                         & Image (Pd));
                  Check (St_Dot = Ok, "tier 3 " & Name & ": verify_dot "
                         & St_Dot'Image);
                  LV.Verify_Quad (G, P, Ch.U_Quad, T_Dblock, Yc, Yp, Good);
                  Compare ("quad yc", Yc, R_Quad, 0);
                  Compare ("quad yp", Yp, R_Quad, NQ);
                  Check (Good, "tier 3 " & Name & ": verify_quad");
                  --  The negative cases of the tests, on the same tables
                  --  and challenges (ADR 0040): one response polynomial
                  --  altered after the columns were chosen, and the
                  --  constant vector altered for the sum check.
                  declare
                     P2 : LP.Proof := P;
                     B2 : Element_Array := B;
                  begin
                     P2.Ldt_Poly (0) := P2.Ldt_Poly (0) + One;
                     LV.Verify_LDT (G, P2, Ch.U_Ldt, T_Block, Yc, Yp, Good);
                     Check (not Good, "tier 3 " & Name
                            & ": altered ldt_poly not refused (LDT_Failed)");
                     P2 := P;
                     P2.Linear_Poly (0) := P2.Linear_Poly (0) + One;
                     LV.Verify_Dot (G, B, P2, A_Full, Ch.Alphal, T_Block,
                                    T_Dblock, Yc, Yp, Want, Pd, St_Dot);
                     Check (St_Dot = Linear_Failed, "tier 3 " & Name
                            & ": altered linear_poly gave " & St_Dot'Image);
                     B2 (0) := B2 (0) + One;
                     LV.Verify_Dot (G, B2, P, A_Full, Ch.Alphal, T_Block,
                                    T_Dblock, Yc, Yp, Want, Pd, St_Dot);
                     Check (St_Dot = Linear_Sum_Failed, "tier 3 " & Name
                            & ": altered b gave " & St_Dot'Image);
                     P2 := P;
                     P2.Quad_Low (0) := P2.Quad_Low (0) + One;
                     LV.Verify_Quad (G, P2, Ch.U_Quad, T_Dblock, Yc, Yp, Good);
                     Check (not Good, "tier 3 " & Name
                            & ": altered quad_poly_low not refused");
                     P2 := P;
                     P2.Quad_High (0) := P2.Quad_High (0) + One;
                     LV.Verify_Quad (G, P2, Ch.U_Quad, T_Dblock, Yc, Yp, Good);
                     Check (not Good, "tier 3 " & Name
                            & ": altered quad_poly_high not refused");
                  end;
               end;
            end;
         end;
      end;
   end Check_Ligero;

   --  Stage 5 (ADR 0040): the complete verifier on the proof string of
   --  the circuit (root, sumcheck part, Ligero part concatenated), which
   --  must accept, then the negative cases built from those bytes with
   --  the status each must produce, on both fields (ADR 0044).
   procedure Check_Zk (Name : String; C : Circuit; Pub : Element_Array) is
      use Ligero_Geometry;
      use Verifier_Status;
      Cfg   : constant Config :=
        (Rate_Inv => Zk_Rate, Num_Queries => Zk_Nreq, Encoded_Len => Zk_Ncol);
      SL    : constant Natural := Zk_Sumcheck_Len;
      LL    : constant Natural := Zk_Ligero_Len;
      LO    : constant Natural := 32 + SL;
      Len   : constant Natural := LO + LL;
      Full  : Bytes.Byte_Array (0 .. Len - 1);
      Label : constant Bytes.Byte_Array := Zk_Label (0 .. Zk_Label_Len - 1);

      function LE32 (B : Bytes.Byte_Array; Off : Natural) return Natural is
        (Natural (B (Off)) + 256 * Natural (B (Off + 1))
         + 65536 * Natural (B (Off + 2)) + 16777216 * Natural (B (Off + 3)));

      function Size4 (N : Natural) return Bytes.Byte_Array is
        ([0 => Unsigned_8 (N mod 256), 1 => Unsigned_8 (N / 256 mod 256),
          2 => Unsigned_8 (N / 65536 mod 256),
          3 => Unsigned_8 (N / 16777216 mod 256)]);

      --  Full with bit 0 of byte Off flipped.
      function Flip (Off : Natural) return Bytes.Byte_Array is
         R : Bytes.Byte_Array := Full;
      begin
         R (Off) := R (Off) xor 1;
         return R;
      end Flip;

      procedure Expect
        (What : String; B : Bytes.Byte_Array; P : Element_Array;
         Want : Status)
      is
         St : Status;
      begin
         ZK.Verify (Label, Zk_Id, Cfg, C, P, B, St);
         Check (St = Want, "tier 3 " & Name & ": end to end, " & What
                & ": got " & St'Image & ", expected " & Want'Image);
      end Expect;
   begin
      if not (Have_Zk and Have_Zk_Sumcheck and Have_Zk_Ligero) then
         Report_Failure ("tier 3 " & Name & ": no complete proof string");
         return;
      end if;
      Full (0 .. 31)         := Zk_Root;
      Full (32 .. LO - 1)    := Zk_Sumcheck (0 .. SL - 1);
      Full (LO .. Len - 1)   := Zk_Ligero (0 .. LL - 1);
      Expect ("the Appendix B.3 proof", Full, Pub, Ok);
      Expect ("a public input too many", Full, Pub & Zero,
              Public_Input_Length);
      if not Valid (Cfg) then
         return;
      end if;
      declare
         G      : constant Valid_Geometry :=
           Make (Cfg, ZK.Witness_Count (C), C.Last_Layer + 1);
         Size   : constant Natural := LP.Size;
         Sub    : constant Natural := LP.Sub_Size;
         Total  : constant Natural := LP.Opened (G);
         Nonces : constant Natural := LO + (2 * G.Dblock_Len + G.Num_Queries) * Size;
         Cols   : constant Natural := Nonces + 32 * G.Num_Queries;
         R0     : constant Natural := LE32 (Full, Cols);
         --  The first run that has elements: its header, its width.
         Head   : constant Natural := (if R0 > 0 then Cols else Cols + 4);
         Width  : constant Natural := (if R0 > 0 then Size else Sub);
         Run    : constant Natural := LE32 (Full, Head);
         Elt    : constant Natural := Head + 4;
         P      : LP.Proof
           (Ldt_Last    => G.Block_Len - 1,
            Linear_Last => G.Dblock_Len - 1,
            Low_Last    => G.Num_Queries - 1,
            High_Last   => G.Dblock_Len - G.Block_Len - 1,
            Nonce_Last  => G.Num_Queries - 1,
            Col_Last    => Total - 1,
            Path_Last   => 2 * Num_Leaves (G) - 1);
         Next   : Natural;
         St     : Status;
      begin
         LP.Read (Zk_Ligero (0 .. LL - 1), 0, G, P, Next, St);
         if St /= Ok then
            Report_Failure ("tier 3 " & Name & ": Ligero part unreadable");
            return;
         end if;
         declare
            Count_Off : constant Natural := Len - 4 - 32 * P.Path_Count;
            Path_Off  : constant Natural := Count_Off + 4;
         begin
            Expect ("an altered opened column element", Flip (Elt), Pub,
                    Merkle_Failed);
            Expect ("an altered nonce", Flip (Nonces), Pub, Merkle_Failed);
            if P.Path_Count > 0 then
               Expect ("an altered path digest", Flip (Path_Off), Pub,
                       Merkle_Failed);
            end if;
            --  The response polynomials are absorbed before the columns
            --  are chosen: an altered polynomial moves the queried
            --  columns and the Merkle check fails first, as upstream.
            --  The test statuses are exercised at the step level, in
            --  Check_Ligero (ADR 0040 amended, block 5).
            Expect ("an altered element of ldt_poly", Flip (LO), Pub,
                    Merkle_Failed);
            Expect ("an altered element of linear_poly",
                    Flip (LO + G.Block_Len * Size), Pub, Merkle_Failed);
            Expect ("an altered element of quad_poly_low",
                    Flip (LO + (G.Block_Len + G.Dblock_Len) * Size), Pub,
                    Merkle_Failed);
            Expect ("an altered element of quad_poly_high",
                    Flip (LO + (G.Block_Len + G.Dblock_Len + G.Num_Queries)
                              * Size),
                    Pub, Merkle_Failed);
            Expect ("a path one digest too long",
                    Full (0 .. Count_Off - 1) & Size4 (P.Path_Count + 1)
                    & Full (Path_Off .. Len - 1) & Full (Path_Off .. Path_Off + 31),
                    Pub, Merkle_Failed);
            if P.Path_Count > 0 then
               Expect ("a path one digest too short",
                       Full (0 .. Count_Off - 1) & Size4 (P.Path_Count - 1)
                       & Full (Path_Off .. Len - 33),
                       Pub, Merkle_Failed);
            end if;
            Expect ("a second zero-length run",
                    Full (0 .. Cols - 1)
                    & (if R0 > 0 then Size4 (0) & Size4 (0) else Size4 (0))
                    & Full (Cols .. Len - 1),
                    Pub, Proof_Encoding);
            if Run > 40 then
               Expect ("a zero-length run that is not the first",
                       Full (0 .. Head - 1) & Size4 (40)
                       & Full (Elt .. Elt + 40 * Width - 1) & Size4 (0)
                       & Full (Elt + 40 * Width .. Len - 1),
                       Pub, Proof_Encoding);
            end if;
            Expect ("a run beyond the total",
                    Full (0 .. Head - 1) & Size4 (Total + 1)
                    & Full (Elt .. Len - 1),
                    Pub, Proof_Encoding);
            Expect ("trailing bytes", Full & Bytes.Byte_Array'[0 => 0], Pub,
                    Proof_Encoding);
         end;
      end;
   end Check_Zk;

   procedure Check_Replay
     (Name : String;
      C    : Circuit;
      Pub  : Element_Array;
      Prf  : SV.Sumcheck_Proof;
      Ch   : SV.Challenges;
      A    : SV.Ligero_Terms;
      B    : Element_Array;
      Lqc  : SV.Lqc_Array)
   is
      use type ST.Status;
      use type SV.Lqc_Array;
   begin
      if not Have_Zk or else not Have_Zk_Sumcheck
        or else Zk_Name (1 .. Zk_Name_Len) /= Name
      then
         Report_Failure ("tier 3 " & Name & ": no zk_proof lines for the replay");
         return;
      end if;
      --  The reader: the sumcheck bytes of the draft into the recorded
      --  padded proof.
      declare
         Prf2 : SV.Sumcheck_Proof (Last => Prf.Last);
         Stat : ST.Status;
         Same : Boolean := True;
      begin
         if Zk_Sumcheck_Len /= SV.Proof_Total (C) * ST.Size then
            Report_Failure
              ("tier 3 " & Name & ": sumcheck part is" & Zk_Sumcheck_Len'Image
               & " bytes, the circuit needs"
               & Natural'Image (SV.Proof_Total (C) * ST.Size));
            return;
         end if;
         ST.Read_Sumcheck_Proof
           (Zk_Sumcheck (0 .. Zk_Sumcheck_Len - 1), C, Prf2, Stat);
         Check (Stat = ST.Ok,
                "tier 3 " & Name & ": reader status " & Stat'Image);
         for I in Prf2.Evals'Range loop
            if Prf2.Evals (I) /= Prf.Evals (I) then
               if Same then
                  Report_Failure
                    ("tier 3 " & Name & ": read proof differs at" & I'Image
                     & ": got " & Image (Prf2.Evals (I))
                     & " recorded " & Image (Prf.Evals (I)));
               end if;
               Same := False;
            end if;
         end loop;
         Check (Same, "tier 3 " & Name & ": read proof");
      end;
      --  The replay: every challenge the recording holds.
      declare
         Ch2  : SV.Challenges (Last => Ch.Last);
         Stat : ST.Status;
         Same : Boolean := True;
         A2   : SV.Ligero_Terms (Max => A.Max);
         B2   : Element_Array (B'Range);
         Lqc2 : SV.Lqc_Array (Lqc'Range);
      begin
         ST.Replay_Challenges
           (Zk_Label (0 .. Zk_Label_Len - 1), Zk_Root, Zk_Id, C, Pub, Prf,
            Ch2, Stat);
         Check (Stat = ST.Ok,
                "tier 3 " & Name & ": replay status " & Stat'Image);
         for I in Ch2.G'Range loop
            if Ch2.G (I) /= Ch.G (I) then
               if Same then
                  Report_Failure
                    ("tier 3 " & Name & ": replayed g differs at" & I'Image
                     & ": got " & Image (Ch2.G (I))
                     & " recorded " & Image (Ch.G (I)));
               end if;
               Same := False;
            end if;
         end loop;
         for I in Ch2.Layer'Range loop
            if Ch2.Layer (I) /= Ch.Layer (I) then
               if Same then
                  Report_Failure
                    ("tier 3 " & Name & ": replayed layer challenge differs at"
                     & I'Image & ": got " & Image (Ch2.Layer (I))
                     & " recorded " & Image (Ch.Layer (I)));
               end if;
               Same := False;
            end if;
         end loop;
         if Ch2.Alpha_Input /= Ch.Alpha_Input then
            if Same then
               Report_Failure
                 ("tier 3 " & Name & ": replayed alpha_input got "
                  & Image (Ch2.Alpha_Input) & " recorded "
                  & Image (Ch.Alpha_Input));
            end if;
            Same := False;
         end if;
         Check (Same, "tier 3 " & Name & ": replayed challenges");
         --  Both ways: the core on the replayed record emits what it
         --  emitted on the recorded one.
         SV.Verifier_Core (C, Pub, Prf, Ch2, A2, B2, Lqc2);
         Same := A2.Count = A.Count and then B2 = B and then Lqc2 = Lqc;
         if Same then
            for K in 0 .. A.Count - 1 loop
               if A2.Coeff (K) /= A.Coeff (K)
                 or else A2.Constraint (K) /= A.Constraint (K)
                 or else A2.Witness (K) /= A.Witness (K)
               then
                  Same := False;
               end if;
            end loop;
         end if;
         Check (Same, "tier 3 " & Name & ": core on the replayed record");
         --  Stage 5: the Ligero verifier continues on this transcript;
         --  then the complete verifier from the proof string.
         if Same then
            Check_Ligero (Name, C, A2, B2, Lqc2);
            Check_Zk (Name, C, Pub);
         end if;
      end;
      --  A proof with a non-canonical element must be refused, for the
      --  fields that reject encodings: every byte of the first element
      --  set, which is at or above p for P-256.
      if SA.F.Sampling_Rejects then
         declare
            Bad  : Bytes.Byte_Array (0 .. Zk_Sumcheck_Len - 1) :=
              Zk_Sumcheck (0 .. Zk_Sumcheck_Len - 1);
            Prf3 : SV.Sumcheck_Proof (Last => Prf.Last);
            Stat : ST.Status;
         begin
            Bad (0 .. ST.Size - 1) := [others => 16#FF#];
            ST.Read_Sumcheck_Proof (Bad, C, Prf3, Stat);
            Check (Stat = ST.Bad_Element,
                   "tier 3 " & Name & ": non-canonical element not refused");
         end;
      end if;
      Have_Zk := False;
      Have_Zk_Sumcheck := False;
      Have_Zk_Ligero := False;
      Zk_Nonce_Given := [others => False];
   end Check_Replay;

   procedure Finish_Tier3 is
      Name : constant String := C_Name (1 .. C_Name_Len);
   begin
      if not (Have_Public and Have_Pad and Have_G and Have_Alpha)
        or else Chal_Layers /= C_NL or else Proof_Layers /= C_NL
        or else Cur_Layer /= C_NL - 1 or else Terms_Left /= 0
      then
         raise Parse_Error with "tier 3 block " & Name & " incomplete";
      end if;
      --  Exactly the constraints 0 .. NL and the triples 0 .. NL - 1 must
      --  be recorded: a recording that expects nothing proves nothing.
      for Cidx in 0 .. C_NL loop
         if not Exp_B_Given (Cidx) then
            raise Parse_Error with "tier 3 block " & Name
              & ": constraint" & Cidx'Image & " not recorded";
         end if;
      end loop;
      for J in 0 .. C_NL - 1 loop
         if not Exp_Lqc_Given (J) then
            raise Parse_Error with "tier 3 block " & Name
              & ": lqc of layer" & J'Image & " not recorded";
         end if;
      end loop;
      if Exp_B_Count /= C_NL + 1 then
         raise Parse_Error with "tier 3 block " & Name
           & ": constraint index beyond NL";
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
         if not Well_Formed (Raw) then
            Report_Failure ("tier 3 circuit " & Name & " not well formed");
            return;
         end if;
         declare
            C   : constant Circuit := Raw;
            Pub : Element_Array (0 .. C_Npublic - 1);
            Ch  : SV.Challenges (Last => Chal_Count - 1);
            Prf : SV.Sumcheck_Proof (Last => Proof_Count - 1);
            A   : SV.Ligero_Terms (Max => SV.A_Bound (C));
            B   : Element_Array (0 .. C_NL);
            Lqc : SV.Lqc_Array (0 .. C_NL - 1);
         begin
            for I in Pub'Range loop
               Pub (I) := Pub_Buf (I);
            end loop;
            for I in 0 .. Max_Logw - 1 loop
               Ch.G (I) := G_Buf (I);
            end loop;
            for I in 0 .. Chal_Count - 1 loop
               Ch.Layer (I) := Chal_Buf (I);
            end loop;
            Ch.Alpha_Input := Alpha_In;
            for I in 0 .. Proof_Count - 1 loop
               Prf.Evals (I) := Proof_Buf (I);
            end loop;
            Check (Pad_Base_Val = C_Ninput - C_Npublic,
                   "tier 3 " & Name & ": pad_base is not ninput - npublic");
            Check (Chal_Count = SV.Chal_Total (C)
                   and then Proof_Count = SV.Proof_Total (C),
                   "tier 3 " & Name & ": challenge or proof count");
            SV.Verifier_Core (C, Pub, Prf, Ch, A, B, Lqc);
            Check_Replay (Name, C, Pub, Prf, Ch, A, B, Lqc);
            --  b, per constraint.
            for Cidx in 0 .. C_NL loop
               if Exp_B_Given (Cidx) then
                  Check (B (Cidx) = Exp_B (Cidx),
                         "tier 3 " & Name & ": b of constraint" & Cidx'Image
                         & " got " & Image (B (Cidx))
                         & " expected " & Image (Exp_B (Cidx)));
               end if;
            end loop;
            --  A, per constraint, as sets of (variable, coefficient) with
            --  zero coefficients ignored on both sides.
            for Cidx in 0 .. C_NL loop
               if Exp_B_Given (Cidx) then
                  declare
                     Good : Boolean := True;
                  begin
                     --  every recorded non-zero term is emitted
                     for K in 0 .. Exp_Terms - 1 loop
                        if Exp_Cons (K) = Cidx and then Exp_Coeff (K) /= Zero
                        then
                           declare
                              Found : Boolean := False;
                           begin
                              for L in 0 .. A.Count - 1 loop
                                 if A.Constraint (L) = Cidx
                                   and then A.Witness (L) = Exp_Var (K)
                                   and then A.Coeff (L) = Exp_Coeff (K)
                                 then
                                    Found := True;
                                 end if;
                              end loop;
                              if not Found then
                                 Good := False;
                                 TIO.Put_Line
                                   ("  constraint" & Cidx'Image & " variable"
                                    & Exp_Var (K)'Image & ": expected "
                                    & Image (Exp_Coeff (K)) & " not emitted");
                              end if;
                           end;
                        end if;
                     end loop;
                     --  every emitted non-zero term is recorded with the
                     --  same coefficient
                     for L in 0 .. A.Count - 1 loop
                        if A.Constraint (L) = Cidx and then A.Coeff (L) /= Zero
                        then
                           declare
                              Found : Boolean := False;
                           begin
                              for K in 0 .. Exp_Terms - 1 loop
                                 if Exp_Cons (K) = Cidx
                                   and then Exp_Var (K) = A.Witness (L)
                                   and then Exp_Coeff (K) = A.Coeff (L)
                                 then
                                    Found := True;
                                 end if;
                              end loop;
                              if not Found then
                                 Good := False;
                                 TIO.Put_Line
                                   ("  constraint" & Cidx'Image & " variable"
                                    & A.Witness (L)'Image & ": emitted "
                                    & Image (A.Coeff (L)) & " not recorded");
                              end if;
                           end;
                        end if;
                     end loop;
                     Check (Good,
                            "tier 3 " & Name & ": constraint" & Cidx'Image);
                  end;
               end if;
            end loop;
            for J in 0 .. C_NL - 1 loop
               if Exp_Lqc_Given (J) then
                  Check (Lqc (J) = Exp_Lqc (J),
                         "tier 3 " & Name & ": lqc of layer" & J'Image);
               end if;
            end loop;
         end;
      end;
   end Finish_Tier3;

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
            Tier3 := False;
            Have_Public := False;
            Have_Pad := False;
            Have_G := False;
            Chal_Count := 0;
            Chal_Layers := 0;
            Proof_Count := 0;
            Proof_Layers := 0;
            Have_Alpha := False;
            Exp_Terms := 0;
            Exp_B_Count := 0;
            Exp_B_Given := [others => False];
            Exp_Lqc_Given := [others => False];
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
         elsif Op = "public" then
            if not In_Circuit or else Count - 1 /= C_Npublic then
               raise Parse_Error with "public length";
            end if;
            for I in 0 .. C_Npublic - 1 loop
               Pub_Buf (I) := E (2 + I);
            end loop;
            Have_Public := True;
            Tier3 := True;
         elsif Op = "pad_base" then
            Pad_Base_Val := Nat (F (2));
            Have_Pad := True;
            Tier3 := True;
         elsif Op = "g" then
            if Count - 1 /= Max_Logw then
               raise Parse_Error with "g expects" & Max_Logw'Image & " values";
            end if;
            for I in 0 .. Max_Logw - 1 loop
               G_Buf (I) := E (2 + I);
            end loop;
            Have_G := True;
            Tier3 := True;
         elsif Op = "layer_challenges" then
            declare
               J    : constant Natural := Nat (F (2));
               Logw : Natural;
            begin
               if not In_Circuit or else J /= Chal_Layers
                 or else J > Cur_Layer
               then
                  raise Parse_Error with "unexpected layer_challenges";
               end if;
               Logw := Layers (J).Logw;
               if Count - 2 /= 2 * Logw + 2 then
                  raise Parse_Error with "layer_challenges length";
               end if;
               for I in 0 .. 2 * Logw + 1 loop
                  Chal_Buf (Chal_Count + I) := E (3 + I);
               end loop;
               Chal_Count := Chal_Count + 2 * Logw + 2;
               Chal_Layers := Chal_Layers + 1;
            end;
            Tier3 := True;
         elsif Op = "proof" then
            declare
               J    : constant Natural := Nat (F (2));
               Logw : Natural;
            begin
               if not In_Circuit or else J /= Proof_Layers
                 or else J > Cur_Layer
               then
                  raise Parse_Error with "unexpected proof";
               end if;
               Logw := Layers (J).Logw;
               if Count - 2 /= 4 * Logw + 2 then
                  raise Parse_Error with "proof length";
               end if;
               for I in 0 .. 4 * Logw + 1 loop
                  Proof_Buf (Proof_Count + I) := E (3 + I);
               end loop;
               Proof_Count := Proof_Count + 4 * Logw + 2;
               Proof_Layers := Proof_Layers + 1;
            end;
            Tier3 := True;
         elsif Op = "alpha_input" then
            Alpha_In := E (2);
            Have_Alpha := True;
            Tier3 := True;
         elsif Op = "zk_proof" then
            if Count /= 5 then
               raise Parse_Error with "zk_proof expects 4 values";
            end if;
            if F (2)'Length > Zk_Name'Length then
               raise Parse_Error with "zk_proof name too long";
            end if;
            Zk_Name_Len := F (2)'Length;
            Zk_Name (1 .. Zk_Name_Len) := F (2);
            Hex_Into (F (3), Zk_Label, Zk_Label_Len);
            declare
               Len : Natural;
            begin
               Hex_Into (F (4), Zk_Root, Len);
               if Len /= 32 then
                  raise Parse_Error with "zk_proof root must be 32 bytes";
               end if;
               Hex_Into (F (5), Zk_Id, Len);
               if Len /= 32 then
                  raise Parse_Error with "zk_proof identifier must be 32 bytes";
               end if;
            end;
            Have_Zk := True;
         elsif Op = "zk_sumcheck" then
            if Count /= 3 then
               raise Parse_Error with "zk_sumcheck expects 2 values";
            end if;
            if not Have_Zk or else Zk_Name (1 .. Zk_Name_Len) /= F (2) then
               raise Parse_Error with "zk_sumcheck before its zk_proof line";
            end if;
            Hex_Into (F (3), Zk_Sumcheck, Zk_Sumcheck_Len);
            Have_Zk_Sumcheck := True;
         elsif Op = "zk_ligero" then
            if Count /= 6 then
               raise Parse_Error with "zk_ligero expects 5 values";
            end if;
            if not Have_Zk or else Zk_Name (1 .. Zk_Name_Len) /= F (2) then
               raise Parse_Error with "zk_ligero before its zk_proof line";
            end if;
            Zk_Rate := Nat (F (3));
            Zk_Nreq := Nat (F (4));
            Zk_Ncol := Nat (F (5));
            Hex_Into (F (6), Zk_Ligero, Zk_Ligero_Len);
            Have_Zk_Ligero := True;
         elsif Op = "zk_nonce" then
            if Count /= 4 then
               raise Parse_Error with "zk_nonce expects 3 values";
            end if;
            if not Have_Zk or else Zk_Name (1 .. Zk_Name_Len) /= F (2) then
               raise Parse_Error with "zk_nonce before its zk_proof line";
            end if;
            declare
               K   : constant Natural := Nat (F (3));
               Len : Natural;
            begin
               if K >= Max_Nonces then
                  raise Parse_Error with "zk_nonce index too large";
               end if;
               Hex_Into (F (4), Zk_Nonces (K), Len);
               if Len /= 32 then
                  raise Parse_Error with "zk_nonce must be 32 bytes";
               end if;
               Zk_Nonce_Given (K) := True;
            end;
         elsif Op = "claim" then
            --  Optional intermediate claims: parsed and accepted; the
            --  comparison of intermediate claims is not implemented
            --  (the emitted constraints cover the final values).
            Tier3 := True;
         elsif Op = "constraint" then
            declare
               Cidx : constant Natural := Nat (F (2));
               NT   : constant Natural := Nat (F (4));
            begin
               if not In_Circuit or else Cidx > C_NL
                 or else Count /= 4 + 2 * NT
               then
                  raise Parse_Error with "constraint line";
               end if;
               if Exp_B_Given (Cidx) then
                  raise Parse_Error with "constraint" & Cidx'Image
                    & " recorded twice";
               end if;
               Exp_B (Cidx) := E (3);
               Exp_B_Given (Cidx) := True;
               Exp_B_Count := Natural'Max (Exp_B_Count, Cidx + 1);
               for I in 0 .. NT - 1 loop
                  Exp_Cons (Exp_Terms) := Cidx;
                  Exp_Var (Exp_Terms) := Nat (F (5 + 2 * I));
                  Exp_Coeff (Exp_Terms) := E (6 + 2 * I);
                  Exp_Terms := Exp_Terms + 1;
               end loop;
            end;
            Tier3 := True;
         elsif Op = "lqc" then
            declare
               J : constant Natural := Nat (F (2));
            begin
               if not In_Circuit or else J >= C_NL then
                  raise Parse_Error with "lqc layer";
               end if;
               if Exp_Lqc_Given (J) then
                  raise Parse_Error with "lqc of layer" & J'Image
                    & " recorded twice";
               end if;
               Exp_Lqc (J) :=
                 (X => Nat (F (3)), Y => Nat (F (4)), Z => Nat (F (5)));
               Exp_Lqc_Given (J) := True;
            end;
            Tier3 := True;
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
            if Tier3 then
               Finish_Tier3;
            else
               Finish_Circuit;
            end if;
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
