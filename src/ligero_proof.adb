pragma SPARK_Mode (On);

package body Ligero_Proof is

   function Row_Off (G : Valid_Geometry; Row : Natural) return Natural is
   begin
      SPARK.Lemmas.Integer_Arithmetic.Lemma_Mult_Is_Monotonic
        (Row + 1, G.Total_Rows, G.Num_Queries);
      return Row * G.Num_Queries;
   end Row_Off;

   ----------------------------------------------------------------------
   --  The hidden predicate, one step at a time
   ----------------------------------------------------------------------

   --  Nothing remains: well coded whatever follows.
   procedure Lemma_Done
     (B : Byte_Array; Pos : Natural; Sub_Run, First : Boolean)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => B'First = 0,
     Post   => Well_Coded (B, Pos, 0, Sub_Run, First)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Well_Coded);
   begin
      null;
   end Lemma_Done;

   --  One run that obeys the rules, followed by a well coded rest, is
   --  well coded.
   procedure Lemma_Step
     (B       : Byte_Array;
      Pos     : Natural;
      Left     : Natural;
      Sub_Run : Boolean;
      First   : Boolean;
      R       : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    =>
       B'First = 0 and then Left > 0
       and then B'Length >= 4 and then Pos <= B'Length - 4
       and then Size_4 (B, Pos) <= Max_Run
       and then R = Natural (Size_4 (B, Pos))
       and then R <= Left
       and then (R > 0 or else First)
       and then Long_Long_Integer (R) * Long_Long_Integer (Run_Width (Sub_Run))
                <= Long_Long_Integer (B'Length - Pos - 4),
     Post   =>
       (if Well_Coded (B, Pos + 4 + R * Run_Width (Sub_Run), Left - R,
                       not Sub_Run, False)
        then Well_Coded (B, Pos, Left, Sub_Run, First))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Well_Coded);
   begin
      null;
   end Lemma_Step;

   ----------------------------------------------------------------------
   --  Elements
   ----------------------------------------------------------------------

   --  Dest'Length elements from B at Pos, in the subfield encoding
   --  when Sub; Pos advanced past them. Ok is False on a non-canonical
   --  encoding, Dest then unspecified.
   procedure Read_Elements
     (B    : Byte_Array;
      Pos  : in out Natural;
      Sub  : Boolean;
      Dest : out Element_Array;
      Ok   : out Boolean)
   with
     Global => null,
     Pre    =>
       B'First = 0 and then Dest'Length <= Max_Run
       and then Pos <= B'Length
       and then Long_Long_Integer (Dest'Length)
                * Long_Long_Integer (Run_Width (Sub))
                <= Long_Long_Integer (B'Length - Pos),
     Post   =>
       Pos >= Pos'Old
       and then Pos <= Pos'Old + Dest'Length * Run_Width (Sub)
       and then (if Ok then Pos = Pos'Old + Dest'Length * Run_Width (Sub))
   is
      W  : constant Positive := Run_Width (Sub);
      E  : Element;
      Ac : Boolean;
   begin
      Dest := [others => Zero];
      Ok := True;
      for I in Dest'Range loop
         pragma Loop_Invariant
           (Pos = Pos'Loop_Entry + (I - Dest'First) * W);
         if Sub then
            SA.F.From_Subfield_Bytes (B (Pos .. Pos + Sub_Size - 1), E, Ac);
         else
            SA.F.From_Bytes (B (Pos .. Pos + Size - 1), E, Ac);
         end if;
         if not Ac then
            Ok := False;
            return;
         end if;
         Dest (I) := E;
         Pos := Pos + W;
      end loop;
   end Read_Elements;

   ----------------------------------------------------------------------
   --  The reader
   ----------------------------------------------------------------------

   procedure Read
     (B    : Byte_Array;
      Off  : Natural;
      G    : Valid_Geometry;
      P    : out Proof;
      Next : out Natural;
      St   : out Status)
   is
      Total   : constant Natural := Opened (G);
      Pos     : Natural := Off;
      Cnt     : Natural := 0;
      Sub_Run : Boolean := False;
      First   : Boolean := True;
      Acc     : Boolean;
      R32     : Unsigned_32;
      R       : Natural;
   begin
      P := (Ldt_Last    => P.Ldt_Last,
            Linear_Last => P.Linear_Last,
            Low_Last    => P.Low_Last,
            High_Last   => P.High_Last,
            Nonce_Last  => P.Nonce_Last,
            Col_Last    => P.Col_Last,
            Path_Last   => P.Path_Last,
            Ldt_Poly    => [others => Zero],
            Linear_Poly => [others => Zero],
            Quad_Low    => [others => Zero],
            Quad_High   => [others => Zero],
            Nonces      => [others => [others => 0]],
            Columns     => [others => Zero],
            Path        => [others => [others => 0]],
            Path_Count  => 0);
      Next := Off;
      St   := Proof_Encoding;

      --  The four polynomials and the nonces.
      if B'Length - Off < Fixed_Len (G) then
         return;
      end if;
      declare
         Start : constant Natural := Off + Fixed_Len (G)
           with Ghost => Proof_Only;
      begin
         Read_Elements (B, Pos, False, P.Ldt_Poly, Acc);
         if not Acc then
            return;
         end if;
         Read_Elements (B, Pos, False, P.Linear_Poly, Acc);
         if not Acc then
            return;
         end if;
         Read_Elements (B, Pos, False, P.Quad_Low, Acc);
         if not Acc then
            return;
         end if;
         Read_Elements (B, Pos, False, P.Quad_High, Acc);
         if not Acc then
            return;
         end if;
         for I in P.Nonces'Range loop
            pragma Loop_Invariant
              (Pos = Off + (2 * G.Dblock_Len + G.Num_Queries) * Size + 32 * I);
            P.Nonces (I) := B (Pos .. Pos + 31);
            Pos := Pos + 32;
         end loop;
         pragma Assert (Proof_Only => Pos = Start);

         --  The opened columns, run by run.
         while Cnt < Total loop
            pragma Loop_Invariant (Pos in Off .. B'Length);
            pragma Loop_Invariant (Proof_Only => Pos >= Start);
            pragma Loop_Invariant (Cnt <= Total);
            pragma Loop_Invariant
              (Proof_Only =>
                 (if Well_Coded (B, Pos, Total - Cnt, Sub_Run, First)
                  then Well_Coded (B, Start, Total, False, True)));
            pragma Loop_Variant (Increases => Cnt,
                                 Decreases => (if First then 1 else 0));
            if B'Length - Pos < 4 then
               return;
            end if;
            R32 := Size_4 (B, Pos);
            if R32 > Max_Run then
               return;
            end if;
            R := Natural (R32);
            if R > Total - Cnt then
               return;
            end if;
            if R = 0 and then not First then
               return;
            end if;
            if Long_Long_Integer (R) * Long_Long_Integer (Run_Width (Sub_Run))
               > Long_Long_Integer (B'Length - Pos - 4)
            then
               return;
            end if;
            Lemma_Step (B, Pos, Total - Cnt, Sub_Run, First, R);
            Pos := Pos + 4;
            if R > 0 then
               Read_Elements
                 (B, Pos, Sub_Run, P.Columns (Cnt .. Cnt + R - 1), Acc);
               if not Acc then
                  return;
               end if;
            end if;
            Cnt     := Cnt + R;
            Sub_Run := not Sub_Run;
            First   := False;
         end loop;
         Lemma_Done (B, Pos, Sub_Run, First);

         --  The path: a 4-byte count, then that many digests.
         if B'Length - Pos < 4 then
            return;
         end if;
         R32 := Size_4 (B, Pos);
         if R32 > Unsigned_32 (P.Path_Last + 1) then
            return;
         end if;
         R   := Natural (R32);
         pragma Assert (R <= P.Path_Last + 1);
         Pos := Pos + 4;
         if B'Length - Pos < 32 * R then
            return;
         end if;
         for I in 0 .. R - 1 loop
            pragma Loop_Invariant (Pos + 32 * R <= B'Length);
            pragma Loop_Invariant (Proof_Only => Pos >= Start);
            P.Path (I) := B (Pos + 32 * I .. Pos + 32 * I + 31);
         end loop;
         Pos := Pos + 32 * R;
         P.Path_Count := R;
         Next := Pos;
         St   := Ok;
      end;
   end Read;

end Ligero_Proof;
