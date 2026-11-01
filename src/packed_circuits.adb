pragma SPARK_Mode (On);

package body Packed_Circuits is

   procedure Lemma_Step (P : Packed_Circuit; J, K : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Cursor_At);
   begin
      pragma Assert (Cursor_At (P, J, K) = Step (P, Cursor_At (P, J, K - 1)));
   end Lemma_Step;

   procedure Lemma_Term_Of (P : Packed_Circuit; J, K : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Cursor_At);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Term_At);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Valid);
      C : constant Cursor := Cursor_At (P, J, K - 1);
   begin
      pragma Assert (On_Delta (P, C));
      pragma Assert (Cursor_At (P, J, K) = Step (P, C));
      pragma Assert (Cursor_At (P, J, K).G = C.G + Delta_At (P, C).DG);
      pragma Assert (Cursor_At (P, J, K).H0 = C.H0 + Delta_At (P, C).DH0);
      pragma Assert (Cursor_At (P, J, K).H1 = C.H1 + Delta_At (P, C).DH1);
      pragma Assert (Cursor_At (P, J, K).G in 0 .. SA.Max_Wires - 1);
      pragma Assert (Cursor_At (P, J, K).H0 in 0 .. SA.Max_Wires - 1);
      pragma Assert (Cursor_At (P, J, K).H1 in 0 .. SA.Max_Wires - 1);
   end Lemma_Term_Of;

   function Expand (P : Packed_Circuit) return SA.Raw_Circuit is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Valid);
      R : SA.Raw_Circuit (P.Last_Layer, P.NT) :=
        (Last_Layer => P.Last_Layer,
         NT         => P.NT,
         Noutput    => P.Noutput,
         Ninput     => P.Ninput,
         Npublic    => P.Npublic,
         Layers     => P.Layers,
         Terms      => [others => (K => SA.Zero, G => 0, H0 => 0, H1 => 0)]);
   begin
      for J in 0 .. P.Last_Layer loop
         pragma Loop_Invariant (R.Layers = P.Layers);
         pragma Loop_Invariant
           (for all J2 in 0 .. J - 1 =>
              (for all K2 in 1 .. Layer_Len (P, J2) =>
                 R.Terms (P.Layers (J2).First + K2 - 1)
                   = Term_At (P, J2, K2)
                 and then
                 SA.Same (R.Terms (P.Layers (J2).First + K2 - 1).K,
                          Term_At (P, J2, K2).K)));
         for K in 1 .. Layer_Len (P, J) loop
            R.Terms (P.Layers (J).First + K - 1) := Term_At (P, J, K);
            pragma Loop_Invariant (R.Layers = P.Layers);
            pragma Loop_Invariant
              (for all J2 in 0 .. J - 1 =>
                 (for all K2 in 1 .. Layer_Len (P, J2) =>
                    R.Terms (P.Layers (J2).First + K2 - 1)
                    = Term_At (P, J2, K2)
                    and then
                    SA.Same (R.Terms (P.Layers (J2).First + K2 - 1).K,
                             Term_At (P, J2, K2).K)));
            pragma Loop_Invariant
              (for all K2 in 1 .. K =>
                 R.Terms (P.Layers (J).First + K2 - 1) = Term_At (P, J, K2)
                 and then
                 SA.Same (R.Terms (P.Layers (J).First + K2 - 1).K,
                          Term_At (P, J, K2).K));
         end loop;
      end loop;
      return R;
   end Expand;

   procedure Lemma_Valid (P : Packed_Circuit) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Valid);
   begin
      null;
   end Lemma_Valid;

   procedure Lemma_Valid_Intro (P : Packed_Circuit) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Valid);
   begin
      null;
   end Lemma_Valid_Intro;

   procedure Lemma_Walked_Start (P : Packed_Circuit; J : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Walked);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Valid);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Cursor_At);
   begin
      null;
   end Lemma_Walked_Start;

   procedure Lemma_Walked_Step
     (P : Packed_Circuit; J, K : Natural; C : Cursor)
   is
      --  C is named only by the contract.
      pragma Unreferenced (C);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Walked);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Valid);
   begin
      Lemma_Term_Of (P, J, K);
      pragma Assert
        (Expand (P).Terms (P.Layers (J).First + K - 1) = Term_At (P, J, K));
      pragma Assert
        (SA.Same (Expand (P).Terms (P.Layers (J).First + K - 1).K,
                  Term_At (P, J, K).K));
   end Lemma_Walked_Step;

end Packed_Circuits;
