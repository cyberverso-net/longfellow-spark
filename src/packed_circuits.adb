pragma SPARK_Mode (On);

package body Packed_Circuits is

   procedure Lemma_Term_Of (P : Packed_Circuit; J, K : Natural) is
      C : constant Cursor := Cursor_At (P, J, K - 1);
   begin
      pragma Assert (On_Delta (P, C));
      pragma Assert (Cursor_At (P, J, K) = Step (P, C));
      pragma Assert (Cursor_At (P, J, K).G = C.G + Delta_At (P, C).DG);
      pragma Assert (Cursor_At (P, J, K).H0 = C.H0 + Delta_At (P, C).DH0);
      pragma Assert (Cursor_At (P, J, K).H1 = C.H1 + Delta_At (P, C).DH1);
   end Lemma_Term_Of;

   function Expand (P : Packed_Circuit) return SA.Raw_Circuit is
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
                 R.Terms (P.Layers (J2).First + K2 - 1) = Term_At (P, J2, K2)));
         for K in 1 .. Layer_Len (P, J) loop
            R.Terms (P.Layers (J).First + K - 1) := Term_At (P, J, K);
            pragma Loop_Invariant (R.Layers = P.Layers);
            pragma Loop_Invariant
              (for all J2 in 0 .. J - 1 =>
                 (for all K2 in 1 .. Layer_Len (P, J2) =>
                    R.Terms (P.Layers (J2).First + K2 - 1)
                    = Term_At (P, J2, K2)));
            pragma Loop_Invariant
              (for all K2 in 1 .. K =>
                 R.Terms (P.Layers (J).First + K2 - 1) = Term_At (P, J, K2));
         end loop;
      end loop;
      return R;
   end Expand;

end Packed_Circuits;
