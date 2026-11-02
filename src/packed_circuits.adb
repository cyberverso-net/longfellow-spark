pragma SPARK_Mode (On);

package body Packed_Circuits is

   use type SA.Element;
   use type SA.Term_Array;
   use type SA.Raw_Shape;

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

   -------------------------------------------------------------------
   --  The shape
   -------------------------------------------------------------------

   procedure Lemma_Shape_Of (P : Packed_Circuit) is
   begin
      SA.Lemma_Shape_Of (Expand (P));
      pragma Assert (SA.Shape_Of (Expand (P)) = Shape_Of (P));
   end Lemma_Shape_Of;

   -------------------------------------------------------------------
   --  Pack, and its proof: the packed form is described by Packing,
   --  established by the loops of Pack; the lemmas then take it from
   --  Packing to Valid and to Expand, layer by layer, term by term, by
   --  induction on the walk (Lemma_Step, Lemma_Term_Of).
   -------------------------------------------------------------------

   --  The number of layers with a term among the first J: the tokens
   --  Pack places before layer J.
   function Tokens_Before (C : SA.Raw_Circuit; J : Natural) return Natural
   is
     (if J = 0 then 0
      else Tokens_Before (C, J - 1)
           + (if C.Layers (J - 1).Last >= C.Layers (J - 1).First
              then 1 else 0))
   with Ghost => Proof_Only,
        Global => null,
        Pre    => J <= C.Last_Layer + 1,
        Post   => Tokens_Before'Result <= J,
        Subprogram_Variant => (Decreases => J);

   procedure Lemma_Tokens_Before_Mono
     (C : SA.Raw_Circuit; J1, J2 : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => J1 <= J2 and then J2 <= C.Last_Layer + 1,
     Post   => Tokens_Before (C, J1) <= Tokens_Before (C, J2);

   procedure Lemma_Tokens_Before_Mono
     (C : SA.Raw_Circuit; J1, J2 : Natural)
   is
   begin
      for K in J1 .. J2 - 1 loop
         pragma Assert (Tokens_Before (C, K + 1) >= Tokens_Before (C, K));
         pragma Loop_Invariant
           (Tokens_Before (C, J1) <= Tokens_Before (C, K + 1));
      end loop;
   end Lemma_Tokens_Before_Mono;

   --  The term indices of the layers before J: 0 .. Done (C, J).
   function Done (C : SA.Raw_Circuit; J : Natural) return Natural is
     (if J = 0 then 0 else C.Layers (J - 1).Last)
   with Ghost => Proof_Only,
        Global => null,
        Pre    => J <= C.Last_Layer + 1;

   --  The delta of term I of layer J as Pack writes it.
   function Delta_Ok
     (C : SA.Raw_Circuit; J : Natural; I : Positive; D : Packed_Delta)
      return Boolean
   is
     (D.DG = Long_Long_Integer (C.Terms (I).G)
             - (if I = C.Layers (J).First then 0
                else Long_Long_Integer (C.Terms (I - 1).G))
      and then
      D.DH0 = Long_Long_Integer (C.Terms (I).H0)
              - (if I = C.Layers (J).First then 0
                 else Long_Long_Integer (C.Terms (I - 1).H0))
      and then
      D.DH1 = Long_Long_Integer (C.Terms (I).H1)
              - (if I = C.Layers (J).First then 0
                 else Long_Long_Integer (C.Terms (I - 1).H1))
      and then D.K = I)
   with Ghost => Proof_Only,
        Global => null,
        Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
                  and then I in C.Layers (J).First .. C.Layers (J).Last;

   --  P is the packed form of C that Pack builds.
   function Packing (C : SA.Raw_Circuit; P : Packed_Circuit) return Boolean
   is
     (P.Last_Layer = C.Last_Layer and then P.NT = C.NT
      and then P.NC = C.NT and then P.ND = C.NT and then P.NE = C.NT
      and then P.NS = C.Last_Layer + 1
      and then P.Noutput = C.Noutput and then P.Ninput = C.Ninput
      and then P.Npublic = C.Npublic
      and then P.Layers = C.Layers
      and then (for all I in 1 .. C.NT =>
                  P.Constants (I) = C.Terms (I).K
                  and then P.Entries (I) = I)
      and then (for all J in 0 .. C.Last_Layer =>
                  P.Seg_Start (J + 1) = C.Layers (J).First
                  and then P.Seg_Len (J + 1)
                           = C.Layers (J).Last + 1 - C.Layers (J).First
                  and then (for all I in C.Layers (J).First
                                        .. C.Layers (J).Last =>
                              Delta_Ok (C, J, I, P.Deltas (I)))
                  and then P.Spans (J).First - 1
                           = (if J = 0 then 0 else P.Spans (J - 1).Last)
                  and then P.Spans (J).Last
                           = P.Spans (J).First - 1
                             + (if C.Layers (J).Last >= C.Layers (J).First
                                then 1 else 0)
                  and then (if C.Layers (J).Last >= C.Layers (J).First
                            then P.Spans (J).First <= P.NK
                                 and then P.Tokens (P.Spans (J).First)
                                          = J + 1))
      and then P.Spans (C.Last_Layer).Last = P.NK)
   with Ghost => Proof_Only,
        Global => null,
        Pre    => SA.Well_Formed (C);

   --  The cursor of layer J of the packed form after K terms: on the
   --  layer's one token at offset K while terms remain, past it after
   --  the last; the running sums are the wires of term K (zero before
   --  the first).
   function Pack_Cursor
     (C : SA.Raw_Circuit; P : Packed_Circuit; J, K : Natural) return Cursor
   is
     ((Tok => (if K > 0 and then K = Layer_Len (P, J)
               then P.Spans (J).First + 1 else P.Spans (J).First),
       Off => (if K = Layer_Len (P, J) then 0 else K),
       G   => (if K = 0 then 0
               else Long_Long_Integer
                      (C.Terms (C.Layers (J).First + K - 1).G)),
       H0  => (if K = 0 then 0
               else Long_Long_Integer
                      (C.Terms (C.Layers (J).First + K - 1).H0)),
       H1  => (if K = 0 then 0
               else Long_Long_Integer
                      (C.Terms (C.Layers (J).First + K - 1).H1))))
   with Ghost => Proof_Only,
        Global => null,
        Pre    => SA.Well_Formed (C) and then Packing (C, P)
                  and then J <= C.Last_Layer
                  and then K <= Layer_Len (P, J);

   --  The layers of a well-formed circuit are in order, pairwise: the
   --  conjunct of Layers_Ok that Well_Formed states only for neighbours.
   procedure Lemma_Layers_Ordered (C : SA.Raw_Circuit) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C),
     Post   => (for all J1 in 0 .. C.Last_Layer =>
                  (for all J2 in J1 + 1 .. C.Last_Layer =>
                     C.Layers (J1).Last < C.Layers (J2).First));

   procedure Lemma_Layers_Ordered (C : SA.Raw_Circuit) is
   begin
      for K in 1 .. C.Last_Layer loop
         pragma Loop_Invariant
           (for all J1 in 0 .. K - 1 =>
              (for all J2 in J1 + 1 .. K - 1 =>
                 C.Layers (J1).Last < C.Layers (J2).First));
         pragma Assert (C.Layers (K).First = C.Layers (K - 1).Last + 1);
         pragma Assert
           (for all J1 in 0 .. K - 1 =>
              C.Layers (J1).Last < C.Layers (K).First);
      end loop;
   end Lemma_Layers_Ordered;

   --  Counts_Ok of the packed form: a layer with a term has one token,
   --  whose segment has as many entries as the layer has terms.
   procedure Lemma_Pack_Counts (C : SA.Raw_Circuit; P : Packed_Circuit) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then Packing (C, P)
               and then Indices_Ok (P) and then Layers_Ok (P),
     Post   => Counts_Ok (P);

   procedure Lemma_Pack_Counts (C : SA.Raw_Circuit; P : Packed_Circuit) is
   begin
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant
           (for all J2 in 0 .. J - 1 =>
              Long_Long_Integer (P.Layers (J2).Last + 1 - P.Layers (J2).First)
              = Tok_Sum (P, P.Spans (J2).First, P.Spans (J2).Last));
         if C.Layers (J).Last >= C.Layers (J).First then
            declare
               F : constant Positive := P.Spans (J).First;
            begin
               pragma Assert (P.Spans (J).Last = F);
               pragma Assert (Tok_Sum (P, F, F - 1) = 0);
               pragma Assert
                 (Tok_Sum (P, F, F)
                  = Long_Long_Integer (P.Seg_Len (P.Tokens (F))));
               pragma Assert (P.Tokens (F) = J + 1);
            end;
         else
            pragma Assert (P.Spans (J).Last < P.Spans (J).First);
            pragma Assert
              (Tok_Sum (P, P.Spans (J).First, P.Spans (J).Last) = 0);
         end if;
      end loop;
   end Lemma_Pack_Counts;

   --  The cursor of a layer before any term is its Start.
   procedure Lemma_Cursor_At_Zero (P : Packed_Circuit; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Indices_Ok (P) and then Layers_Ok (P) and then Counts_Ok (P)
               and then J <= P.Last_Layer,
     Post   => Cursor_At (P, J, 0) = Start (P, J);

   procedure Lemma_Cursor_At_Zero (P : Packed_Circuit; J : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Cursor_At);
   begin
      null;
   end Lemma_Cursor_At_Zero;

   --  The walk of layer J of the packed form: after K terms the cursor
   --  is Pack_Cursor, by induction on K with one Lemma_Step per term.
   procedure Lemma_Pack_Walk
     (C : SA.Raw_Circuit; P : Packed_Circuit; J : Natural)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then Packing (C, P)
               and then Indices_Ok (P) and then Layers_Ok (P)
               and then Counts_Ok (P) and then J <= C.Last_Layer,
     Post   => (for all K in 0 .. Layer_Len (P, J) =>
                  Cursor_At (P, J, K) = Pack_Cursor (C, P, J, K));

   procedure Lemma_Pack_Walk
     (C : SA.Raw_Circuit; P : Packed_Circuit; J : Natural)
   is
      First : constant Positive := C.Layers (J).First;
      Len   : constant Natural := Layer_Len (P, J);
   begin
      Lemma_Cursor_At_Zero (P, J);
      pragma Assert (Cursor_At (P, J, 0) = Pack_Cursor (C, P, J, 0));
      for K in 1 .. Len loop
         pragma Loop_Invariant
           (for all K2 in 0 .. K - 1 =>
              Cursor_At (P, J, K2) = Pack_Cursor (C, P, J, K2));
         Lemma_Step (P, J, K);
         declare
            Cur : constant Cursor := Pack_Cursor (C, P, J, K - 1);
         begin
            pragma Assert (Cursor_At (P, J, K - 1) = Cur);
            pragma Assert (Cur.Tok = P.Spans (J).First);
            pragma Assert (Cur.Off = K - 1);
            pragma Assert (P.Tokens (Cur.Tok) = J + 1);
            pragma Assert (P.Seg_Len (J + 1) = Len);
            pragma Assert (On_Delta (P, Cur));
            pragma Assert
              (P.Seg_Start (P.Tokens (Cur.Tok)) + Cur.Off = First + K - 1);
            pragma Assert (P.Entries (First + K - 1) = First + K - 1);
            pragma Assert (Delta_At (P, Cur) = P.Deltas (First + K - 1));
            pragma Assert (Delta_Ok (C, J, First + K - 1, Delta_At (P, Cur)));
            pragma Assert (Step (P, Cur) = Pack_Cursor (C, P, J, K));
         end;
         pragma Assert (Cursor_At (P, J, K) = Pack_Cursor (C, P, J, K));
      end loop;
   end Lemma_Pack_Walk;

   --  Every walk of the packed form gives Pack_Cursor, so every wire
   --  the walks produce is a wire of C: Wires_Ok.
   procedure Lemma_Pack_Cursors (C : SA.Raw_Circuit; P : Packed_Circuit)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then Packing (C, P)
               and then Indices_Ok (P) and then Layers_Ok (P)
               and then Counts_Ok (P),
     Post   => Wires_Ok (P)
               and then
               (for all J in 0 .. C.Last_Layer =>
                  (for all K in 0 .. Layer_Len (P, J) =>
                     Cursor_At (P, J, K) = Pack_Cursor (C, P, J, K)));

   procedure Lemma_Pack_Cursors (C : SA.Raw_Circuit; P : Packed_Circuit)
   is
   begin
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant
           (for all J2 in 0 .. J - 1 =>
              (for all K in 0 .. Layer_Len (P, J2) =>
                 Cursor_At (P, J2, K) = Pack_Cursor (C, P, J2, K)));
         pragma Loop_Invariant
           (for all J2 in 0 .. J - 1 =>
              (for all K in 1 .. Layer_Len (P, J2) =>
                 Cursor_At (P, J2, K).G in 0 .. SA.Max_Wires - 1
                 and then Cursor_At (P, J2, K).H0 in 0 .. SA.Max_Wires - 1
                 and then Cursor_At (P, J2, K).H1 in 0 .. SA.Max_Wires - 1));
         Lemma_Pack_Walk (C, P, J);
         pragma Assert
           (for all K in 1 .. Layer_Len (P, J) =>
              Cursor_At (P, J, K).G
              = Long_Long_Integer (C.Terms (C.Layers (J).First + K - 1).G)
              and then Cursor_At (P, J, K).H0
                       = Long_Long_Integer
                           (C.Terms (C.Layers (J).First + K - 1).H0)
              and then Cursor_At (P, J, K).H1
                       = Long_Long_Integer
                           (C.Terms (C.Layers (J).First + K - 1).H1));
         pragma Assert
           (for all K in 1 .. Layer_Len (P, J) =>
              Cursor_At (P, J, K).G in 0 .. SA.Max_Wires - 1
              and then Cursor_At (P, J, K).H0 in 0 .. SA.Max_Wires - 1
              and then Cursor_At (P, J, K).H1 in 0 .. SA.Max_Wires - 1);
      end loop;
      pragma Assert (Wires_Ok (P));
   end Lemma_Pack_Cursors;

   --  Term K of layer J of the packed form is term K of layer J of C.
   procedure Lemma_Pack_Terms (C : SA.Raw_Circuit; P : Packed_Circuit) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then Packing (C, P) and then Valid (P)
               and then Indices_Ok (P) and then Layers_Ok (P)
               and then Counts_Ok (P)
               and then
               (for all J in 0 .. C.Last_Layer =>
                  (for all K in 0 .. Layer_Len (P, J) =>
                     Cursor_At (P, J, K) = Pack_Cursor (C, P, J, K))),
     Post   => (for all J in 0 .. C.Last_Layer =>
                  (for all K in 1 .. Layer_Len (P, J) =>
                     Term_At (P, J, K)
                     = C.Terms (C.Layers (J).First + K - 1)));

   procedure Lemma_Pack_Terms (C : SA.Raw_Circuit; P : Packed_Circuit) is
   begin
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant
           (for all J2 in 0 .. J - 1 =>
              (for all K in 1 .. Layer_Len (P, J2) =>
                 Term_At (P, J2, K) = C.Terms (C.Layers (J2).First + K - 1)));
         declare
            First : constant Positive := C.Layers (J).First;
         begin
            for K in 1 .. Layer_Len (P, J) loop
               pragma Loop_Invariant
                 (for all K2 in 1 .. K - 1 =>
                    Term_At (P, J, K2) = C.Terms (First + K2 - 1));
               Lemma_Term_Of (P, J, K);
               declare
                  Cur : constant Cursor := Pack_Cursor (C, P, J, K - 1);
               begin
                  pragma Assert (Cursor_At (P, J, K - 1) = Cur);
                  pragma Assert (P.Tokens (Cur.Tok) = J + 1);
                  pragma Assert
                    (P.Seg_Start (P.Tokens (Cur.Tok)) + Cur.Off
                     = First + K - 1);
                  pragma Assert (Delta_At (P, Cur) = P.Deltas (First + K - 1));
                  pragma Assert
                    (Delta_Ok (C, J, First + K - 1, Delta_At (P, Cur)));
                  pragma Assert
                    (Term_Of (P, Cur).K = C.Terms (First + K - 1).K);
                  pragma Assert
                    (Term_Of (P, Cur).G = C.Terms (First + K - 1).G);
                  pragma Assert
                    (Term_Of (P, Cur).H0 = C.Terms (First + K - 1).H0);
                  pragma Assert
                    (Term_Of (P, Cur).H1 = C.Terms (First + K - 1).H1);
                  pragma Assert (Term_Of (P, Cur) = C.Terms (First + K - 1));
               end;
               pragma Assert (Term_At (P, J, K) = C.Terms (First + K - 1));
            end loop;
         end;
      end loop;
   end Lemma_Pack_Terms;

   --  The expansion of the packed form is C: the header and the layers
   --  by the postcondition of Expand, the terms layer by layer.
   procedure Lemma_Pack_Expand (C : SA.Raw_Circuit; P : Packed_Circuit) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then Packing (C, P) and then Valid (P)
               and then
               (for all J in 0 .. C.Last_Layer =>
                  (for all K in 1 .. Layer_Len (P, J) =>
                     Term_At (P, J, K)
                     = C.Terms (C.Layers (J).First + K - 1))),
     Post   => Expand (P) = C;

   procedure Lemma_Pack_Expand (C : SA.Raw_Circuit; P : Packed_Circuit) is
      E : constant SA.Raw_Circuit := Expand (P);
   begin
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant
           (for all I in 1 .. Done (C, J) => E.Terms (I) = C.Terms (I));
         for I in C.Layers (J).First .. C.Layers (J).Last loop
            pragma Loop_Invariant
              (for all I2 in 1 .. I - 1 => E.Terms (I2) = C.Terms (I2));
            --  Term I is term K of layer J: the postcondition of Expand
            --  is instantiated in its own form, then read at I.
            declare
               K : constant Positive := I - C.Layers (J).First + 1;
            begin
               pragma Assert (K <= Layer_Len (P, J));
               pragma Assert (P.Layers (J).First + K - 1 = I);
               pragma Assert
                 (E.Terms (P.Layers (J).First + K - 1) = Term_At (P, J, K));
               pragma Assert (Term_At (P, J, K) = C.Terms (I));
            end;
            pragma Assert (E.Terms (I) = C.Terms (I));
         end loop;
      end loop;
      pragma Assert (for all I in 1 .. C.NT => E.Terms (I) = C.Terms (I));
      pragma Assert (E.Terms = C.Terms);
   end Lemma_Pack_Expand;

   function Pack (C : SA.Raw_Circuit) return Packed_Circuit is
      NK : Natural := 0;
   begin
      --  The layers are disjoint pairwise: a term written for layer J
      --  leaves the deltas of the layers before it as they are.
      Lemma_Layers_Ordered (C);
      --  The tokens: one per layer with a term.
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant (NK <= J);
         pragma Loop_Invariant (Proof_Only => NK = Tokens_Before (C, J));
         if C.Layers (J).Last >= C.Layers (J).First then
            NK := NK + 1;
         end if;
      end loop;
      pragma Assert (Proof_Only => NK = Tokens_Before (C, C.Last_Layer + 1));
      declare
         P : Packed_Circuit :=
           (Last_Layer => C.Last_Layer,
            NT         => C.NT,
            NC         => C.NT,
            ND         => C.NT,
            NS         => C.Last_Layer + 1,
            NE         => C.NT,
            NK         => NK,
            Noutput    => C.Noutput,
            Ninput     => C.Ninput,
            Npublic    => C.Npublic,
            Layers     => C.Layers,
            Spans      => [others => (First => 1, Last => 0)],
            Constants  => [others => SA.Zero],
            Deltas     => [others => (DG => 0, DH0 => 0, DH1 => 0, K => 1)],
            Seg_Start  => [others => 1],
            Seg_Len    => [others => 0],
            Entries    => [others => 1],
            Tokens     => [others => 1]);
         T : Natural := 0;   --  the tokens placed
      begin
         for J in 0 .. C.Last_Layer loop
            pragma Loop_Invariant (T <= NK);
            pragma Loop_Invariant (Proof_Only => T = Tokens_Before (C, J));
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all I in 1 .. Done (C, J) =>
                    P.Constants (I) = C.Terms (I).K
                    and then P.Entries (I) = I
                    and then P.Deltas (I).K = I));
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all J2 in 0 .. J - 1 =>
                    P.Seg_Start (J2 + 1) = C.Layers (J2).First
                    and then P.Seg_Len (J2 + 1)
                             = C.Layers (J2).Last + 1 - C.Layers (J2).First
                    and then (for all I in C.Layers (J2).First
                                          .. C.Layers (J2).Last =>
                                Delta_Ok (C, J2, I, P.Deltas (I)))
                    and then P.Spans (J2).First - 1
                             = (if J2 = 0 then 0 else P.Spans (J2 - 1).Last)
                    and then P.Spans (J2).Last
                             = P.Spans (J2).First - 1
                               + (if C.Layers (J2).Last
                                     >= C.Layers (J2).First
                                  then 1 else 0)
                    and then P.Spans (J2).Last <= T
                    and then (if C.Layers (J2).Last >= C.Layers (J2).First
                              then P.Spans (J2).First <= NK
                                   and then P.Tokens (P.Spans (J2).First)
                                            = J2 + 1)));
            pragma Loop_Invariant (if J > 0 then P.Spans (J - 1).Last = T);
            pragma Loop_Invariant
              (for all T2 in 1 .. T =>
                 P.Tokens (T2) in 1 .. J
                 and then P.Seg_Len (P.Tokens (T2)) >= 1);
            declare
               First : constant Positive := C.Layers (J).First;
               Last  : constant Natural := C.Layers (J).Last;
            begin
               P.Seg_Start (J + 1) := First;
               P.Seg_Len (J + 1) := Last + 1 - First;
               for I in First .. Last loop
                  pragma Loop_Invariant
                    (Proof_Only =>
                       (for all I2 in 1 .. Done (C, J) =>
                          P.Constants (I2) = C.Terms (I2).K
                          and then P.Entries (I2) = I2
                          and then P.Deltas (I2).K = I2));
                  pragma Loop_Invariant
                    (Proof_Only =>
                       (for all J2 in 0 .. J - 1 =>
                          (for all I2 in C.Layers (J2).First
                                         .. C.Layers (J2).Last =>
                             Delta_Ok (C, J2, I2, P.Deltas (I2)))));
                  pragma Loop_Invariant
                    (Proof_Only =>
                       (for all I2 in First .. I - 1 =>
                          P.Constants (I2) = C.Terms (I2).K
                          and then P.Entries (I2) = I2
                          and then Delta_Ok (C, J, I2, P.Deltas (I2))));
                  P.Constants (I) := C.Terms (I).K;
                  P.Entries (I) := I;
                  P.Deltas (I) :=
                    (DG  => Long_Long_Integer (C.Terms (I).G)
                            - (if I = First then 0
                               else Long_Long_Integer (C.Terms (I - 1).G)),
                     DH0 => Long_Long_Integer (C.Terms (I).H0)
                            - (if I = First then 0
                               else Long_Long_Integer (C.Terms (I - 1).H0)),
                     DH1 => Long_Long_Integer (C.Terms (I).H1)
                            - (if I = First then 0
                               else Long_Long_Integer (C.Terms (I - 1).H1)),
                     K   => I);
               end loop;
               Lemma_Tokens_Before_Mono (C, J + 1, C.Last_Layer + 1);
               if Last >= First then
                  pragma Assert
                    (Proof_Only => Tokens_Before (C, J + 1) = T + 1);
                  T := T + 1;
                  P.Tokens (T) := J + 1;
                  P.Spans (J) := (First => T, Last => T);
               else
                  pragma Assert (Proof_Only => Tokens_Before (C, J + 1) = T);
                  P.Spans (J) := (First => T + 1, Last => T);
               end if;
            end;
         end loop;
         pragma Assert (Proof_Only => T = NK);
         pragma Assert
           (Proof_Only =>
              (for all I in 1 .. C.NT =>
                 P.Constants (I) = C.Terms (I).K
                 and then P.Entries (I) = I
                 and then P.Deltas (I).K = I));
         pragma Assert
           (Proof_Only =>
              (for all J in 0 .. C.Last_Layer =>
                 P.Seg_Start (J + 1) = C.Layers (J).First
                 and then P.Seg_Len (J + 1)
                          = C.Layers (J).Last + 1 - C.Layers (J).First));
         pragma Assert
           (Proof_Only =>
              (for all J in 0 .. C.Last_Layer =>
                 (for all I in C.Layers (J).First .. C.Layers (J).Last =>
                    Delta_Ok (C, J, I, P.Deltas (I)))));
         pragma Assert
           (Proof_Only =>
              (for all J in 0 .. C.Last_Layer =>
                 P.Spans (J).First - 1
                 = (if J = 0 then 0 else P.Spans (J - 1).Last)
                 and then P.Spans (J).Last
                          = P.Spans (J).First - 1
                            + (if C.Layers (J).Last >= C.Layers (J).First
                               then 1 else 0)
                 and then P.Spans (J).Last <= NK
                 and then (if C.Layers (J).Last >= C.Layers (J).First
                           then P.Spans (J).First <= NK
                                and then P.Tokens (P.Spans (J).First)
                                         = J + 1)));
         pragma Assert (Proof_Only => P.Spans (C.Last_Layer).Last = NK);
         pragma Assert (Proof_Only => Packing (C, P));
         pragma Assert
           (Proof_Only =>
              (for all S in 1 .. P.NS =>
                 P.Seg_Start (S) <= P.NE + 1
                 and then P.Seg_Len (S) <= P.NE + 1 - P.Seg_Start (S)));
         pragma Assert
           (Proof_Only =>
              (for all T2 in 1 .. P.NK =>
                 P.Tokens (T2) <= P.NS
                 and then P.Seg_Len (P.Tokens (T2)) >= 1));
         pragma Assert (Proof_Only => Indices_Ok (P));
         pragma Assert (Proof_Only => Layers_Ok (P));
         Lemma_Pack_Counts (C, P);
         Lemma_Pack_Cursors (C, P);
         Lemma_Valid_Intro (P);
         Lemma_Pack_Terms (C, P);
         Lemma_Pack_Expand (C, P);
         return P;
      end;
   end Pack;

end Packed_Circuits;
