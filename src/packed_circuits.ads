--  Packed_Circuits: a circuit held as its LFC2 file holds it (the memory
--  milestone, ADR 0080). Per layer, the terms are not stored: the file
--  gives a dictionary of term deltas (dg, dh0, dh1, a constant), segments
--  (runs of dictionary entries) and a sequence of tokens (segments), and
--  the terms are the prefix sums of the deltas met in token order, from
--  zero at the start of each layer. On the mDoc hash circuit this form
--  takes 4.2 MB where the expanded terms take 236.7 MB (circuit_kat).
--
--  The model is the expanded circuit of Sumcheck_Algebra, Raw_Circuit:
--  Expand gives it, at level Proof_Only, from one recursive ghost
--  function, Cursor_At, the state of a walk of a layer after K terms.
--  A walk is executable: Start, then Step once per term, with Term_Of the
--  term a cursor produces. Every executable walk proves, at each step,
--  that its cursor is Cursor_At of its position, so what it reads is the
--  layer of Expand.
--
--  Two facts make Step a plain expression function. Tokens of an empty
--  segment produce no term and are not kept (the segment is, since the
--  tokens index the segments), so a token is never skipped. The running
--  sums are 64-bit integers: K steps of deltas below 2^27 stay below
--  2^56, so they cannot wrap; that every term's wires are in range is a
--  fact the reader checks and Valid states.
--
--  Indices_Ok is executable, and the reader checks it once. In the
--  preconditions of the walk it is at level Proof_Only: it reads every
--  delta, entry and token, and an assertion-enabled build that ran it at
--  every step would take time quadratic in the circuit. The provers still
--  require it at every call; the rest of each precondition still runs.
--
--  Proof status: Gold for the walk against Cursor_At (absence of
--  run-time errors and the Posts below). Nothing here relates the packed
--  form to the bytes of a file: as before, the expansion agrees with
--  upstream's by the vectors (ADR 0048).
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, circuits are
--  public data (ADR 0037).

pragma SPARK_Mode (On);

with Proof_Levels;
with Sumcheck_Algebra;

generic
   with package SA is new Sumcheck_Algebra (<>);
package Packed_Circuits is

   use type SA.Layer_Array;
   use type SA.Term;

   subtype Count is Natural range 0 .. SA.Max_Terms;

   --  A delta of the file: the zigzag range of Uleb128.
   subtype Delta_Value is Long_Long_Integer range -(2**27) .. 2**27 - 1;

   --  A running sum after at most Max_Terms deltas.
   Max_Run : constant := 2**56;
   subtype Run_Value is Long_Long_Integer range -Max_Run .. Max_Run;

   type Packed_Delta is record
      DG, DH0, DH1 : Delta_Value;
      K            : Positive;   --  the index of the constant
   end record;

   type Delta_Array is array (Positive range <>) of Packed_Delta;
   type Index_Array is array (Positive range <>) of Positive;
   type Length_Array is array (Positive range <>) of Natural;
   type Const_Array is array (Positive range <>) of SA.Element;

   --  The tokens of a layer: First .. Last, Last = First - 1 when none.
   type Tokens_Span is record
      First : Positive;
      Last  : Natural;
   end record;

   type Span_Array is array (Natural range <>) of Tokens_Span;

   --  Layers as in Raw_Circuit: Logw, NW_In and the term indices First
   --  .. Last of the expansion; Spans the tokens of each layer.
   type Packed_Circuit
     (Last_Layer : SA.Layer_Last;
      NT         : SA.Term_Count;
      NC         : Count;    --  constants
      ND         : Count;    --  deltas
      NS         : Count;    --  segments
      NE         : Count;    --  segment entries
      NK         : Count)    --  tokens
   is record
      Noutput   : SA.Wire_Count;
      Ninput    : SA.Wire_Count;
      Npublic   : SA.Wire_Count;
      Layers    : SA.Layer_Array (0 .. Last_Layer);
      Spans     : Span_Array (0 .. Last_Layer);
      Constants : Const_Array (1 .. NC);
      Deltas    : Delta_Array (1 .. ND);
      Seg_Start : Index_Array (1 .. NS);
      Seg_Len   : Length_Array (1 .. NS);
      Entries   : Index_Array (1 .. NE);
      Tokens    : Index_Array (1 .. NK);
   end record;

   -------------------------------------------------------------------
   --  The structure
   -------------------------------------------------------------------

   --  Every index points inside its array, and the spans partition the
   --  tokens in layer order.
   function Indices_Ok (P : Packed_Circuit) return Boolean is
     ((for all I in 1 .. P.ND => P.Deltas (I).K <= P.NC)
      and then (for all S in 1 .. P.NS =>
                  P.Seg_Start (S) <= P.NE + 1
                  and then P.Seg_Len (S) <= P.NE + 1 - P.Seg_Start (S))
      and then (for all E in 1 .. P.NE => P.Entries (E) <= P.ND)
      and then (for all T in 1 .. P.NK =>
                  P.Tokens (T) <= P.NS
                  and then P.Seg_Len (P.Tokens (T)) >= 1)
      and then P.Spans (0).First = 1
      and then P.Spans (P.Last_Layer).Last = P.NK
      and then (for all J in 0 .. P.Last_Layer =>
                  P.Spans (J).Last <= P.NK
                  and then P.Spans (J).Last + 1 >= P.Spans (J).First)
      and then (for all J in 1 .. P.Last_Layer =>
                  P.Spans (J).First = P.Spans (J - 1).Last + 1))
   with Global => null;

   --  The layers' term indices are consecutive ranges, possibly empty,
   --  from 1, in layer order, inside 1 .. NT.
   function Layers_Ok (P : Packed_Circuit) return Boolean is
     (P.Layers (0).First = 1
      and then (for all J in 0 .. P.Last_Layer =>
                  P.Layers (J).Last <= P.NT
                  and then P.Layers (J).Last + 1 >= P.Layers (J).First)
      and then (for all J in 1 .. P.Last_Layer =>
                  P.Layers (J).First = P.Layers (J - 1).Last + 1)
      and then (for all J1 in 0 .. P.Last_Layer =>
                  (for all J2 in J1 + 1 .. P.Last_Layer =>
                     P.Layers (J1).Last < P.Layers (J2).First)))
   with Global => null;

   --  The number of terms tokens F .. L produce.
   function Tok_Sum
     (P : Packed_Circuit; F, L : Natural) return Long_Long_Integer
   is
     (if L < F then 0
      else Tok_Sum (P, F, L - 1)
           + Long_Long_Integer (P.Seg_Len (P.Tokens (L))))
   with Ghost => Proof_Only,
        Global => null,
        Pre    => Indices_Ok (P) and then F >= 1
                  and then (L < F or else L <= P.NK),
        Post   => Tok_Sum'Result >= 0
                  and then Tok_Sum'Result
                           <= Long_Long_Integer (Natural'Max (0, L + 1 - F))
                              * Long_Long_Integer (SA.Max_Terms),
        Subprogram_Variant => (Decreases => L);

   --  The term count of each layer is what its tokens produce.
   function Counts_Ok (P : Packed_Circuit) return Boolean is
     (for all J in 0 .. P.Last_Layer =>
        Long_Long_Integer (P.Layers (J).Last + 1 - P.Layers (J).First)
        = Tok_Sum (P, P.Spans (J).First, P.Spans (J).Last))
   with Ghost => Proof_Only,
        Global => null,
        Pre    => Indices_Ok (P) and then Layers_Ok (P);

   --  The term count of layer J.
   function Layer_Len (P : Packed_Circuit; J : Natural) return Natural is
     (P.Layers (J).Last + 1 - P.Layers (J).First)
   with Global => null,
        Pre    => J <= P.Last_Layer
                  and then P.Layers (J).Last + 1 >= P.Layers (J).First;

   -------------------------------------------------------------------
   --  The walk
   -------------------------------------------------------------------

   --  A position in a layer: the token, the offset in its segment, and
   --  the running sums before the delta at that position.
   type Cursor is record
      Tok        : Positive;
      Off        : Natural;
      G, H0, H1  : Run_Value;
   end record;

   function Start (P : Packed_Circuit; J : Natural) return Cursor is
     ((Tok => P.Spans (J).First, Off => 0, G => 0, H0 => 0, H1 => 0))
   with Global => null, Pre => J <= P.Last_Layer;

   --  The cursor is on a delta of its token's segment.
   function On_Delta (P : Packed_Circuit; C : Cursor) return Boolean is
     (C.Tok <= P.NK and then C.Off < P.Seg_Len (P.Tokens (C.Tok)))
   with Global => null,
        Pre    => (Proof_Only => Indices_Ok (P));

   --  The delta at the cursor.
   function Delta_At (P : Packed_Circuit; C : Cursor) return Packed_Delta is
     (P.Deltas (P.Entries (P.Seg_Start (P.Tokens (C.Tok)) + C.Off)))
   with Global => null,
        Pre    => (Proof_Only => Indices_Ok (P),
                   Runtime    => On_Delta (P, C));

   --  The cursor after one term.
   function Step (P : Packed_Circuit; C : Cursor) return Cursor is
     ((Tok => (if C.Off + 1 < P.Seg_Len (P.Tokens (C.Tok)) then C.Tok
               else C.Tok + 1),
       Off => (if C.Off + 1 < P.Seg_Len (P.Tokens (C.Tok)) then C.Off + 1
               else 0),
       G   => C.G + Delta_At (P, C).DG,
       H0  => C.H0 + Delta_At (P, C).DH0,
       H1  => C.H1 + Delta_At (P, C).DH1))
   with Global => null,
        Pre    => (Proof_Only => Indices_Ok (P),
                   Runtime    => On_Delta (P, C)
                                 and then abs C.G <= Max_Run - 2**27
                                 and then abs C.H0 <= Max_Run - 2**27
                                 and then abs C.H1 <= Max_Run - 2**27);

   --  The cursor of layer J after K terms. Recursive, hence hidden (see
   --  Bytes.Add_Zeros): its Post is what callers see, and Lemma_Step
   --  gives one step of its body.
   function Cursor_At
     (P : Packed_Circuit; J : Natural; K : Natural) return Cursor
   is
     (if K = 0 then Start (P, J) else Step (P, Cursor_At (P, J, K - 1)))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre    => Indices_Ok (P) and then Layers_Ok (P)
                  and then Counts_Ok (P) and then J <= P.Last_Layer
                  and then K <= Layer_Len (P, J),
        Post   =>
          Cursor_At'Result.Tok in P.Spans (J).First .. P.Spans (J).Last + 1
          and then Tok_Sum (P, P.Spans (J).First, Cursor_At'Result.Tok - 1)
                   + Long_Long_Integer (Cursor_At'Result.Off)
                   = Long_Long_Integer (K)
          and then (if Cursor_At'Result.Tok <= P.Spans (J).Last then
                      Cursor_At'Result.Off
                        < P.Seg_Len (P.Tokens (Cursor_At'Result.Tok))
                    else Cursor_At'Result.Off = 0)
          and then abs Cursor_At'Result.G <= Long_Long_Integer (K) * 2**27
          and then abs Cursor_At'Result.H0 <= Long_Long_Integer (K) * 2**27
          and then abs Cursor_At'Result.H1 <= Long_Long_Integer (K) * 2**27,
        Subprogram_Variant => (Decreases => K);

   --  One step of the walk: the cursor after K - 1 terms is on a delta,
   --  and Step takes it to the cursor after K.
   procedure Lemma_Step (P : Packed_Circuit; J, K : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Indices_Ok (P) and then Layers_Ok (P) and then Counts_Ok (P)
               and then J <= P.Last_Layer
               and then K in 1 .. Layer_Len (P, J),
     Post   => On_Delta (P, Cursor_At (P, J, K - 1))
               and then abs Cursor_At (P, J, K - 1).G <= Max_Run - 2**27
               and then abs Cursor_At (P, J, K - 1).H0 <= Max_Run - 2**27
               and then abs Cursor_At (P, J, K - 1).H1 <= Max_Run - 2**27
               and then Step (P, Cursor_At (P, J, K - 1))
                          = Cursor_At (P, J, K);

   --  Every term of every layer names wires in range: the fact the
   --  reader checks as it walks.
   function Wires_Ok (P : Packed_Circuit) return Boolean is
     (for all J in 0 .. P.Last_Layer =>
        (for all K in 1 .. Layer_Len (P, J) =>
           Cursor_At (P, J, K).G in 0 .. SA.Max_Wires - 1
           and then Cursor_At (P, J, K).H0 in 0 .. SA.Max_Wires - 1
           and then Cursor_At (P, J, K).H1 in 0 .. SA.Max_Wires - 1))
   with Ghost => Proof_Only,
        Global => null,
        Pre    => Indices_Ok (P) and then Layers_Ok (P)
                  and then Counts_Ok (P);

   --  The packed circuit is one the reader accepts. Hidden: behind it
   --  are Tok_Sum and Cursor_At, both recursive, and a caller that sees
   --  them unfolds them without bound. Lemma_Valid gives the two parts an
   --  executable walk needs, Lemma_Valid_Intro builds it.
   function Valid (P : Packed_Circuit) return Boolean is
     (Indices_Ok (P) and then Layers_Ok (P) and then Counts_Ok (P)
      and then Wires_Ok (P))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   procedure Lemma_Valid (P : Packed_Circuit) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Valid (P),
     Post   => Indices_Ok (P) and then Layers_Ok (P);

   procedure Lemma_Valid_Intro (P : Packed_Circuit) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Indices_Ok (P) and then Layers_Ok (P) and then Counts_Ok (P)
               and then Wires_Ok (P),
     Post   => Valid (P);

   --  The term a cursor on a delta produces, its wires in range.
   function Term_Of (P : Packed_Circuit; C : Cursor) return SA.Term is
     ((K  => P.Constants (Delta_At (P, C).K),
       G  => Natural (C.G + Delta_At (P, C).DG),
       H0 => Natural (C.H0 + Delta_At (P, C).DH0),
       H1 => Natural (C.H1 + Delta_At (P, C).DH1)))
   with Global => null,
        Pre    => (Proof_Only => Indices_Ok (P),
                   Runtime    =>
                     On_Delta (P, C)
                     and then C.G + Delta_At (P, C).DG
                                in 0 .. SA.Max_Wires - 1
                     and then C.H0 + Delta_At (P, C).DH0
                                in 0 .. SA.Max_Wires - 1
                     and then C.H1 + Delta_At (P, C).DH1
                                in 0 .. SA.Max_Wires - 1);

   --  Term K of layer J, K from 1: the constant of the delta at the
   --  cursor after K - 1 terms, the wires of the cursor after K. The body
   --  states the parts of Valid it reads, since Valid is hidden; on a
   --  valid circuit it is the term (Lemma_Term_Of).
   function Term_At (P : Packed_Circuit; J, K : Natural) return SA.Term is
     (if Indices_Ok (P) and then Layers_Ok (P) and then Counts_Ok (P)
        and then Wires_Ok (P) and then K in 1 .. Layer_Len (P, J)
      then
        (K  => P.Constants (Delta_At (P, Cursor_At (P, J, K - 1)).K),
         G  => Natural (Cursor_At (P, J, K).G),
         H0 => Natural (Cursor_At (P, J, K).H0),
         H1 => Natural (Cursor_At (P, J, K).H1))
      else (K => SA.Zero, G => 0, H0 => 0, H1 => 0))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre    => J <= P.Last_Layer;

   --  The term a walk produces is the layer's: the cursor after K - 1
   --  terms gives Term_At (P, J, K), and one Step gives the cursor after
   --  K.
   procedure Lemma_Term_Of (P : Packed_Circuit; J, K : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Valid (P) and then Indices_Ok (P) and then Layers_Ok (P)
               and then J <= P.Last_Layer
               and then K in 1 .. Layer_Len (P, J),
     Post   => On_Delta (P, Cursor_At (P, J, K - 1))
               and then abs Cursor_At (P, J, K - 1).G <= Max_Run - 2**27
               and then abs Cursor_At (P, J, K - 1).H0 <= Max_Run - 2**27
               and then abs Cursor_At (P, J, K - 1).H1 <= Max_Run - 2**27
               and then Step (P, Cursor_At (P, J, K - 1)) = Cursor_At (P, J, K)
               and then Cursor_At (P, J, K - 1).G
                          + Delta_At (P, Cursor_At (P, J, K - 1)).DG
                        in 0 .. SA.Max_Wires - 1
               and then Cursor_At (P, J, K - 1).H0
                          + Delta_At (P, Cursor_At (P, J, K - 1)).DH0
                        in 0 .. SA.Max_Wires - 1
               and then Cursor_At (P, J, K - 1).H1
                          + Delta_At (P, Cursor_At (P, J, K - 1)).DH1
                        in 0 .. SA.Max_Wires - 1
               and then Term_Of (P, Cursor_At (P, J, K - 1))
                        = Term_At (P, J, K);

   --  The model: the circuit with the layers of P and, at the term
   --  indices of each layer, the terms of its walk.
   function Expand (P : Packed_Circuit) return SA.Raw_Circuit
   with Ghost => Proof_Only,
        Global => null,
        Pre    => Valid (P),
        Post   =>
          Expand'Result.Last_Layer = P.Last_Layer
          and then Expand'Result.NT = P.NT
          and then Expand'Result.Noutput = P.Noutput
          and then Expand'Result.Ninput = P.Ninput
          and then Expand'Result.Npublic = P.Npublic
          and then Expand'Result.Layers = P.Layers
          and then
          (for all J in 0 .. P.Last_Layer =>
             (for all K in 1 .. Layer_Len (P, J) =>
                Expand'Result.Terms (P.Layers (J).First + K - 1)
                = Term_At (P, J, K)));

   --  C is the cursor of layer J after K terms. Hidden, so that a loop
   --  that walks a layer carries no instance of Cursor_At and of the
   --  sums behind it; the two lemmas below are all a walk needs. The
   --  body states the parts of Valid that Cursor_At needs.
   function Walked
     (P : Packed_Circuit; J, K : Natural; C : Cursor) return Boolean
   is
     (Indices_Ok (P) and then Layers_Ok (P) and then Counts_Ok (P)
      and then K <= Layer_Len (P, J) and then C = Cursor_At (P, J, K))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre    => J <= P.Last_Layer;

   procedure Lemma_Walked_Start (P : Packed_Circuit; J : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Valid (P) and then J <= P.Last_Layer,
     Post   => Walked (P, J, 0, Start (P, J));

   --  One step of a walk on the expansion: the cursor after K - 1 terms
   --  produces term K of layer J of Expand (P), and steps to the cursor
   --  after K.
   procedure Lemma_Walked_Step
     (P : Packed_Circuit; J, K : Natural; C : Cursor)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Valid (P) and then Indices_Ok (P) and then Layers_Ok (P)
               and then J <= P.Last_Layer
               and then K in 1 .. Layer_Len (P, J)
               and then Walked (P, J, K - 1, C),
     Post   => On_Delta (P, C)
               and then abs C.G <= Max_Run - 2**27
               and then abs C.H0 <= Max_Run - 2**27
               and then abs C.H1 <= Max_Run - 2**27
               and then Walked (P, J, K, Step (P, C))
               and then C.G + Delta_At (P, C).DG in 0 .. SA.Max_Wires - 1
               and then C.H0 + Delta_At (P, C).DH0 in 0 .. SA.Max_Wires - 1
               and then C.H1 + Delta_At (P, C).DH1 in 0 .. SA.Max_Wires - 1
               and then P.Layers (J).First + K - 1 in 1 .. P.NT
               and then Term_Of (P, C)
                        = Expand (P).Terms (P.Layers (J).First + K - 1);

end Packed_Circuits;
