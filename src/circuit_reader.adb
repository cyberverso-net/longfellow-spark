pragma SPARK_Mode (On);

with Interfaces; use Interfaces;
with Ada.Unchecked_Deallocation;
with Sha256;
with Uleb128;

package body Circuit_Reader is

   Size : constant Positive := SA.F.Serialized_Size;

   -------------------------------------------------------------------
   --  Temporaries of the walk, on the heap (ADR 0047), each sized by
   --  a count the file declares after the check that the count fits
   --  the bytes that remain.
   -------------------------------------------------------------------

   type Const_Array is array (Positive range <>) of SA.Element;
   type Const_Access is access Const_Array;

   --  A step (a delta of the file): the signed differences, in the
   --  range Zigzag gives, and the constant's index (1-based into the
   --  table).
   subtype Signed_Delta is Integer range -(2**27) .. 2**27 - 1;
   type Step is record
      G, H0, H1 : Signed_Delta;
      K         : Positive;
   end record;
   type Step_Array is array (Positive range <>) of Step;
   type Step_Access is access Step_Array;

   --  A segment: where its delta indices start in the file, how many.
   type Segment is record
      Pos, Len : Natural;
   end record;
   type Segment_Array is array (Positive range <>) of Segment;
   type Segment_Access is access Segment_Array;

   procedure Free_Consts is
     new Ada.Unchecked_Deallocation (Const_Array, Const_Access);
   procedure Free_Deltas is
     new Ada.Unchecked_Deallocation (Step_Array, Step_Access);
   procedure Free_Segments is
     new Ada.Unchecked_Deallocation (Segment_Array, Segment_Access);
   procedure Free_Circuit is
     new Ada.Unchecked_Deallocation (Raw_Circuit, Circuit_Access);

   --  Per wire of a layer, the index of its assertion, or 0.
   type Marks is array (Natural range <>) of Natural;
   type Marks_Access is access Marks;

   procedure Free_Marks is
     new Ada.Unchecked_Deallocation (Marks, Marks_Access);

   procedure Free (C : in out Circuit_Access) is
   begin
      Free_Circuit (C);
   end Free;

   -------------------------------------------------------------------
   --  Integers
   -------------------------------------------------------------------

   --  Eight little-endian bytes of N (u64 in the reference).
   function LE64 (N : Natural) return Bytes_8 is
     ([Unsigned_8 (N mod 256),
       Unsigned_8 (N / 2**8 mod 256),
       Unsigned_8 (N / 2**16 mod 256),
       Unsigned_8 (N / 2**24 mod 256),
       0, 0, 0, 0])
   with Global => null;

   function Ceil_Lg2 (N : Natural) return Natural is
      P : Natural := 1;
   begin
      if N <= 1 then
         return 0;
      end if;
      for K in 0 .. 24 loop
         if P >= N then
            return K;
         end if;
         pragma Assert (P < N);
         P := 2 * P;
      end loop;
      return 24;
   end Ceil_Lg2;

   --  One ULEB128 integer at Pos: Ok with Pos advanced, or the status
   --  of the failure with Pos unchanged.
   procedure Read_Nat
     (B   : Byte_Array;
      Pos : in out Natural;
      V   : out Natural;
      St  : out Status)
   with
     Global => null,
     Pre    => B'First = 0 and then Pos <= B'Length,
     Post   =>
       (if St = Ok then
          Pos > Pos'Old and then Pos <= B'Length
          and then V <= Uleb128.Max_Value
        else Pos = Pos'Old and then V = 0);

   procedure Read_Nat
     (B   : Byte_Array;
      Pos : in out Natural;
      V   : out Natural;
      St  : out Status)
   is
      Val  : Uleb128.Value;
      Good : Boolean;
      Long : Boolean;
   begin
      Uleb128.Read (B, Pos, Val, Good, Long);
      V := Val;
      if Good then
         St := Ok;
      elsif Long then
         St := Bad_Integer;
      else
         St := Truncated;
      end if;
   end Read_Nat;

   --  One element of Section 7.2.1 at Pos.
   procedure Read_Element
     (B   : Byte_Array;
      Pos : in out Natural;
      E   : out SA.Element;
      St  : out Status)
   with
     Global => null,
     Pre    => B'First = 0 and then Pos <= B'Length,
     Post   =>
       (if St = Ok then Pos = Pos'Old + Size and then Pos <= B'Length
        else Pos = Pos'Old);

   procedure Read_Element
     (B   : Byte_Array;
      Pos : in out Natural;
      E   : out SA.Element;
      St  : out Status)
   is
      Good : Boolean;
   begin
      E := SA.Zero;
      if B'Length - Pos < Size then
         St := Truncated;
         return;
      end if;
      SA.F.From_Bytes (B (Pos .. Pos + Size - 1), E, Good);
      if not Good then
         E  := SA.Zero;
         St := Bad_Element;
         return;
      end if;
      Pos := Pos + Size;
      St  := Ok;
   end Read_Element;

   -------------------------------------------------------------------
   --  The identifier
   -------------------------------------------------------------------

   function Compute_Id
     (C : Raw_Circuit; Subfield_Boundary : Natural) return Bytes_32
   is
      Ctx : Sha256.Context := Sha256.Initial;
      --  The field tag: 2 and the bit width for a binary field, 1 and
      --  the encoding of -1 for a prime field.
      Tag  : constant Bytes_8 := LE64 (if Is_Binary then 2 else 1);
      Mone : constant Byte_Array := SA.F.To_Bytes (SA.F.Neg (SA.F.One));
   begin
      Sha256.Update (Ctx, Tag);
      Sha256.Update (Ctx, (if Is_Binary then LE64 (8 * Size) else Mone));
      Sha256.Update (Ctx, LE64 (C.Noutput));
      Sha256.Update (Ctx, LE64 (Ceil_Lg2 (C.Noutput)));
      Sha256.Update (Ctx, LE64 (1));   --  ncopies
      Sha256.Update (Ctx, LE64 (0));   --  logc
      Sha256.Update (Ctx, LE64 (C.Last_Layer + 1));
      Sha256.Update (Ctx, LE64 (C.Ninput));
      Sha256.Update (Ctx, LE64 (C.Npublic));
      Sha256.Update (Ctx, LE64 (Subfield_Boundary));
      for J in 0 .. C.Last_Layer loop
         Sha256.Update (Ctx, LE64 (C.Layers (J).NW_In));
         Sha256.Update (Ctx, LE64 (C.Layers (J).Logw));
         Sha256.Update
           (Ctx, LE64 (C.Layers (J).Last + 1 - C.Layers (J).First));
         for I in C.Layers (J).First .. C.Layers (J).Last loop
            Sha256.Update (Ctx, LE64 (C.Terms (I).G));
            Sha256.Update (Ctx, LE64 (C.Terms (I).H0));
            Sha256.Update (Ctx, LE64 (C.Terms (I).H1));
            Sha256.Update (Ctx, SA.F.To_Bytes (C.Terms (I).K));
         end loop;
      end loop;
      return Sha256.Digest (Ctx);
   end Compute_Id;

   -------------------------------------------------------------------
   --  The walk: validate and count (C null), or fill (C allocated
   --  with the counts of the first walk; every index into it is
   --  guarded, so the second walk needs nothing of the first).
   -------------------------------------------------------------------

   No_Consts : constant Const_Array (1 .. 0) := [others => SA.Zero];

   type Counts is record
      NL, NT, Noutput, Ninput, Npublic, Nconst, Sfb : Natural;
      Id_Pos : Natural;
   end record;

   Zero_Counts : constant Counts := (others => 0);

   --  One layer: logw, nw, the deltas, the segments, the tokens. LT is
   --  the layer's term count; Base the terms before it. When C is not
   --  null the layer and its terms are written at Base + 1 onwards.
   procedure Read_Layer
     (B      : Byte_Array;
      Pos    : in out Natural;
      C      : Circuit_Access;
      K      : Const_Array;
      Nconst : Natural;
      J      : Natural;
      Base   : Natural;
      LT     : out Natural;
      St     : out Status)
   with
     Global => null,
     Pre    => B'First = 0 and then Pos <= B'Length
               and then Base <= SA.Max_Terms,
     Post   =>
       (if St = Ok then
          Pos <= B'Length and then LT <= SA.Max_Terms - Base);

   procedure Read_Layer
     (B      : Byte_Array;
      Pos    : in out Natural;
      C      : Circuit_Access;
      K      : Const_Array;
      Nconst : Natural;
      J      : Natural;
      Base   : Natural;
      LT     : out Natural;
      St     : out Status)
   is
      Logw, NW, ND, NS, NTok, V, Len, Tok, Idx : Natural;
      DG, DH0, DH1 : Natural;
      G, H0, H1 : Integer := 0;
      D  : Step_Access := null;
      S  : Segment_Access := null;
      P2, Val : Natural;
   begin
      LT := 0;
      Read_Nat (B, Pos, Logw, St);
      if St /= Ok then
         return;
      end if;
      if Logw > SA.Max_Logw then
         St := Bound_Exceeded;
         return;
      end if;
      Read_Nat (B, Pos, NW, St);
      if St /= Ok then
         return;
      end if;
      if NW > SA.Max_Wires then
         St := Bound_Exceeded;
         return;
      end if;

      --  Deltas: four integers each, so at least four bytes.
      Read_Nat (B, Pos, ND, St);
      if St /= Ok then
         return;
      end if;
      if ND > (B'Length - Pos) / 4 then
         St := Truncated;
         return;
      end if;
      if C /= null then
         D := new Step_Array'(1 .. ND => (G => 0, H0 => 0, H1 => 0, K => 1));
      end if;
      for I in 1 .. ND loop
         pragma Loop_Invariant (Pos <= B'Length);
         pragma Loop_Invariant ((D /= null) = (C /= null));
         pragma Loop_Invariant (D = null or else D'Length = ND);
         Read_Nat (B, Pos, DG, St);
         if St /= Ok then
            Free_Deltas (D);
            Free_Segments (S);
            return;
         end if;
         Read_Nat (B, Pos, DH0, St);
         if St /= Ok then
            Free_Deltas (D);
            Free_Segments (S);
            return;
         end if;
         Read_Nat (B, Pos, DH1, St);
         if St /= Ok then
            Free_Deltas (D);
            Free_Segments (S);
            return;
         end if;
         Read_Nat (B, Pos, V, St);
         if St /= Ok then
            Free_Deltas (D);
            Free_Segments (S);
            return;
         end if;
         if V >= Nconst then
            St := Bad_Index;
            Free_Deltas (D);
            Free_Segments (S);
            return;
         end if;
         if D /= null then
            D (I) := (G  => Uleb128.Zigzag (DG),
                      H0 => Uleb128.Zigzag (DH0),
                      H1 => Uleb128.Zigzag (DH1),
                      K  => V + 1);
         end if;
      end loop;

      --  Segments: a length then the delta indices, so at least one
      --  byte each.
      Read_Nat (B, Pos, NS, St);
      if St /= Ok then
         Free_Deltas (D);
         Free_Segments (S);
         return;
      end if;
      if NS > B'Length - Pos then
         St := Truncated;
         Free_Deltas (D);
         Free_Segments (S);
         return;
      end if;
      S := new Segment_Array'(1 .. NS => (Pos => 0, Len => 0));
      for I in 1 .. NS loop
         pragma Loop_Invariant (Pos <= B'Length);
         pragma Loop_Invariant ((D /= null) = (C /= null));
         pragma Loop_Invariant (D = null or else D'Length = ND);
         pragma Loop_Invariant (S /= null and then S'Length = NS);
         pragma Loop_Invariant
           (for all X in 1 .. I - 1 =>
              S (X).Pos <= B'Length and then S (X).Len <= B'Length);
         Read_Nat (B, Pos, Len, St);
         if St /= Ok then
            Free_Deltas (D);
            Free_Segments (S);
            return;
         end if;
         if Len > B'Length - Pos then
            St := Truncated;
            Free_Deltas (D);
            Free_Segments (S);
            return;
         end if;
         S (I) := (Pos => Pos, Len => Len);
         for X in 1 .. Len loop
            pragma Loop_Invariant (Pos <= B'Length);
            Read_Nat (B, Pos, V, St);
            if St /= Ok then
               Free_Deltas (D);
               Free_Segments (S);
               return;
            end if;
            if V >= ND then
               St := Bad_Index;
               Free_Deltas (D);
               Free_Segments (S);
               return;
            end if;
         end loop;
      end loop;

      --  Tokens: each names a segment; the terms are the expansion.
      Read_Nat (B, Pos, NTok, St);
      if St /= Ok then
         Free_Deltas (D);
         Free_Segments (S);
         return;
      end if;
      for T in 1 .. NTok loop
         pragma Loop_Invariant (Pos <= B'Length);
         pragma Loop_Invariant ((D /= null) = (C /= null));
         pragma Loop_Invariant (D = null or else D'Length = ND);
         pragma Loop_Invariant (S /= null and then S'Length = NS);
         pragma Loop_Invariant
           (for all X in 1 .. NS =>
              S (X).Pos <= B'Length and then S (X).Len <= B'Length);
         pragma Loop_Invariant (LT <= SA.Max_Terms - Base);
         pragma Loop_Invariant (G in 0 .. SA.Max_Wires - 1);
         pragma Loop_Invariant (H0 in 0 .. SA.Max_Wires - 1);
         pragma Loop_Invariant (H1 in 0 .. SA.Max_Wires - 1);
         Read_Nat (B, Pos, Tok, St);
         if St /= Ok then
            Free_Deltas (D);
            Free_Segments (S);
            return;
         end if;
         if Tok >= NS then
            St := Bad_Index;
            Free_Deltas (D);
            Free_Segments (S);
            return;
         end if;
         Len := S (Tok + 1).Len;
         if Len > SA.Max_Terms - Base - LT then
            St := Bound_Exceeded;
            Free_Deltas (D);
            Free_Segments (S);
            return;
         end if;
         if C /= null then
            P2 := S (Tok + 1).Pos;
            for X in 1 .. Len loop
               pragma Loop_Invariant (P2 <= B'Length);
               pragma Loop_Invariant (G in 0 .. SA.Max_Wires - 1);
               pragma Loop_Invariant (H0 in 0 .. SA.Max_Wires - 1);
               pragma Loop_Invariant (H1 in 0 .. SA.Max_Wires - 1);
               Read_Nat (B, P2, Val, St);
               if St /= Ok or else Val >= ND or else D = null then
                  St := Bad_Index;
                  Free_Deltas (D);
                  Free_Segments (S);
                  return;
               end if;
               declare
                  Dl : constant Step := D (Val + 1);
               begin
                  if G + Dl.G not in 0 .. SA.Max_Wires - 1
                    or else H0 + Dl.H0 not in 0 .. SA.Max_Wires - 1
                    or else H1 + Dl.H1 not in 0 .. SA.Max_Wires - 1
                    or else Dl.K not in K'Range
                  then
                     St := Bad_Index;
                     Free_Deltas (D);
                     Free_Segments (S);
                     return;
                  end if;
                  G  := G + Dl.G;
                  H0 := H0 + Dl.H0;
                  H1 := H1 + Dl.H1;
                  Idx := Base + LT + X;
                  if Idx > C.NT then
                     St := Bad_Index;
                     Free_Deltas (D);
                     Free_Segments (S);
                     return;
                  end if;
                  C.Terms (Idx) := (K => K (Dl.K), G => G, H0 => H0, H1 => H1);
               end;
            end loop;
         end if;
         LT := LT + Len;
      end loop;

      if C /= null then
         if J > C.Last_Layer or else Base + LT > C.NT then
            St := Bad_Index;
            Free_Deltas (D);
            Free_Segments (S);
            return;
         end if;
         C.Layers (J) := (Logw  => Logw,
                          NW_In => NW,
                          First => Base + 1,
                          Last  => Base + LT);
      end if;
      Free_Deltas (D);
      Free_Segments (S);
      St := Ok;
   end Read_Layer;

   procedure Walk
     (B   : Byte_Array;
      C   : Circuit_Access;
      Cnt : out Counts;
      St  : out Status)
   with
     Global => null,
     Pre    => B'First = 0,
     Post   =>
       (if St = Ok then
          Cnt.NL in 1 .. SA.Max_Layers
          and then Cnt.NT <= SA.Max_Terms
          and then Cnt.Noutput <= SA.Max_Wires
          and then Cnt.Ninput <= SA.Max_Wires
          and then Cnt.Npublic <= SA.Max_Wires
          and then Cnt.Id_Pos + 32 = B'Length);

   procedure Walk
     (B   : Byte_Array;
      C   : Circuit_Access;
      Cnt : out Counts;
      St  : out Status)
   is
      Pos : Natural;
      V, Fid, LT : Natural;
      K : Const_Access := null;
      E : SA.Element;
   begin
      Cnt := Zero_Counts;
      if B'Length < 4 then
         St := Truncated;
         return;
      end if;
      if B (0) /= Character'Pos ('L')
        or else B (1) /= Character'Pos ('F')
        or else B (2) /= Character'Pos ('C')
        or else B (3) /= Character'Pos ('2')
      then
         St := Bad_Magic;
         return;
      end if;
      Pos := 4;

      --  The header, checked in the order of the production reader.
      Read_Nat (B, Pos, Fid, St);
      if St /= Ok then
         return;
      end if;
      Read_Nat (B, Pos, Cnt.Noutput, St);
      if St /= Ok then
         return;
      end if;
      if Cnt.Noutput > SA.Max_Wires then
         St := Bound_Exceeded;
         return;
      end if;
      Read_Nat (B, Pos, V, St);
      if St /= Ok then
         return;
      end if;
      if V /= 1 then
         St := Unsupported_Copies;
         return;
      end if;
      Read_Nat (B, Pos, Cnt.Npublic, St);
      if St /= Ok then
         return;
      end if;
      if Cnt.Npublic > SA.Max_Wires then
         St := Bound_Exceeded;
         return;
      end if;
      Read_Nat (B, Pos, Cnt.Sfb, St);
      if St /= Ok then
         return;
      end if;
      Read_Nat (B, Pos, Cnt.Ninput, St);
      if St /= Ok then
         return;
      end if;
      if Cnt.Ninput > SA.Max_Wires then
         St := Bound_Exceeded;
         return;
      end if;
      Read_Nat (B, Pos, Cnt.NL, St);
      if St /= Ok then
         return;
      end if;
      if Cnt.NL not in 1 .. SA.Max_Layers then
         St := Bound_Exceeded;
         return;
      end if;
      if Fid /= Field_Id then
         St := Field_Mismatch;
         return;
      end if;

      --  The constants.
      Read_Nat (B, Pos, Cnt.Nconst, St);
      if St /= Ok then
         return;
      end if;
      if Cnt.Nconst > (B'Length - Pos) / Size then
         St := Truncated;
         return;
      end if;
      if C /= null then
         K := new Const_Array'(1 .. Cnt.Nconst => SA.Zero);
      end if;
      for I in 1 .. Cnt.Nconst loop
         pragma Loop_Invariant (Pos <= B'Length);
         pragma Loop_Invariant ((K /= null) = (C /= null));
         pragma Loop_Invariant (K = null or else K'Length = Cnt.Nconst);
         Read_Element (B, Pos, E, St);
         if St /= Ok then
            Free_Consts (K);
            return;
         end if;
         if K /= null then
            K (I) := E;
         end if;
      end loop;

      --  The layers.
      Cnt.NT := 0;
      for J in 0 .. Cnt.NL - 1 loop
         pragma Loop_Invariant (Pos <= B'Length);
         pragma Loop_Invariant (Cnt.NT <= SA.Max_Terms);
         pragma Loop_Invariant ((K /= null) = (C /= null));
         pragma Loop_Invariant (K = null or else K'Length = Cnt.Nconst);
         if K = null then
            Read_Layer (B, Pos, C, No_Consts, Cnt.Nconst, J, Cnt.NT, LT, St);
         else
            Read_Layer (B, Pos, C, K.all, Cnt.Nconst, J, Cnt.NT, LT, St);
         end if;
         if St /= Ok then
            Free_Consts (K);
            return;
         end if;
         Cnt.NT := Cnt.NT + LT;
      end loop;
      Free_Consts (K);

      --  The identifier, and nothing after it.
      if B'Length - Pos < 32 then
         St := Truncated;
         return;
      end if;
      Cnt.Id_Pos := Pos;
      Pos := Pos + 32;
      if Pos /= B'Length then
         St := Trailing_Bytes;
         return;
      end if;
      St := Ok;
   end Walk;

   -------------------------------------------------------------------
   --  The circuit premises (ADR 0064)
   -------------------------------------------------------------------

   --  Layer J: Ok when every assertion of the layer is alone on its
   --  wire; then M (W) is the assertion of wire W, or 0.
   procedure Mark_Layer
     (C : Raw_Circuit; J : Natural; M : in out Marks; Ok : out Boolean)
   with
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then M'First = 0 and then M'Last >= SA.NW_Out (C, J) - 1,
     Post   =>
       (Proof_Only =>
          Ok = Isolated_Layer (C, J)
          and then
          (if Ok then
             (for all W in 0 .. SA.NW_Out (C, J) - 1 =>
                (M (W) /= 0) = Assert_Wire (C, J, W))))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Isolated_Layer);
      First : constant Positive := C.Layers (J).First;
      Last  : constant Natural := C.Layers (J).Last;
      NV    : constant Natural := SA.NW_Out (C, J);
      K     : Natural;
   begin
      pragma Assert
        (SA.Fits (C.Terms (First .. Last), NV, C.Layers (J).NW_In));
      for W in 0 .. NV - 1 loop
         M (W) := 0;
         pragma Loop_Invariant
           (Proof_Only => (for all V in 0 .. W => M (V) = 0));
      end loop;
      Ok := True;
      --  Each assertion marks its wire; a second one on a marked wire
      --  is not isolated.
      for I in First .. Last loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all W in 0 .. NV - 1 =>
                 (if M (W) /= 0 then
                    M (W) in First .. I - 1
                    and then Is_Assert (C.Terms (M (W)))
                    and then C.Terms (M (W)).G = W))
              and then
              (for all I2 in First .. I - 1 =>
                 (if Is_Assert (C.Terms (I2)) then
                    M (C.Terms (I2).G) = I2)));
         if Is_Assert (C.Terms (I)) then
            K := M (C.Terms (I).G);
            if K /= 0 then
               --  K and I: two terms on one wire, K an assertion.
               pragma Assert
                 (Proof_Only =>
                    K in First .. Last and then K /= I
                    and then Is_Assert (C.Terms (K))
                    and then C.Terms (I).G = C.Terms (K).G);
               pragma Assert (Proof_Only => not Isolated_Layer (C, J));
               Ok := False;
               return;
            end if;
            M (C.Terms (I).G) := I;
         end if;
      end loop;
      pragma Assert
        (Proof_Only =>
           (for all I in First .. Last =>
              (if Is_Assert (C.Terms (I)) then M (C.Terms (I).G) = I)));
      --  Any other term on a marked wire.
      for I in First .. Last loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all I2 in First .. I - 1 =>
                 M (C.Terms (I2).G) = 0 or else M (C.Terms (I2).G) = I2));
         K := M (C.Terms (I).G);
         if K /= 0 and then K /= I then
            --  The assertion K shares its wire with I.
            pragma Assert
              (Proof_Only =>
                 K in First .. Last
                 and then Is_Assert (C.Terms (K))
                 and then C.Terms (I).G = C.Terms (K).G);
            pragma Assert (Proof_Only => not Isolated_Layer (C, J));
            Ok := False;
            return;
         end if;
      end loop;
      pragma Assert
        (Proof_Only =>
           (for all I in First .. Last =>
              M (C.Terms (I).G) = 0 or else M (C.Terms (I).G) = I));
      pragma Assert (Proof_Only => Isolated_Layer (C, J));
      pragma Assert
        (Proof_Only =>
           (for all W in 0 .. NV - 1 =>
              (M (W) /= 0) = Assert_Wire (C, J, W)));
   end Mark_Layer;

   --  Dead_End_Layer of layer J - 1 from its reads, either way.
   procedure Lemma_Dead_End (C : Raw_Circuit; J : Positive) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then
               (for all I in C.Layers (J - 1).First .. C.Layers (J - 1).Last =>
                  not Assert_Wire (C, J, C.Terms (I).H0)
                  and then not Assert_Wire (C, J, C.Terms (I).H1)),
     Post   => Dead_End_Layer (C, J - 1)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Dead_End_Layer);
   begin
      null;
   end Lemma_Dead_End;

   procedure Lemma_Not_Dead_End (C : Raw_Circuit; J : Positive; I : Positive)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then I in C.Layers (J - 1).First .. C.Layers (J - 1).Last
               and then (Assert_Wire (C, J, C.Terms (I).H0)
                         or else Assert_Wire (C, J, C.Terms (I).H1)),
     Post   => not Dead_End_Layer (C, J - 1)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Dead_End_Layer);
   begin
      null;
   end Lemma_Not_Dead_End;

   --  Isolated and Dead_End, layer by layer: the marks of layer J are
   --  checked against the reads of layer J - 1.
   procedure Check_Premises (C : Raw_Circuit; St : out Status) with
     Global => null,
     Pre    => SA.Well_Formed (C),
     Post   =>
       (Runtime => St in Ok | Not_Isolated | Not_Dead_End,
        Proof_Only =>
          (St = Ok) = (Isolated (C) and then Dead_End (C))
          and then (if St = Not_Isolated then not Isolated (C))
          and then (if St = Not_Dead_End then not Dead_End (C)))
   is
      NV_Max : Natural := 0;
      M      : Marks_Access;
      Iso    : Boolean;
   begin
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant
           (for all J2 in 0 .. J - 1 => SA.NW_Out (C, J2) <= NV_Max);
         pragma Loop_Invariant (NV_Max <= SA.Max_Wires);
         if SA.NW_Out (C, J) > NV_Max then
            NV_Max := SA.NW_Out (C, J);
         end if;
      end loop;
      M := new Marks'(0 .. NV_Max - 1 => 0);
      for J in 0 .. C.Last_Layer loop
         pragma Loop_Invariant (M /= null and then M'First = 0
                                and then M'Last = NV_Max - 1);
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J2 in 0 .. J - 1 => Isolated_Layer (C, J2))
              and then
              (for all J2 in 0 .. J - 2 => Dead_End_Layer (C, J2)));
         Mark_Layer (C, J, M.all, Iso);
         if not Iso then
            Free_Marks (M);
            St := Not_Isolated;
            return;
         end if;
         if J > 0 then
            pragma Assert
              (SA.NW_Out (C, J) = C.Layers (J - 1).NW_In
               and then
               SA.Fits (C.Terms (C.Layers (J - 1).First
                                 .. C.Layers (J - 1).Last),
                        SA.NW_Out (C, J - 1), C.Layers (J - 1).NW_In));
            for I in C.Layers (J - 1).First .. C.Layers (J - 1).Last loop
               pragma Loop_Invariant
                 (M /= null and then M'First = 0
                  and then M'Last = NV_Max - 1);
               pragma Loop_Invariant
                 (Proof_Only =>
                    (for all I2 in C.Layers (J - 1).First .. I - 1 =>
                       not Assert_Wire (C, J, C.Terms (I2).H0)
                       and then not Assert_Wire (C, J, C.Terms (I2).H1)));
               pragma Assert
                 (C.Terms (I).H0 < SA.NW_Out (C, J)
                  and then C.Terms (I).H1 < SA.NW_Out (C, J));
               if M (C.Terms (I).H0) /= 0 or else M (C.Terms (I).H1) /= 0
               then
                  pragma Assert
                    (Proof_Only =>
                       Assert_Wire (C, J, C.Terms (I).H0)
                       or else Assert_Wire (C, J, C.Terms (I).H1));
                  Lemma_Not_Dead_End (C, J, I);
                  Free_Marks (M);
                  St := Not_Dead_End;
                  return;
               end if;
            end loop;
            Lemma_Dead_End (C, J);
         end if;
      end loop;
      pragma Assert (Proof_Only => Isolated (C) and then Dead_End (C));
      Free_Marks (M);
      St := Ok;
   end Check_Premises;

   -------------------------------------------------------------------
   --  Read
   -------------------------------------------------------------------

   procedure Read
     (B  : Byte_Array;
      C  : out Circuit_Access;
      H  : out Header;
      St : out Status)
   is
      Cnt, Again : Counts;
      Id : Bytes_32;
   begin
      C := null;
      H := Null_Header;
      Walk (B, null, Cnt, St);
      if St /= Ok then
         return;
      end if;
      C := new Raw_Circuit'
        (Last_Layer => Cnt.NL - 1,
         NT         => Cnt.NT,
         Noutput    => Cnt.Noutput,
         Ninput     => Cnt.Ninput,
         Npublic    => Cnt.Npublic,
         Layers     => [others => (Logw => 0, NW_In => 0, First => 1,
                                   Last => 0)],
         Terms      => [others => (K => SA.Zero, G => 0, H0 => 0, H1 => 0)]);
      Walk (B, C, Again, St);
      if St /= Ok then
         Free (C);
         return;
      end if;
      --  The two walks read the same bytes; a disagreement is a defect
      --  of this unit, reported rather than trusted.
      if Again /= Cnt then
         Free (C);
         St := Bad_Index;
         return;
      end if;
      if not SA.Well_Formed (C.all) then
         Free (C);
         St := Not_Well_Formed;
         return;
      end if;
      Check_Premises (C.all, St);
      if St /= Ok then
         Free (C);
         return;
      end if;
      Id := B (Cnt.Id_Pos .. Cnt.Id_Pos + 31);
      if Compute_Id (C.all, Cnt.Sfb) /= Id then
         Free (C);
         St := Id_Mismatch;
         return;
      end if;
      H := (Field_Id => Field_Id, Subfield_Boundary => Cnt.Sfb, Id => Id);
   end Read;

end Circuit_Reader;
