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

   --  The body of Read and Read_Pinned: Pinned selects the check of
   --  the identifier, recomputed or compared with Pin.
   procedure Load
     (B      : Byte_Array;
      Pinned : Boolean;
      Pin    : Bytes_32;
      C      : out Circuit_Access;
      H      : out Header;
      St     : out Status)
   with
     Global => null,
     Pre    => B'First = 0,
     Post   =>
       (Runtime =>
          (St = Ok) = (C /= null)
          and then (if St = Ok then
                      SA.Well_Formed (C.all)
                      and then H.Field_Id = Field_Id
                      and then (if Pinned then H.Id = Pin
                                else H.Id = Compute_Id
                                       (C.all, H.Subfield_Boundary))
                    else H = Null_Header),
        Proof_Only =>
          (if St = Ok then Isolated (C.all) and then Dead_End (C.all)));

   procedure Load
     (B      : Byte_Array;
      Pinned : Boolean;
      Pin    : Bytes_32;
      C      : out Circuit_Access;
      H      : out Header;
      St     : out Status)
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
      if (if Pinned then Id /= Pin else Compute_Id (C.all, Cnt.Sfb) /= Id)
      then
         Free (C);
         St := Id_Mismatch;
         return;
      end if;
      H := (Field_Id => Field_Id, Subfield_Boundary => Cnt.Sfb, Id => Id);
   end Load;

   procedure Read
     (B  : Byte_Array;
      C  : out Circuit_Access;
      H  : out Header;
      St : out Status)
   is
   begin
      Load (B, False, [others => 0], C, H, St);
   end Read;

   procedure Read_Pinned
     (B  : Byte_Array;
      Id : Bytes_32;
      C  : out Circuit_Access;
      H  : out Header;
      St : out Status)
   is
   begin
      Load (B, True, Id, C, H, St);
   end Read_Pinned;

   -------------------------------------------------------------------
   --  The packed reader (the memory milestone, ADR 0080)
   -------------------------------------------------------------------

   use type PC.Cursor;
   use type SA.Layer;
   use type SA.Layer_Array;
   use type SA.Term;

   procedure Free_Packed_Circuit is
     new Ada.Unchecked_Deallocation (Packed_Circuit, Packed_Access);

   procedure Free_Packed (P : in out Packed_Access) is
   begin
      Free_Packed_Circuit (P);
   end Free_Packed;

   type Length_Access is access PC.Length_Array;

   procedure Free_Lengths is
     new Ada.Unchecked_Deallocation (PC.Length_Array, Length_Access);

   --  The counts of the packed walk: those of Walk, and the deltas,
   --  segments, segment entries and kept tokens.
   type P_Counts is record
      NL, NT, Noutput, Ninput, Npublic, Nconst, Sfb : Natural;
      ND, NS, NE, NK : Natural;
      Id_Pos : Natural;
   end record;

   Zero_P_Counts : constant P_Counts := (others => 0);

   function Bounded (Cnt : P_Counts) return Boolean is
     (Cnt.NT <= SA.Max_Terms and then Cnt.ND <= SA.Max_Terms
      and then Cnt.NS <= SA.Max_Terms and then Cnt.NE <= SA.Max_Terms
      and then Cnt.NK <= SA.Max_Terms)
   with Global => null;

   --  One layer, as Read_Layer, without expanding it: its deltas,
   --  segments and tokens are written into P (when not null) after those
   --  of the layers before, which Cnt counts, their indices made global;
   --  a token of an empty segment is not kept.
   procedure Read_Layer_P
     (B      : Byte_Array;
      Pos    : in out Natural;
      P      : Packed_Access;
      Nconst : Natural;
      J      : Natural;
      Cnt    : in out P_Counts;
      St     : out Status)
   with
     Global => null,
     Pre    => B'First = 0 and then Pos <= B'Length and then Bounded (Cnt),
     Post   => (if St = Ok then Pos <= B'Length and then Bounded (Cnt))
               and then Cnt.NL = Cnt'Old.NL
               and then Cnt.Noutput = Cnt'Old.Noutput
               and then Cnt.Ninput = Cnt'Old.Ninput
               and then Cnt.Npublic = Cnt'Old.Npublic
               and then Cnt.Nconst = Cnt'Old.Nconst
               and then Cnt.Sfb = Cnt'Old.Sfb
               and then Cnt.Id_Pos = Cnt'Old.Id_Pos;

   procedure Read_Layer_P
     (B      : Byte_Array;
      Pos    : in out Natural;
      P      : Packed_Access;
      Nconst : Natural;
      J      : Natural;
      Cnt    : in out P_Counts;
      St     : out Status)
   is
      Logw, NW, ND, NS, NTok, V, Len, Tok : Natural;
      DG, DH0, DH1 : Natural;
      L     : Length_Access := null;
      E_Off : Natural := 0;
      LT    : Natural := 0;
      NKL   : Natural := 0;
   begin
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
      if ND > SA.Max_Terms - Cnt.ND then
         St := Bound_Exceeded;
         return;
      end if;
      for I in 1 .. ND loop
         pragma Loop_Invariant (Pos <= B'Length);
         Read_Nat (B, Pos, DG, St);
         if St /= Ok then
            return;
         end if;
         Read_Nat (B, Pos, DH0, St);
         if St /= Ok then
            return;
         end if;
         Read_Nat (B, Pos, DH1, St);
         if St /= Ok then
            return;
         end if;
         Read_Nat (B, Pos, V, St);
         if St /= Ok then
            return;
         end if;
         if V >= Nconst then
            St := Bad_Index;
            return;
         end if;
         if P /= null and then Cnt.ND + I <= P.ND then
            P.Deltas (Cnt.ND + I) :=
              (DG  => Long_Long_Integer (Uleb128.Zigzag (DG)),
               DH0 => Long_Long_Integer (Uleb128.Zigzag (DH0)),
               DH1 => Long_Long_Integer (Uleb128.Zigzag (DH1)),
               K   => V + 1);
         end if;
      end loop;

      --  Segments: a length then the delta indices, so at least one
      --  byte each.
      Read_Nat (B, Pos, NS, St);
      if St /= Ok then
         return;
      end if;
      if NS > B'Length - Pos then
         St := Truncated;
         return;
      end if;
      if NS > SA.Max_Terms - Cnt.NS then
         St := Bound_Exceeded;
         return;
      end if;
      L := new PC.Length_Array'(1 .. NS => 0);
      for I in 1 .. NS loop
         pragma Loop_Invariant (Pos <= B'Length);
         pragma Loop_Invariant
           (L /= null and then L'First = 1 and then L'Last = NS);
         pragma Loop_Invariant (E_Off <= SA.Max_Terms - Cnt.NE);
         Read_Nat (B, Pos, Len, St);
         if St /= Ok then
            Free_Lengths (L);
            return;
         end if;
         if Len > B'Length - Pos then
            St := Truncated;
            Free_Lengths (L);
            return;
         end if;
         if Len > SA.Max_Terms - Cnt.NE - E_Off then
            St := Bound_Exceeded;
            Free_Lengths (L);
            return;
         end if;
         L (I) := Len;
         if P /= null and then Cnt.NS + I <= P.NS then
            P.Seg_Start (Cnt.NS + I) := Cnt.NE + E_Off + 1;
            P.Seg_Len (Cnt.NS + I) := Len;
         end if;
         for X in 1 .. Len loop
            pragma Loop_Invariant (Pos <= B'Length);
            pragma Loop_Invariant
              (L /= null and then L'First = 1 and then L'Last = NS);
            Read_Nat (B, Pos, V, St);
            if St /= Ok then
               Free_Lengths (L);
               return;
            end if;
            if V >= ND then
               St := Bad_Index;
               Free_Lengths (L);
               return;
            end if;
            if P /= null and then Cnt.NE + E_Off + X <= P.NE then
               P.Entries (Cnt.NE + E_Off + X) := Cnt.ND + V + 1;
            end if;
         end loop;
         E_Off := E_Off + Len;
      end loop;

      --  Tokens: each names a segment; a token of an empty segment adds
      --  no term and is not kept.
      Read_Nat (B, Pos, NTok, St);
      if St /= Ok then
         Free_Lengths (L);
         return;
      end if;
      for T in 1 .. NTok loop
         pragma Loop_Invariant (Pos <= B'Length);
         pragma Loop_Invariant
           (L /= null and then L'First = 1 and then L'Last = NS);
         pragma Loop_Invariant (LT <= SA.Max_Terms - Cnt.NT);
         pragma Loop_Invariant (NKL <= SA.Max_Terms - Cnt.NK);
         Read_Nat (B, Pos, Tok, St);
         if St /= Ok then
            Free_Lengths (L);
            return;
         end if;
         if Tok >= NS then
            St := Bad_Index;
            Free_Lengths (L);
            return;
         end if;
         Len := L (Tok + 1);
         if Len > SA.Max_Terms - Cnt.NT - LT then
            St := Bound_Exceeded;
            Free_Lengths (L);
            return;
         end if;
         if Len > 0 then
            if NKL = SA.Max_Terms - Cnt.NK then
               St := Bound_Exceeded;
               Free_Lengths (L);
               return;
            end if;
            NKL := NKL + 1;
            if P /= null and then Cnt.NK + NKL <= P.NK then
               P.Tokens (Cnt.NK + NKL) := Cnt.NS + Tok + 1;
            end if;
         end if;
         LT := LT + Len;
      end loop;
      Free_Lengths (L);

      if P /= null then
         if J > P.Last_Layer then
            St := Bad_Index;
            return;
         end if;
         P.Layers (J) := (Logw  => Logw,
                          NW_In => NW,
                          First => Cnt.NT + 1,
                          Last  => Cnt.NT + LT);
         P.Spans (J) := (First => Cnt.NK + 1, Last => Cnt.NK + NKL);
      end if;
      Cnt.NT := Cnt.NT + LT;
      Cnt.ND := Cnt.ND + ND;
      Cnt.NS := Cnt.NS + NS;
      Cnt.NE := Cnt.NE + E_Off;
      Cnt.NK := Cnt.NK + NKL;
      St := Ok;
   end Read_Layer_P;

   --  The walk of the file for the packed form: count (P null), or fill
   --  (P allocated with the counts of the first walk).
   procedure Walk_P
     (B   : Byte_Array;
      P   : Packed_Access;
      Cnt : out P_Counts;
      St  : out Status)
   with
     Global => null,
     Pre    => B'First = 0,
     Post   =>
       (if St = Ok then
          Cnt.NL in 1 .. SA.Max_Layers
          and then Bounded (Cnt)
          and then Cnt.Nconst <= SA.Max_Terms
          and then Cnt.Noutput <= SA.Max_Wires
          and then Cnt.Ninput <= SA.Max_Wires
          and then Cnt.Npublic <= SA.Max_Wires
          and then Cnt.Id_Pos + 32 = B'Length);

   procedure Walk_P
     (B   : Byte_Array;
      P   : Packed_Access;
      Cnt : out P_Counts;
      St  : out Status)
   is
      Pos : Natural;
      V, Fid : Natural;
      E : SA.Element;
   begin
      Cnt := Zero_P_Counts;
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
      if Cnt.Nconst > SA.Max_Terms then
         St := Bound_Exceeded;
         return;
      end if;
      for I in 1 .. Cnt.Nconst loop
         pragma Loop_Invariant (Pos <= B'Length);
         pragma Loop_Invariant (Cnt.Nconst <= SA.Max_Terms);
         pragma Loop_Invariant (Bounded (Cnt));
         Read_Element (B, Pos, E, St);
         if St /= Ok then
            return;
         end if;
         if P /= null and then I <= P.NC then
            P.Constants (I) := E;
         end if;
      end loop;

      --  The layers.
      for J in 0 .. Cnt.NL - 1 loop
         pragma Loop_Invariant (Pos <= B'Length);
         pragma Loop_Invariant (Bounded (Cnt));
         pragma Loop_Invariant (Cnt.Nconst <= SA.Max_Terms);
         pragma Loop_Invariant
           (Cnt.Noutput <= SA.Max_Wires and then Cnt.Ninput <= SA.Max_Wires
            and then Cnt.Npublic <= SA.Max_Wires
            and then Cnt.NL in 1 .. SA.Max_Layers);
         Read_Layer_P (B, Pos, P, Cnt.Nconst, J, Cnt, St);
         if St /= Ok then
            return;
         end if;
      end loop;

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
   end Walk_P;

   --  The part of Well_Formed that does not read the terms.
   function Shape_Ok (P : Packed_Circuit) return Boolean is
     (P.Npublic <= P.Ninput
      and then P.Layers (P.Last_Layer).Last = P.NT
      and then (for all J in 0 .. P.Last_Layer =>
                  Unsigned_64 (P.Layers (J).NW_In)
                    <= Shift_Left (1, P.Layers (J).Logw))
      and then P.Layers (P.Last_Layer).NW_In = P.Ninput)
   with Global => null;

   --  The wires layer J's terms read and write: as in Well_Formed.
   function NV_Of (P : Packed_Circuit; J : Natural) return Natural is
     (if J = 0 then P.Noutput else P.Layers (J - 1).NW_In)
   with Global => null, Pre => J <= P.Last_Layer;

   --  Counts_Ok, checked: each layer's term count is what its tokens
   --  produce.
   procedure Check_Counts (P : Packed_Circuit; Ok : out Boolean) with
     Global => null,
     Pre    => PC.Indices_Ok (P) and then PC.Layers_Ok (P),
     Post   => (Proof_Only => (if Ok then PC.Counts_Ok (P)))
   is
      S : Long_Long_Integer;
   begin
      for J in 0 .. P.Last_Layer loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J2 in 0 .. J - 1 =>
                 Long_Long_Integer
                   (P.Layers (J2).Last + 1 - P.Layers (J2).First)
                 = PC.Tok_Sum (P, P.Spans (J2).First, P.Spans (J2).Last)));
         S := 0;
         for T in P.Spans (J).First .. P.Spans (J).Last loop
            pragma Loop_Invariant
              (S >= 0 and then S <= Long_Long_Integer (T - P.Spans (J).First)
                                    * Long_Long_Integer (SA.Max_Terms));
            pragma Loop_Invariant
              (Proof_Only => S = PC.Tok_Sum (P, P.Spans (J).First, T - 1));
            S := S + Long_Long_Integer (P.Seg_Len (P.Tokens (T)));
         end loop;
         pragma Assert
           (Proof_Only =>
              S = PC.Tok_Sum (P, P.Spans (J).First, P.Spans (J).Last));
         if S /= Long_Long_Integer (P.Layers (J).Last + 1 - P.Layers (J).First)
         then
            Ok := False;
            return;
         end if;
      end loop;
      Ok := True;
   end Check_Counts;

   --  Every term's wires in range, checked by a walk of each layer: the
   --  out-of-range wire is a Bad_Index, as when Read expands the layer.
   procedure Check_Wires (P : Packed_Circuit; Ok : out Boolean) with
     Global => null,
     Pre    => (Proof_Only =>
                  PC.Indices_Ok (P) and then PC.Layers_Ok (P)
                  and then PC.Counts_Ok (P)),
     Post   => (Proof_Only => (if Ok then PC.Wires_Ok (P)))
   is
      C : PC.Cursor;
      D : PC.Packed_Delta;
   begin
      for J in 0 .. P.Last_Layer loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J2 in 0 .. J - 1 =>
                 (for all K in 1 .. PC.Layer_Len (P, J2) =>
                    PC.Cursor_At (P, J2, K).G in 0 .. SA.Max_Wires - 1
                    and then PC.Cursor_At (P, J2, K).H0
                               in 0 .. SA.Max_Wires - 1
                    and then PC.Cursor_At (P, J2, K).H1
                               in 0 .. SA.Max_Wires - 1)));
         C := PC.Start (P, J);
         for K in 1 .. PC.Layer_Len (P, J) loop
            pragma Loop_Invariant
              (Proof_Only => C = PC.Cursor_At (P, J, K - 1));
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all K2 in 1 .. K - 1 =>
                    PC.Cursor_At (P, J, K2).G in 0 .. SA.Max_Wires - 1
                    and then PC.Cursor_At (P, J, K2).H0
                               in 0 .. SA.Max_Wires - 1
                    and then PC.Cursor_At (P, J, K2).H1
                               in 0 .. SA.Max_Wires - 1));
            PC.Lemma_Step (P, J, K);
            pragma Assert (PC.On_Delta (P, C));
            D := PC.Delta_At (P, C);
            if C.G + D.DG not in 0 .. SA.Max_Wires - 1
              or else C.H0 + D.DH0 not in 0 .. SA.Max_Wires - 1
              or else C.H1 + D.DH1 not in 0 .. SA.Max_Wires - 1
            then
               Ok := False;
               return;
            end if;
            C := PC.Step (P, C);
            pragma Assert (Proof_Only => C = PC.Cursor_At (P, J, K));
         end loop;
      end loop;
      Ok := True;
   end Check_Wires;

   --  Fits of every layer of the expansion, checked by a walk.
   procedure Check_Fits (P : Packed_Circuit; Ok : out Boolean) with
     Global => null,
     Pre    => (Proof_Only => PC.Valid (P) and then PC.Layers_Ok (P)),
     Post   =>
       (Proof_Only =>
          (if Ok then
             (for all J in 0 .. P.Last_Layer =>
                SA.Fits (PC.Expand (P).Terms (P.Layers (J).First
                                              .. P.Layers (J).Last),
                         NV_Of (P, J), P.Layers (J).NW_In))))
   is
      E : constant Raw_Circuit := PC.Expand (P) with Ghost => Proof_Only;
      C : PC.Cursor;
      T : SA.Term;
   begin
      PC.Lemma_Valid (P);
      for J in 0 .. P.Last_Layer loop
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J2 in 0 .. J - 1 =>
                 SA.Fits (E.Terms (P.Layers (J2).First .. P.Layers (J2).Last),
                          NV_Of (P, J2), P.Layers (J2).NW_In)));
         C := PC.Start (P, J);
         PC.Lemma_Walked_Start (P, J);
         for K in 1 .. PC.Layer_Len (P, J) loop
            pragma Loop_Invariant (Proof_Only => PC.Walked (P, J, K - 1, C));
            pragma Loop_Invariant
              (Proof_Only =>
                 (for all I2 in P.Layers (J).First
                                .. P.Layers (J).First + K - 2 =>
                    E.Terms (I2).G < NV_Of (P, J)
                    and then E.Terms (I2).H0 < P.Layers (J).NW_In
                    and then E.Terms (I2).H1 < P.Layers (J).NW_In));
            PC.Lemma_Walked_Step (P, J, K, C);
            T := PC.Term_Of (P, C);
            pragma Assert
              (Proof_Only => T = E.Terms (P.Layers (J).First + K - 1));
            if T.G >= NV_Of (P, J)
              or else T.H0 >= P.Layers (J).NW_In
              or else T.H1 >= P.Layers (J).NW_In
            then
               Ok := False;
               return;
            end if;
            C := PC.Step (P, C);
            pragma Assert
              (Proof_Only =>
                 (for all I2 in P.Layers (J).First
                                .. P.Layers (J).First + K - 1 =>
                    E.Terms (I2).G < NV_Of (P, J)
                    and then E.Terms (I2).H0 < P.Layers (J).NW_In
                    and then E.Terms (I2).H1 < P.Layers (J).NW_In));
         end loop;
         pragma Assert
           (Proof_Only =>
              SA.Fits (E.Terms (P.Layers (J).First .. P.Layers (J).Last),
                       NV_Of (P, J), P.Layers (J).NW_In));
      end loop;
      Ok := True;
   end Check_Fits;

   --  The expansion is well formed: its layers are P's, and they fit.
   procedure Lemma_Well_Formed (P : Packed_Circuit) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => PC.Valid (P) and then PC.Layers_Ok (P) and then Shape_Ok (P)
               and then
               (for all J in 0 .. P.Last_Layer =>
                  SA.Fits (PC.Expand (P).Terms (P.Layers (J).First
                                                .. P.Layers (J).Last),
                           NV_Of (P, J), P.Layers (J).NW_In)),
     Post   => SA.Well_Formed (PC.Expand (P))
   is
      E : constant Raw_Circuit := PC.Expand (P);
   begin
      pragma Assert (E.Layers = P.Layers);
      pragma Assert
        (for all J in 0 .. E.Last_Layer =>
           SA.Fits (E.Terms (E.Layers (J).First .. E.Layers (J).Last),
                    (if J = 0 then E.Noutput else E.Layers (J - 1).NW_In),
                    E.Layers (J).NW_In));
   end Lemma_Well_Formed;

   --  Two terms of layer J on one wire, one an assertion: not isolated.
   procedure Lemma_Not_Isolated
     (C : Raw_Circuit; J : Natural; X, I : Positive)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then X in C.Layers (J).First .. C.Layers (J).Last
               and then I in C.Layers (J).First .. C.Layers (J).Last
               and then X /= I and then Is_Assert (C.Terms (X))
               and then C.Terms (I).G = C.Terms (X).G,
     Post   => not Isolated_Layer (C, J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Isolated_Layer);
   begin
      null;
   end Lemma_Not_Isolated;

   --  The marks of layer J make it isolated: each assertion marks its
   --  wire with its own index, and every term's wire is unmarked or
   --  marked with that term's index.
   procedure Lemma_Isolated (C : Raw_Circuit; J : Natural; M : Marks) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then M'First = 0 and then M'Last >= SA.NW_Out (C, J) - 1
               and then
               (for all I in C.Layers (J).First .. C.Layers (J).Last =>
                  (if Is_Assert (C.Terms (I)) then M (C.Terms (I).G) = I))
               and then
               (for all I in C.Layers (J).First .. C.Layers (J).Last =>
                  M (C.Terms (I).G) = 0 or else M (C.Terms (I).G) = I),
     Post   => Isolated_Layer (C, J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Isolated_Layer);
   begin
      pragma Assert
        (SA.Fits (C.Terms (C.Layers (J).First .. C.Layers (J).Last),
                  SA.NW_Out (C, J), C.Layers (J).NW_In));
   end Lemma_Isolated;

   --  The invariants of the marking walks of a layer, hidden so that
   --  the walks carry them as plain facts; the lemmas below are the steps
   --  of the proof of Mark_Layer, one term at a time.

   --  Before term I of layer J: each marked wire names an assertion
   --  before I on that wire, and each assertion before I marks its wire.
   function Inv_Mark
     (C : Raw_Circuit; J : Natural; M : Marks; I : Positive) return Boolean
   is
     ((for all W in 0 .. SA.NW_Out (C, J) - 1 =>
         (if M (W) /= 0 then
            M (W) in C.Layers (J).First .. I - 1
            and then Is_Assert (C.Terms (M (W)))
            and then C.Terms (M (W)).G = W))
      and then
      (for all I2 in C.Layers (J).First .. I - 1 =>
         (if Is_Assert (C.Terms (I2)) then M (C.Terms (I2).G) = I2)))
   with Ghost    => Proof_Only,
        Global   => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre      => SA.Well_Formed (C) and then J <= C.Last_Layer
                    and then M'First = 0
                    and then M'Last >= SA.NW_Out (C, J) - 1
                    and then I in C.Layers (J).First
                                  .. C.Layers (J).Last + 1;

   --  Before term I of layer J: no term before I shares the wire of an
   --  assertion other than itself.
   function Inv_Seen
     (C : Raw_Circuit; J : Natural; M : Marks; I : Positive) return Boolean
   is
     (for all I2 in C.Layers (J).First .. I - 1 =>
        M (C.Terms (I2).G) = 0 or else M (C.Terms (I2).G) = I2)
   with Ghost    => Proof_Only,
        Global   => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre      => SA.Well_Formed (C) and then J <= C.Last_Layer
                    and then M'First = 0
                    and then M'Last >= SA.NW_Out (C, J) - 1
                    and then I in C.Layers (J).First
                                  .. C.Layers (J).Last + 1;

   --  The wires of term I of layer J are in range.
   procedure Lemma_Fits_At (C : Raw_Circuit; J : Natural; I : Positive) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then I in C.Layers (J).First .. C.Layers (J).Last,
     Post   => C.Terms (I).G < SA.NW_Out (C, J)
               and then C.Terms (I).H0 < C.Layers (J).NW_In
               and then C.Terms (I).H1 < C.Layers (J).NW_In
   is
   begin
      pragma Assert
        (SA.Fits (C.Terms (C.Layers (J).First .. C.Layers (J).Last),
                  SA.NW_Out (C, J), C.Layers (J).NW_In));
   end Lemma_Fits_At;

   procedure Lemma_Mark_Start (C : Raw_Circuit; J : Natural; M : Marks) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then M'First = 0 and then M'Last >= SA.NW_Out (C, J) - 1
               and then (for all W in 0 .. SA.NW_Out (C, J) - 1 => M (W) = 0),
     Post   => Inv_Mark (C, J, M, C.Layers (J).First)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Inv_Mark);
   begin
      null;
   end Lemma_Mark_Start;

   --  Term I is not an assertion: nothing to mark.
   procedure Lemma_Mark_Skip
     (C : Raw_Circuit; J : Natural; M : Marks; I : Positive)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then M'First = 0 and then M'Last >= SA.NW_Out (C, J) - 1
               and then I in C.Layers (J).First .. C.Layers (J).Last
               and then Inv_Mark (C, J, M, I)
               and then not Is_Assert (C.Terms (I)),
     Post   => Inv_Mark (C, J, M, I + 1)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Inv_Mark);
   begin
      null;
   end Lemma_Mark_Skip;

   --  Term I is an assertion on an unmarked wire, which it marks.
   procedure Lemma_Mark_Set
     (C : Raw_Circuit; J : Natural; M_Old, M : Marks; I : Positive)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then M_Old'First = 0
               and then M_Old'Last >= SA.NW_Out (C, J) - 1
               and then M'First = 0 and then M'Last = M_Old'Last
               and then I in C.Layers (J).First .. C.Layers (J).Last
               and then Inv_Mark (C, J, M_Old, I)
               and then Is_Assert (C.Terms (I))
               and then C.Terms (I).G < SA.NW_Out (C, J)
               and then M_Old (C.Terms (I).G) = 0
               and then
               (for all W in M'Range =>
                  M (W) = (if W = C.Terms (I).G then I else M_Old (W))),
     Post   => Inv_Mark (C, J, M, I + 1)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Inv_Mark);
   begin
      Lemma_Fits_At (C, J, I);
   end Lemma_Mark_Set;

   --  Term I is an assertion on a wire already marked: not isolated.
   procedure Lemma_Mark_Conflict
     (C : Raw_Circuit; J : Natural; M : Marks; I : Positive)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then M'First = 0 and then M'Last >= SA.NW_Out (C, J) - 1
               and then I in C.Layers (J).First .. C.Layers (J).Last
               and then Inv_Mark (C, J, M, I)
               and then Is_Assert (C.Terms (I))
               and then C.Terms (I).G < SA.NW_Out (C, J)
               and then M (C.Terms (I).G) /= 0,
     Post   => not Isolated_Layer (C, J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Inv_Mark);
      X : constant Natural := M (C.Terms (I).G);
   begin
      pragma Assert (X in C.Layers (J).First .. I - 1);
      Lemma_Not_Isolated (C, J, X, I);
   end Lemma_Mark_Conflict;

   procedure Lemma_Seen_Start (C : Raw_Circuit; J : Natural; M : Marks) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then M'First = 0 and then M'Last >= SA.NW_Out (C, J) - 1,
     Post   => Inv_Seen (C, J, M, C.Layers (J).First)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Inv_Seen);
   begin
      null;
   end Lemma_Seen_Start;

   --  Term I is on an unmarked wire, or is the assertion of its wire.
   procedure Lemma_Seen_Step
     (C : Raw_Circuit; J : Natural; M : Marks; I : Positive)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then M'First = 0 and then M'Last >= SA.NW_Out (C, J) - 1
               and then I in C.Layers (J).First .. C.Layers (J).Last
               and then Inv_Seen (C, J, M, I)
               and then C.Terms (I).G < SA.NW_Out (C, J)
               and then (M (C.Terms (I).G) = 0
                         or else M (C.Terms (I).G) = I),
     Post   => Inv_Seen (C, J, M, I + 1)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Inv_Seen);
   begin
      null;
   end Lemma_Seen_Step;

   --  Term I shares the wire of another term's assertion: not isolated.
   procedure Lemma_Seen_Conflict
     (C : Raw_Circuit; J : Natural; M : Marks; I : Positive)
   with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then M'First = 0 and then M'Last >= SA.NW_Out (C, J) - 1
               and then I in C.Layers (J).First .. C.Layers (J).Last
               and then Inv_Mark (C, J, M, C.Layers (J).Last + 1)
               and then C.Terms (I).G < SA.NW_Out (C, J)
               and then M (C.Terms (I).G) /= 0
               and then M (C.Terms (I).G) /= I,
     Post   => not Isolated_Layer (C, J)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Inv_Mark);
      X : constant Natural := M (C.Terms (I).G);
   begin
      pragma Assert
        (X in C.Layers (J).First .. C.Layers (J).Last
         and then Is_Assert (C.Terms (X))
         and then C.Terms (X).G = C.Terms (I).G);
      Lemma_Not_Isolated (C, J, X, I);
   end Lemma_Seen_Conflict;

   --  Both walks done: the layer is isolated, and the marked wires are
   --  the wires of its assertions.
   procedure Lemma_Marks_Final (C : Raw_Circuit; J : Natural; M : Marks) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => SA.Well_Formed (C) and then J <= C.Last_Layer
               and then M'First = 0 and then M'Last >= SA.NW_Out (C, J) - 1
               and then Inv_Mark (C, J, M, C.Layers (J).Last + 1)
               and then Inv_Seen (C, J, M, C.Layers (J).Last + 1),
     Post   => Isolated_Layer (C, J)
               and then
               (for all W in 0 .. SA.NW_Out (C, J) - 1 =>
                  (M (W) /= 0) = Assert_Wire (C, J, W))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Inv_Mark);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Inv_Seen);
   begin
      Lemma_Isolated (C, J, M);
      pragma Assert
        (for all W in 0 .. SA.NW_Out (C, J) - 1 =>
           (if M (W) /= 0 then Assert_Wire (C, J, W)));
      pragma Assert
        (for all W in 0 .. SA.NW_Out (C, J) - 1 =>
           (if Assert_Wire (C, J, W) then M (W) /= 0));
   end Lemma_Marks_Final;

   --  Mark_Layer on the walk of layer J of P: Ok when every assertion of
   --  the layer is alone on its wire; then M (W) is the term index of the
   --  assertion of wire W, or 0. The proof is Mark_Layer's, on the terms
   --  of Expand (P), which the walk produces one by one, in the lemmas
   --  above.
   procedure Mark_Layer_P
     (P : Packed_Circuit; J : Natural; M : in out Marks; Ok : out Boolean)
   with
     Global => null,
     Pre    =>
       (Runtime    =>
          J <= P.Last_Layer
          and then M'First = 0 and then M'Last >= NV_Of (P, J) - 1,
        Proof_Only =>
          PC.Valid (P) and then SA.Well_Formed (PC.Expand (P))),
     Post   =>
       (Proof_Only =>
          Ok = Isolated_Layer (PC.Expand (P), J)
          and then
          (if Ok then
             (for all W in 0 .. NV_Of (P, J) - 1 =>
                (M (W) /= 0) = Assert_Wire (PC.Expand (P), J, W))))
   is
      E     : constant Raw_Circuit := PC.Expand (P) with Ghost => Proof_Only;
      First : constant Positive := P.Layers (J).First;
      NV    : constant Natural := NV_Of (P, J);
      C     : PC.Cursor;
      T     : SA.Term;
      I     : Positive;
      X     : Natural;
   begin
      PC.Lemma_Valid (P);
      pragma Assert
        (Proof_Only =>
           E.Layers (J) = P.Layers (J) and then SA.NW_Out (E, J) = NV);
      for W in 0 .. NV - 1 loop
         M (W) := 0;
         pragma Loop_Invariant
           (Proof_Only => (for all V in 0 .. W => M (V) = 0));
      end loop;
      Lemma_Mark_Start (E, J, M);
      Ok := True;
      --  Each assertion marks its wire; a second one on a marked wire
      --  is not isolated.
      C := PC.Start (P, J);
      PC.Lemma_Walked_Start (P, J);
      for K in 1 .. PC.Layer_Len (P, J) loop
         I := First + K - 1;
         pragma Loop_Invariant (I = First + K - 1);
         pragma Loop_Invariant (Proof_Only => PC.Walked (P, J, K - 1, C));
         pragma Loop_Invariant (Proof_Only => Inv_Mark (E, J, M, I));
         PC.Lemma_Walked_Step (P, J, K, C);
         T := PC.Term_Of (P, C);
         pragma Assert (Proof_Only => T = E.Terms (I));
         Lemma_Fits_At (E, J, I);
         if Is_Assert (T) then
            X := M (T.G);
            if X /= 0 then
               Lemma_Mark_Conflict (E, J, M, I);
               Ok := False;
               return;
            end if;
            declare
               M_Old : constant Marks := M with Ghost => Proof_Only;
            begin
               M (T.G) := I;
               Lemma_Mark_Set (E, J, M_Old, M, I);
            end;
         else
            Lemma_Mark_Skip (E, J, M, I);
         end if;
         C := PC.Step (P, C);
      end loop;
      pragma Assert
        (Proof_Only => Inv_Mark (E, J, M, E.Layers (J).Last + 1));
      --  Any other term on a marked wire.
      Lemma_Seen_Start (E, J, M);
      C := PC.Start (P, J);
      PC.Lemma_Walked_Start (P, J);
      for K in 1 .. PC.Layer_Len (P, J) loop
         I := First + K - 1;
         pragma Loop_Invariant (I = First + K - 1);
         pragma Loop_Invariant (Proof_Only => PC.Walked (P, J, K - 1, C));
         pragma Loop_Invariant (Proof_Only => Inv_Seen (E, J, M, I));
         PC.Lemma_Walked_Step (P, J, K, C);
         T := PC.Term_Of (P, C);
         pragma Assert (Proof_Only => T = E.Terms (I));
         Lemma_Fits_At (E, J, I);
         X := M (T.G);
         if X /= 0 and then X /= I then
            Lemma_Seen_Conflict (E, J, M, I);
            Ok := False;
            return;
         end if;
         Lemma_Seen_Step (E, J, M, I);
         C := PC.Step (P, C);
      end loop;
      pragma Assert
        (Proof_Only => Inv_Seen (E, J, M, E.Layers (J).Last + 1));
      Lemma_Marks_Final (E, J, M);
   end Mark_Layer_P;

   --  Check_Premises on the walks of P: the marks of layer J against the
   --  reads of layer J - 1.
   procedure Check_Premises_P (P : Packed_Circuit; St : out Status) with
     Global => null,
     Pre    => (Proof_Only =>
                  PC.Valid (P) and then SA.Well_Formed (PC.Expand (P))),
     Post   =>
       (Runtime => St in Ok | Not_Isolated | Not_Dead_End,
        Proof_Only =>
          (St = Ok) = (Isolated (PC.Expand (P))
                       and then Dead_End (PC.Expand (P))))
   is
      E      : constant Raw_Circuit := PC.Expand (P) with Ghost => Proof_Only;
      NV_Max : Natural := 0;
      M      : Marks_Access;
      Iso    : Boolean;
      C      : PC.Cursor;
      T      : SA.Term;
   begin
      PC.Lemma_Valid (P);
      for J in 0 .. P.Last_Layer loop
         pragma Loop_Invariant
           (for all J2 in 0 .. J - 1 => NV_Of (P, J2) <= NV_Max);
         pragma Loop_Invariant (NV_Max <= SA.Max_Wires);
         if NV_Of (P, J) > NV_Max then
            NV_Max := NV_Of (P, J);
         end if;
      end loop;
      M := new Marks'(0 .. NV_Max - 1 => 0);
      for J in 0 .. P.Last_Layer loop
         pragma Loop_Invariant (M /= null and then M'First = 0
                                and then M'Last = NV_Max - 1);
         pragma Loop_Invariant
           (Proof_Only =>
              (for all J2 in 0 .. J - 1 => Isolated_Layer (E, J2))
              and then
              (for all J2 in 0 .. J - 2 => Dead_End_Layer (E, J2)));
         Mark_Layer_P (P, J, M.all, Iso);
         if not Iso then
            Free_Marks (M);
            St := Not_Isolated;
            return;
         end if;
         if J > 0 then
            pragma Assert
              (Proof_Only =>
                 SA.NW_Out (E, J) = E.Layers (J - 1).NW_In
                 and then
                 SA.Fits (E.Terms (E.Layers (J - 1).First
                                   .. E.Layers (J - 1).Last),
                          SA.NW_Out (E, J - 1), E.Layers (J - 1).NW_In));
            C := PC.Start (P, J - 1);
            PC.Lemma_Walked_Start (P, J - 1);
            for K in 1 .. PC.Layer_Len (P, J - 1) loop
               pragma Loop_Invariant
                 (M /= null and then M'First = 0
                  and then M'Last = NV_Max - 1);
               pragma Loop_Invariant
                 (Proof_Only => PC.Walked (P, J - 1, K - 1, C));
               pragma Loop_Invariant
                 (Proof_Only =>
                    (for all I2 in P.Layers (J - 1).First
                                   .. P.Layers (J - 1).First + K - 2 =>
                       not Assert_Wire (E, J, E.Terms (I2).H0)
                       and then not Assert_Wire (E, J, E.Terms (I2).H1)));
               PC.Lemma_Walked_Step (P, J - 1, K, C);
               T := PC.Term_Of (P, C);
               pragma Assert
                 (Proof_Only =>
                    T = E.Terms (P.Layers (J - 1).First + K - 1));
               pragma Assert
                 (T.H0 < NV_Of (P, J) and then T.H1 < NV_Of (P, J));
               if M (T.H0) /= 0 or else M (T.H1) /= 0 then
                  pragma Assert
                    (Proof_Only =>
                       Assert_Wire (E, J, T.H0)
                       or else Assert_Wire (E, J, T.H1));
                  Lemma_Not_Dead_End (E, J, P.Layers (J - 1).First + K - 1);
                  Free_Marks (M);
                  St := Not_Dead_End;
                  return;
               end if;
               C := PC.Step (P, C);
            end loop;
            Lemma_Dead_End (E, J);
         end if;
      end loop;
      pragma Assert (Proof_Only => Isolated (E) and then Dead_End (E));
      Free_Marks (M);
      St := Ok;
   end Check_Premises_P;

   function Compute_Id_P
     (P : Packed_Circuit; Subfield_Boundary : Natural) return Bytes_32
   is
      Ctx : Sha256.Context := Sha256.Initial;
      Tag  : constant Bytes_8 := LE64 (if Is_Binary then 2 else 1);
      Mone : constant Byte_Array := SA.F.To_Bytes (SA.F.Neg (SA.F.One));
      C    : PC.Cursor;
      T    : SA.Term;
   begin
      PC.Lemma_Valid (P);
      Sha256.Update (Ctx, Tag);
      Sha256.Update (Ctx, (if Is_Binary then LE64 (8 * Size) else Mone));
      Sha256.Update (Ctx, LE64 (P.Noutput));
      Sha256.Update (Ctx, LE64 (Ceil_Lg2 (P.Noutput)));
      Sha256.Update (Ctx, LE64 (1));   --  ncopies
      Sha256.Update (Ctx, LE64 (0));   --  logc
      Sha256.Update (Ctx, LE64 (P.Last_Layer + 1));
      Sha256.Update (Ctx, LE64 (P.Ninput));
      Sha256.Update (Ctx, LE64 (P.Npublic));
      Sha256.Update (Ctx, LE64 (Subfield_Boundary));
      for J in 0 .. P.Last_Layer loop
         Sha256.Update (Ctx, LE64 (P.Layers (J).NW_In));
         Sha256.Update (Ctx, LE64 (P.Layers (J).Logw));
         Sha256.Update (Ctx, LE64 (PC.Layer_Len (P, J)));
         C := PC.Start (P, J);
         PC.Lemma_Walked_Start (P, J);
         for K in 1 .. PC.Layer_Len (P, J) loop
            pragma Loop_Invariant (Proof_Only => PC.Walked (P, J, K - 1, C));
            PC.Lemma_Walked_Step (P, J, K, C);
            T := PC.Term_Of (P, C);
            Sha256.Update (Ctx, LE64 (T.G));
            Sha256.Update (Ctx, LE64 (T.H0));
            Sha256.Update (Ctx, LE64 (T.H1));
            Sha256.Update (Ctx, SA.F.To_Bytes (T.K));
            C := PC.Step (P, C);
         end loop;
      end loop;
      return Sha256.Digest (Ctx);
   end Compute_Id_P;

   procedure Read_Packed
     (B      : Byte_Array;
      Pinned : Boolean;
      Pin    : Bytes_32;
      P      : out Packed_Access;
      H      : out Header;
      St     : out Status)
   is
      Cnt, Again : P_Counts;
      Id : Bytes_32;
      Good : Boolean;
   begin
      P := null;
      H := Null_Header;
      Walk_P (B, null, Cnt, St);
      if St /= Ok then
         return;
      end if;
      P := new Packed_Circuit'
        (Last_Layer => Cnt.NL - 1,
         NT         => Cnt.NT,
         NC         => Cnt.Nconst,
         ND         => Cnt.ND,
         NS         => Cnt.NS,
         NE         => Cnt.NE,
         NK         => Cnt.NK,
         Noutput    => Cnt.Noutput,
         Ninput     => Cnt.Ninput,
         Npublic    => Cnt.Npublic,
         Layers     => [others => (Logw => 0, NW_In => 0, First => 1,
                                   Last => 0)],
         Spans      => [others => (First => 1, Last => 0)],
         Constants  => [others => SA.Zero],
         Deltas     => [others => (DG => 0, DH0 => 0, DH1 => 0, K => 1)],
         Seg_Start  => [others => 1],
         Seg_Len    => [others => 0],
         Entries    => [others => 1],
         Tokens     => [others => 1]);
      Walk_P (B, P, Again, St);
      if St /= Ok then
         Free_Packed (P);
         return;
      end if;
      --  The two walks read the same bytes, and the second fills what the
      --  first counted; a disagreement is a defect of this unit, reported
      --  rather than trusted.
      if Again /= Cnt
        or else not PC.Indices_Ok (P.all)
        or else not PC.Layers_Ok (P.all)
      then
         Free_Packed (P);
         St := Bad_Index;
         return;
      end if;
      Check_Counts (P.all, Good);
      if not Good then
         Free_Packed (P);
         St := Bad_Index;
         return;
      end if;
      Check_Wires (P.all, Good);
      if not Good then
         Free_Packed (P);
         St := Bad_Index;
         return;
      end if;
      PC.Lemma_Valid_Intro (P.all);
      if not Shape_Ok (P.all) then
         Free_Packed (P);
         St := Not_Well_Formed;
         return;
      end if;
      Check_Fits (P.all, Good);
      if not Good then
         Free_Packed (P);
         St := Not_Well_Formed;
         return;
      end if;
      Lemma_Well_Formed (P.all);
      Check_Premises_P (P.all, St);
      if St /= Ok then
         Free_Packed (P);
         return;
      end if;
      Id := B (Cnt.Id_Pos .. Cnt.Id_Pos + 31);
      if (if Pinned then Id /= Pin else Compute_Id_P (P.all, Cnt.Sfb) /= Id)
      then
         Free_Packed (P);
         St := Id_Mismatch;
         return;
      end if;
      H := (Field_Id => Field_Id, Subfield_Boundary => Cnt.Sfb, Id => Id);
   end Read_Packed;

end Circuit_Reader;
