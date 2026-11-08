pragma SPARK_Mode (On);

package body Mdoc_Inputs is

   --  The element 2 of GF(2^128), the pad of a short date.
   Two : constant GF2_128.Element := (Limbs => [0 => 2, 1 => 0]);

   --  The CBOR text "elementValue": 6C, then the twelve characters.
   Element_Value : constant Byte_Array (0 .. 12) :=
     [16#6C#,
      Character'Pos ('e'), Character'Pos ('l'), Character'Pos ('e'),
      Character'Pos ('m'), Character'Pos ('e'), Character'Pos ('n'),
      Character'Pos ('t'), Character'Pos ('V'), Character'Pos ('a'),
      Character'Pos ('l'), Character'Pos ('u'), Character'Pos ('e')];

   ----------------------------------------------------------------------
   --  Pushing on the hash circuit's array
   ----------------------------------------------------------------------

   --  The N low bits of V, least significant first, as One or Zero.
   procedure Push_Bits
     (Pub : in out SAH.Element_Array;
      Pos : in out Natural;
      V   : Unsigned_64;
      N   : Natural)
   with
     Pre  => Pub'First = 0 and then N <= 64 and then Pos <= Pub'Length - N,
     Post => Pos = Pos'Old + N
             and then (for all I in 0 .. Pos'Old - 1 => Pub (I) = Pub'Old (I));

   procedure Push_Bits
     (Pub : in out SAH.Element_Array;
      Pos : in out Natural;
      V   : Unsigned_64;
      N   : Natural)
   is
   begin
      for J in 0 .. N - 1 loop
         pragma Loop_Invariant (Pos = Pos'Loop_Entry + J);
         pragma Loop_Invariant
           (for all I in 0 .. Pos'Loop_Entry - 1 =>
              Pub (I) = Pub'Loop_Entry (I));
         Pub (Pos) := (if (Shift_Right (V, J) and 1) = 1 then SAH.One
                       else SAH.Zero);
         Pos := Pos + 1;
      end loop;
   end Push_Bits;

   --  Each byte of D as eight bits.
   procedure Push_Bytes
     (Pub : in out SAH.Element_Array;
      Pos : in out Natural;
      D   : Byte_Array)
   with
     Pre  => Pub'First = 0 and then D'Length <= 2**16
             and then Pos <= Pub'Length - 8 * D'Length,
     Post => Pos = Pos'Old + 8 * D'Length
             and then (for all I in 0 .. Pos'Old - 1 => Pub (I) = Pub'Old (I));

   procedure Push_Bytes
     (Pub : in out SAH.Element_Array;
      Pos : in out Natural;
      D   : Byte_Array)
   is
   begin
      for K in D'Range loop
         pragma Loop_Invariant (Pos = Pos'Loop_Entry + 8 * (K - D'First));
         pragma Loop_Invariant
           (for all I in 0 .. Pos'Loop_Entry - 1 =>
              Pub (I) = Pub'Loop_Entry (I));
         Push_Bits (Pub, Pos, Unsigned_64 (D (K)), 8);
      end loop;
   end Push_Bytes;

   --  Count copies of E.
   procedure Push_Pad
     (Pub   : in out SAH.Element_Array;
      Pos   : in out Natural;
      E     : GF2_128.Element;
      Count : Natural)
   with
     Pre  => Pub'First = 0 and then Pos <= Pub'Length - Count,
     Post => Pos = Pos'Old + Count
             and then (for all I in 0 .. Pos'Old - 1 => Pub (I) = Pub'Old (I));

   procedure Push_Pad
     (Pub   : in out SAH.Element_Array;
      Pos   : in out Natural;
      E     : GF2_128.Element;
      Count : Natural)
   is
   begin
      for J in 0 .. Count - 1 loop
         pragma Loop_Invariant (Pos = Pos'Loop_Entry + J);
         pragma Loop_Invariant
           (for all I in 0 .. Pos'Loop_Entry - 1 =>
              Pub (I) = Pub'Loop_Entry (I));
         Pub (Pos) := E;
         Pos := Pos + 1;
      end loop;
   end Push_Pad;

   --  One attribute, Per_Attribute (Version) elements.
   procedure Push_Attribute
     (Version : Version_Number;
      A       : Attribute;
      Pub     : in out SAH.Element_Array;
      Pos     : in out Natural)
   with
     Pre  => Pub'First = 0 and then Fits (Version, A)
             and then Pos <= Pub'Length - Per_Attribute (Version),
     Post => Pos = Pos'Old + Per_Attribute (Version)
             and then (for all I in 0 .. Pos'Old - 1 => Pub (I) = Pub'Old (I));

   procedure Push_Attribute
     (Version : Version_Number;
      A       : Attribute;
      Pub     : in out SAH.Element_Array;
      Pos     : in out Natural)
   is
      Head : constant Byte_Array :=
        Cbor_Encode.Head (Cbor_Encode.Text_Major, A.Id_Len);
      Hl   : constant Positive := Cbor_Encode.Head_Len (A.Id_Len);
   begin
      if Version = 7 then
         Push_Bytes (Pub, Pos, Head);
         Push_Bytes (Pub, Pos, A.Id (0 .. A.Id_Len - 1));
         Push_Pad (Pub, Pos, GF2_128.Zero, (32 - Hl - A.Id_Len) * 8);
         Push_Bytes (Pub, Pos, A.Value (0 .. A.Value_Len - 1));
         Push_Pad (Pub, Pos, GF2_128.Zero, (64 - A.Value_Len) * 8);
         Push_Bits (Pub, Pos, Unsigned_64 (1 + 17 + 1 + A.Id_Len), 8);
         Push_Bits (Pub, Pos, Unsigned_64 (A.Value_Len + 12 + 1), 8);
      else
         declare
            Len : constant Natural := Hl + A.Id_Len + 13 + A.Value_Len;
         begin
            Push_Bytes (Pub, Pos, Head);
            Push_Bytes (Pub, Pos, A.Id (0 .. A.Id_Len - 1));
            Push_Bytes (Pub, Pos, Element_Value);
            Push_Bytes (Pub, Pos, A.Value (0 .. A.Value_Len - 1));
            Push_Pad (Pub, Pos, GF2_128.Zero, (96 - Len) * 8);
            Push_Bits (Pub, Pos, Unsigned_64 (Len), 8);
         end;
      end if;
   end Push_Attribute;

   procedure Hash_Inputs
     (Version : Version_Number;
      Attrs   : Attribute_List;
      Now     : Byte_Array;
      T       : Mdoc_Mac.Tags;
      Av      : GF2_128.Element;
      Pub     : out SAH.Element_Array)
   is
      Pos : Natural := 1;
   begin
      Pub := [others => GF2_128.Zero];
      Pub (0) := SAH.One;
      for K in Attrs'Range loop
         pragma Loop_Invariant
           (Pos = 1 + (K - Attrs'First) * Per_Attribute (Version));
         pragma Loop_Invariant (Pub (0) = SAH.One);
         Push_Attribute (Version, Attrs (K), Pub, Pos);
      end loop;
      Push_Bytes (Pub, Pos, Now);
      Push_Pad (Pub, Pos, Two, (Now_Len - Now'Length) * 8);
      for I in Mdoc_Mac.Tag_Index loop
         pragma Loop_Invariant (Pos = Pub'Last - 6 + I);
         pragma Loop_Invariant (Pub (0) = SAH.One);
         pragma Loop_Invariant
           (for all J in 0 .. I - 1 => Pub (Pub'Last - 6 + J) = T (J));
         Pub (Pos) := T (I);
         Pos := Pos + 1;
      end loop;
      Pub (Pos) := Av;
   end Hash_Inputs;

   ----------------------------------------------------------------------
   --  The signature circuit's array
   ----------------------------------------------------------------------

   --  The 64 bits of a limb, least significant first, as One or Zero.
   procedure Push_Limb
     (Pub : in out SAP.Element_Array;
      Pos : in out Natural;
      V   : Unsigned_64)
   with
     Pre  => Pub'First = 0 and then Pos <= Pub'Length - 64,
     Post => Pos = Pos'Old + 64
             and then (for all I in 0 .. Pos'Old - 1 => Pub (I) = Pub'Old (I));

   procedure Push_Limb
     (Pub : in out SAP.Element_Array;
      Pos : in out Natural;
      V   : Unsigned_64)
   is
   begin
      for J in 0 .. 63 loop
         pragma Loop_Invariant (Pos = Pos'Loop_Entry + J);
         pragma Loop_Invariant
           (for all I in 0 .. Pos'Loop_Entry - 1 =>
              Pub (I) = Pub'Loop_Entry (I));
         Pub (Pos) := (if (Shift_Right (V, J) and 1) = 1 then SAP.One
                       else SAP.Zero);
         Pos := Pos + 1;
      end loop;
   end Push_Limb;

   procedure Sig_Inputs
     (Pk_X, Pk_Y, E2 : P256_Field.Element;
      T              : Mdoc_Mac.Tags;
      Av             : GF2_128.Element;
      Pub            : out SAP.Element_Array)
   is
      Pos : Natural := 4;
   begin
      Pub := [others => SAP.Zero];
      Pub (0) := SAP.One;
      Pub (1) := Pk_X;
      Pub (2) := Pk_Y;
      Pub (3) := E2;
      for I in Mdoc_Mac.Tag_Index loop
         pragma Loop_Invariant (Pos = 4 + 128 * I);
         pragma Loop_Invariant
           (Pub (0) = SAP.One and then Pub (1) = Pk_X and then Pub (2) = Pk_Y
            and then Pub (3) = E2);
         Push_Limb (Pub, Pos, T (I).Limbs (0));
         Push_Limb (Pub, Pos, T (I).Limbs (1));
      end loop;
      Push_Limb (Pub, Pos, Av.Limbs (0));
      Push_Limb (Pub, Pos, Av.Limbs (1));
   end Sig_Inputs;

   ----------------------------------------------------------------------
   --  The witness
   ----------------------------------------------------------------------

   procedure Witness_Parts
     (Priv : SAH.Element_Array;
      Ap   : out Mdoc_Mac.Pads;
      M    : out Mdoc_Mac.Messages;
      Ok   : out Boolean)
   is
      --  Every bit above bit 0 of every element, or-ed: zero exactly
      --  when every element is One or Zero.
      Bad : Unsigned_64 := 0;
   begin
      Ap := [others => [others => GF2_128.Zero]];
      M  := [others => [others => 0]];
      if Priv'Length < Message_Elements + Pad_Elements then
         Ok := False;
         return;
      end if;
      for I in Mdoc_Mac.Message_Index loop
         for J in 0 .. 31 loop
            declare
               V : Unsigned_8 := 0;
            begin
               for K in 0 .. 7 loop
                  declare
                     E : constant GF2_128.Element :=
                       Priv (I * 256 + J * 8 + K);
                  begin
                     Bad := Bad or E.Limbs (1) or (E.Limbs (0) and not 1);
                     V := V or Shift_Left (Unsigned_8 (E.Limbs (0) and 1), K);
                  end;
               end loop;
               M (I) (J) := V;
            end;
         end loop;
      end loop;
      for I in Mdoc_Mac.Message_Index loop
         pragma Loop_Invariant
           (for all I2 in 0 .. I - 1 =>
              (for all H in Mdoc_Mac.Half_Index =>
                 Ap (I2) (H) = Priv (Priv'Last - 5 + 2 * I2 + H)));
         for H in Mdoc_Mac.Half_Index loop
            pragma Loop_Invariant
              (for all I2 in 0 .. I - 1 =>
                 (for all H2 in Mdoc_Mac.Half_Index =>
                    Ap (I2) (H2) = Priv (Priv'Last - 5 + 2 * I2 + H2)));
            pragma Loop_Invariant
              (for all H2 in 0 .. H - 1 =>
                 Ap (I) (H2) = Priv (Priv'Last - 5 + 2 * I + H2));
            Ap (I) (H) := Priv (Priv'Last - 5 + 2 * I + H);
         end loop;
      end loop;
      Ok := Bad = 0;
   end Witness_Parts;

   function Sig_Pads_Match
     (Sig_Priv : SAP.Element_Array; Ap : Mdoc_Mac.Pads) return Boolean
   is
      --  One bit per mismatch, or-ed: zero exactly when every element
      --  is the pad's; no short circuit on the witness. For the provers,
      --  in ghost code that is never compiled: Same says that every
      --  element seen so far matched, and when it turns false the
      --  position of the first mismatch is kept, the witness that the
      --  quantified postcondition is false on that side.
      Mismatch : Unsigned_64 := 0;
      Same     : Boolean := True with Ghost;
      Bad_I    : Natural := 0 with Ghost;
      Bad_H    : Natural := 0 with Ghost;
      Bad_K    : Natural := 0 with Ghost;
   begin
      for I in Mdoc_Mac.Message_Index loop
         pragma Loop_Invariant ((Mismatch = 0) = Same);
         pragma Loop_Invariant
           (if Same then
              (for all I2 in 0 .. I - 1 =>
                 (for all H in Mdoc_Mac.Half_Index =>
                    (for all K in 0 .. 63 =>
                       Sig_Priv (Sig_Pad_Index (Sig_Priv, I2, H, K))
                       = Plucked (Pair (Ap (I2) (H), K))))));
         pragma Loop_Invariant
           (if not Same then
              Bad_I <= 2 and then Bad_H <= 1 and then Bad_K <= 63
              and then Sig_Priv (Sig_Pad_Index (Sig_Priv, Bad_I, Bad_H, Bad_K))
                       /= Plucked (Pair (Ap (Bad_I) (Bad_H), Bad_K)));
         for H in Mdoc_Mac.Half_Index loop
            pragma Loop_Invariant ((Mismatch = 0) = Same);
            pragma Loop_Invariant
              (if Same then
                 (for all I2 in 0 .. I - 1 =>
                    (for all H2 in Mdoc_Mac.Half_Index =>
                       (for all K in 0 .. 63 =>
                          Sig_Priv (Sig_Pad_Index (Sig_Priv, I2, H2, K))
                          = Plucked (Pair (Ap (I2) (H2), K)))))
                 and then
                 (for all H2 in 0 .. H - 1 =>
                    (for all K in 0 .. 63 =>
                       Sig_Priv (Sig_Pad_Index (Sig_Priv, I, H2, K))
                       = Plucked (Pair (Ap (I) (H2), K)))));
            pragma Loop_Invariant
              (if not Same then
                 Bad_I <= 2 and then Bad_H <= 1 and then Bad_K <= 63
                 and then Sig_Priv
                            (Sig_Pad_Index (Sig_Priv, Bad_I, Bad_H, Bad_K))
                          /= Plucked (Pair (Ap (Bad_I) (Bad_H), Bad_K)));
            for K in 0 .. 63 loop
               pragma Loop_Invariant ((Mismatch = 0) = Same);
               pragma Loop_Invariant
                 (if Same then
                    (for all I2 in 0 .. I - 1 =>
                       (for all H2 in Mdoc_Mac.Half_Index =>
                          (for all K2 in 0 .. 63 =>
                             Sig_Priv (Sig_Pad_Index (Sig_Priv, I2, H2, K2))
                             = Plucked (Pair (Ap (I2) (H2), K2)))))
                    and then
                    (for all H2 in 0 .. H - 1 =>
                       (for all K2 in 0 .. 63 =>
                          Sig_Priv (Sig_Pad_Index (Sig_Priv, I, H2, K2))
                          = Plucked (Pair (Ap (I) (H2), K2))))
                    and then
                    (for all K2 in 0 .. K - 1 =>
                       Sig_Priv (Sig_Pad_Index (Sig_Priv, I, H, K2))
                       = Plucked (Pair (Ap (I) (H), K2))));
               pragma Loop_Invariant
                 (if not Same then
                    Bad_I <= 2 and then Bad_H <= 1 and then Bad_K <= 63
                    and then Sig_Priv
                               (Sig_Pad_Index (Sig_Priv, Bad_I, Bad_H, Bad_K))
                             /= Plucked (Pair (Ap (Bad_I) (Bad_H), Bad_K)));
               declare
                  Here : constant SAP.Element :=
                    Sig_Priv (Sig_Pad_Index (Sig_Priv, I, H, K));
                  Want : constant SAP.Element :=
                    Plucked (Pair (Ap (I) (H), K));
               begin
                  Mismatch := Mismatch or Diff (Here, Want);
                  Bad_I := (if Same and then Here /= Want then I else Bad_I);
                  Bad_H := (if Same and then Here /= Want then H else Bad_H);
                  Bad_K := (if Same and then Here /= Want then K else Bad_K);
                  Same  := Same and then Here = Want;
               end;
            end loop;
         end loop;
      end loop;
      return Mismatch = 0;
   end Sig_Pads_Match;

   procedure Place_Pads
     (Hash_Priv : in out SAH.Element_Array;
      Sig_Priv  : in out SAP.Element_Array;
      Ap        : Mdoc_Mac.Pads)
   is
   begin
      for I in Mdoc_Mac.Message_Index loop
         pragma Loop_Invariant
           (for all I2 in 0 .. I - 1 =>
              (for all H in Mdoc_Mac.Half_Index =>
                 Hash_Priv (Hash_Priv'Last - 5 + 2 * I2 + H) = Ap (I2) (H)));
         for H in Mdoc_Mac.Half_Index loop
            pragma Loop_Invariant
              (for all I2 in 0 .. I - 1 =>
                 (for all H2 in Mdoc_Mac.Half_Index =>
                    Hash_Priv (Hash_Priv'Last - 5 + 2 * I2 + H2)
                    = Ap (I2) (H2)));
            pragma Loop_Invariant
              (for all H2 in 0 .. H - 1 =>
                 Hash_Priv (Hash_Priv'Last - 5 + 2 * I + H2) = Ap (I) (H2));
            Hash_Priv (Hash_Priv'Last - 5 + 2 * I + H) := Ap (I) (H);
         end loop;
      end loop;
      for I in Mdoc_Mac.Message_Index loop
         pragma Loop_Invariant
           (for all I2 in 0 .. I - 1 =>
              (for all H in Mdoc_Mac.Half_Index =>
                 (for all K in 0 .. 63 =>
                    Sig_Priv (Sig_Pad_Index (Sig_Priv, I2, H, K))
                    = Plucked (Pair (Ap (I2) (H), K)))));
         for H in Mdoc_Mac.Half_Index loop
            pragma Loop_Invariant
              (for all I2 in 0 .. I - 1 =>
                 (for all H2 in Mdoc_Mac.Half_Index =>
                    (for all K in 0 .. 63 =>
                       Sig_Priv (Sig_Pad_Index (Sig_Priv, I2, H2, K))
                       = Plucked (Pair (Ap (I2) (H2), K)))));
            pragma Loop_Invariant
              (for all H2 in 0 .. H - 1 =>
                 (for all K in 0 .. 63 =>
                    Sig_Priv (Sig_Pad_Index (Sig_Priv, I, H2, K))
                    = Plucked (Pair (Ap (I) (H2), K))));
            for K in 0 .. 63 loop
               pragma Loop_Invariant
                 (for all I2 in 0 .. I - 1 =>
                    (for all H2 in Mdoc_Mac.Half_Index =>
                       (for all K2 in 0 .. 63 =>
                          Sig_Priv (Sig_Pad_Index (Sig_Priv, I2, H2, K2))
                          = Plucked (Pair (Ap (I2) (H2), K2)))));
               pragma Loop_Invariant
                 (for all H2 in 0 .. H - 1 =>
                    (for all K2 in 0 .. 63 =>
                       Sig_Priv (Sig_Pad_Index (Sig_Priv, I, H2, K2))
                       = Plucked (Pair (Ap (I) (H2), K2))));
               pragma Loop_Invariant
                 (for all K2 in 0 .. K - 1 =>
                    Sig_Priv (Sig_Pad_Index (Sig_Priv, I, H, K2))
                    = Plucked (Pair (Ap (I) (H), K2)));
               Sig_Priv (Sig_Pad_Index (Sig_Priv, I, H, K)) :=
                 Plucked (Pair (Ap (I) (H), K));
            end loop;
         end loop;
      end loop;
   end Place_Pads;

end Mdoc_Inputs;
