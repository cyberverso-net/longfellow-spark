pragma SPARK_Mode (On);

with Sha256;

package body Mdoc_Parse is

   use Cbor_Parse;

   subtype Element_Count is Cbor_Parse.Element_Count;
   subtype Element_Index is Cbor_Parse.Element_Index;
   subtype Document is Cbor_Parse.Document;

   --  K_COSE_SIGN1_SIGNING_HEADER of upstream's cbor/constants.rs: the
   --  array of four, "Signature1", the protected header 43 A1 01 26
   --  (ES256), the empty external data 40.
   Signing_Header : constant Byte_Array (0 .. Signing_Header_Len - 1) :=
     [16#84#, 16#6A#,
      16#53#, 16#69#, 16#67#, 16#6E#, 16#61#, 16#74#, 16#75#, 16#72#,
      16#65#, 16#31#,
      16#43#, 16#A1#, 16#01#, 16#26#, 16#40#];

   -------------------------------------------------------------------
   --  Lookups with upstream's statuses. Each helper leaves Result as it
   --  is on success and sets it on a failure, so that the walk below
   --  reads as upstream's sequence of "?" operators.
   -------------------------------------------------------------------

   --  required_map_value: the value of the unique text key Key of the
   --  map M, 0 with the status otherwise.
   procedure Need_Value
     (Doc    : Document;
      Data   : Byte_Array;
      M      : Element_Count;
      Key    : String;
      Val    : out Element_Count;
      Result : in out Status)
   with
     Global => null,
     Pre    => Valid (Doc) and then M <= Doc.Count
               and then Data'Length = Doc.Length,
     Post   => Val <= Doc.Count
               and then (if Result'Old /= Ok then Result = Result'Old)
               and then (if Result = Ok then Val > 0)
   is
      K : Element_Count;
      L : Lookup;
   begin
      Val := 0;
      if Result /= Ok then
         return;
      end if;
      if M = 0 then
         Result := Unexpected_Type;
         return;
      end if;
      Map_Text_Entry (Doc, Data, M, Key, K, Val, L);
      case L is
         when Found     => null;
         when Missing   => Result := Missing_Field;
         when Duplicate => Result := Duplicate_Field;
         when Not_A_Map => Result := Unexpected_Type;
      end case;
      if Result /= Ok then
         Val := 0;
      end if;
   end Need_Value;

   --  required_map_key: the position of the unique text key Key of the
   --  map M (CborIndexVal.k), with the value element.
   procedure Need_Key
     (Doc    : Document;
      Data   : Byte_Array;
      M      : Element_Count;
      Key    : String;
      Pos    : out Position;
      Val    : out Element_Count;
      Result : in out Status)
   with
     Global => null,
     Pre    => Valid (Doc) and then M <= Doc.Count
               and then Data'Length = Doc.Length,
     Post   => Val <= Doc.Count
               and then (if Result'Old /= Ok then Result = Result'Old)
               and then (if Result = Ok then
                           Val > 0 and then Pos < Doc.Length)
   is
      K : Element_Count;
      L : Lookup;
   begin
      Pos := 0;
      Val := 0;
      if Result /= Ok then
         return;
      end if;
      if M = 0 then
         Result := Unexpected_Type;
         return;
      end if;
      Map_Text_Entry (Doc, Data, M, Key, K, Val, L);
      case L is
         when Found     => null;
         when Missing   => Result := Missing_Field;
         when Duplicate => Result := Duplicate_Field;
         when Not_A_Map => Result := Unexpected_Type;
      end case;
      if Result /= Ok then
         Val := 0;
         return;
      end if;
      --  A key has at least its head: Start < Content <= Stop <= Length.
      Pos := Doc.Elements (K).Start;
   end Need_Key;

   --  required_cose_sign1_array: the array E, or the array under tag
   --  18; 0 with Unexpected_Type otherwise.
   procedure Cose_Array
     (Doc    : Document;
      E      : Element_Count;
      Arr    : out Element_Count;
      Result : in out Status)
   with
     Global => null,
     Pre    => Valid (Doc) and then E <= Doc.Count,
     Post   => Arr <= Doc.Count
               and then (if Result'Old /= Ok then Result = Result'Old)
               and then (if Result = Ok then Arr > 0)
   is
   begin
      Arr := 0;
      if Result /= Ok then
         return;
      end if;
      if E = 0 then
         Result := Unexpected_Type;
         return;
      end if;
      if Doc.Elements (E).Kind = Array_Kind then
         Arr := E;
      else
         Arr := Tag_Child (Doc, E, 18);
         if Arr = 0 or else Doc.Elements (Arr).Kind /= Array_Kind then
            Arr := 0;
            Result := Unexpected_Type;
         end if;
      end if;
   end Cose_Array;

   --  Element I of the array Arr, which must be a byte string
   --  (required_bytes after get (I)): Missing_Field, Unexpected_Type.
   procedure Need_Bytes_Item
     (Doc    : Document;
      Arr    : Element_Count;
      I      : Natural;
      Bs     : out Element_Count;
      Result : in out Status)
   with
     Global => null,
     Pre    => Valid (Doc) and then Arr <= Doc.Count,
     Post   => Bs <= Doc.Count
               and then (if Result'Old /= Ok then Result = Result'Old)
               and then (if Result = Ok then
                           Bs > 0 and then Doc.Elements (Bs).Kind = Byte_String)
   is
   begin
      Bs := 0;
      if Result /= Ok or else Arr = 0 then
         if Result = Ok then
            Result := Unexpected_Type;
         end if;
         return;
      end if;
      Bs := Array_Item (Doc, Arr, I);
      if Bs = 0 then
         Result := Missing_Field;
      elsif Doc.Elements (Bs).Kind /= Byte_String then
         Bs := 0;
         Result := Unexpected_Type;
      end if;
   end Need_Bytes_Item;

   --  The 32 bytes of Data from From into B.
   procedure Copy_32
     (Data : Byte_Array; From : Natural; B : out Bytes_32)
   with
     Global => null,
     Pre    => From >= Data'First and then Data'Last >= From
               and then Data'Last - From >= 31
   is
   begin
      for I in 0 .. 31 loop
         B (I) := Data (From + I);
      end loop;
   end Copy_32;

   --  parse_signature: a byte string of exactly 64 bytes, r then s.
   procedure Signature
     (Doc    : Document;
      Data   : Byte_Array;
      Bs     : Element_Count;
      R, S   : out Bytes_32;
      Result : in out Status)
   with
     Global => null,
     Pre    => Valid (Doc) and then Bs <= Doc.Count
               and then Data'Length = Doc.Length
               and then (if Result = Ok then
                           Bs > 0 and then Doc.Elements (Bs).Kind = Byte_String),
     Post   => (if Result'Old /= Ok then Result = Result'Old)
   is
      El : Element;
   begin
      R := [others => 0];
      S := [others => 0];
      if Result /= Ok then
         return;
      end if;
      El := Doc.Elements (Bs);
      if El.Stop - El.Content /= 64 then
         Result := Invalid_Length;
         return;
      end if;
      Copy_32 (Data, Data'First + El.Content, R);
      Copy_32 (Data, Data'First + El.Content + 32, S);
   end Signature;

   --  required_device_coordinate: the unique integer key -2 or -3 of
   --  the COSE_Key map, a byte string read as upstream's from_bytes_be
   --  reads it into four limbs: a shorter string is left-padded, a
   --  longer one keeps its last 32 bytes (the reversed bytes are
   --  resized to 32).
   procedure Coordinate
     (Doc       : Document;
      Data      : Byte_Array;
      M         : Element_Count;
      Magnitude : Unsigned_64;
      C         : out Bytes_32;
      Result    : in out Status)
   with
     Global => null,
     Pre    => Valid (Doc) and then M <= Doc.Count
               and then Data'Length = Doc.Length,
     Post   => (if Result'Old /= Ok then Result = Result'Old)
   is
      K, V  : Element_Count;
      Found : Boolean := False;
      El    : Element;
      Len   : Natural;
   begin
      C := [others => 0];
      if Result /= Ok then
         return;
      end if;
      if M = 0 or else Doc.Elements (M).Kind /= Map_Kind then
         Result := Unexpected_Type;
         return;
      end if;
      --  Upstream walks the pairs and, at each matching key, reports a
      --  second match before anything else and a value that is not a
      --  byte string at once; so a non-string first value is
      --  Unexpected_Type even when a duplicate follows.
      K := Doc.Elements (M).Child;
      while K /= 0 loop
         pragma Loop_Invariant (K <= Doc.Count);
         pragma Loop_Invariant (if K > 0 then Doc.Elements (K).Parent = M);
         pragma Loop_Variant (Increases => K);
         V := Doc.Elements (K).Next;
         exit when V = 0;
         if Doc.Elements (K).Kind = Negative_Int
           and then Doc.Elements (K).Value = Magnitude
         then
            if Found then
               Result := Duplicate_Field;
               return;
            end if;
            El := Doc.Elements (V);
            if El.Kind /= Byte_String then
               Result := Unexpected_Type;
               return;
            end if;
            Found := True;
            --  from_bytes_be: reversed and resized to 32 bytes, so a
            --  longer string keeps its last 32, a shorter one is
            --  left-padded.
            Len := El.Stop - El.Content;
            if Len >= 32 then
               Copy_32 (Data, Data'First + El.Stop - 32, C);
            else
               C := [others => 0];
               for I in 0 .. Len - 1 loop
                  C (32 - Len + I) := Data (Data'First + El.Content + I);
               end loop;
            end if;
         end if;
         K := Doc.Elements (V).Next;
      end loop;
      if not Found then
         Result := Missing_Field;
      end if;
   end Coordinate;

   -------------------------------------------------------------------
   --  validate_mso_layout
   -------------------------------------------------------------------

   procedure Validate_Mso_Layout
     (Mdoc    : Byte_Array;
      Start   : Position;      --  of the wrapped MSO, in Mdoc
      Len     : Position;      --  of the wrapped MSO
      Map_Len : Position;      --  of the map bytes under the tag
      Version : Version_Number;
      Result  : in out Status)
   with
     Global => null,
     Pre    => Mdoc'Length <= Cbor_Parse.Max_Bytes
               and then Start + Len <= Mdoc'Length
               and then Version in 6 .. 7,
     Post   => (if Result'Old /= Ok then Result = Result'Old)
               and then (if Result = Ok then
                           Len = Map_Len + Mso_Head_Len
                           and then Map_Len >= Min_Mso_Map
                           and then Len <= Max_Wrapped_Mso (Version))
   is
      Encoded : Natural;
   begin
      if Result /= Ok then
         return;
      end if;
      --  The padded message must fit the blocks: the prefix, the two
      --  bytes of length, the MSO, the byte 16#80# and eight bytes of
      --  length; and the length head is two bytes.
      if Cose_Prefix_Len + 2 + Len > 64 * Max_Blocks (Version) - 9
        or else Len > 65_535
      then
         Result := Too_Big;
         return;
      end if;
      if Map_Len < Min_Mso_Map
        or else Len < 5
        or else Mdoc (Mdoc'First + Start) /= 16#D8#
        or else Mdoc (Mdoc'First + Start + 1) /= 16#18#
        or else Mdoc (Mdoc'First + Start + 2) /= 16#59#
        or else Len /= Map_Len + Mso_Head_Len
      then
         Result := Unsupported_Encoding;
         return;
      end if;
      Encoded := 256 * Natural (Mdoc (Mdoc'First + Start + 3))
                 + Natural (Mdoc (Mdoc'First + Start + 4));
      if Encoded /= Map_Len then
         Result := Unsupported_Encoding;
      end if;
   end Validate_Mso_Layout;

   -------------------------------------------------------------------
   --  The signed message and its digest
   -------------------------------------------------------------------

   procedure Signed_Message
     (Mdoc : Byte_Array;
      P    : Parsed_Mdoc;
      Msg  : out Byte_Array;
      Len  : out Natural)
   is
   begin
      Msg := [others => 0];
      Msg (0 .. Signing_Header_Len - 1) := Signing_Header;
      Msg (Signing_Header_Len) := 16#59#;
      Msg (Signing_Header_Len + 1) := Unsigned_8 (P.Mso_Len / 256);
      Msg (Signing_Header_Len + 2) := Unsigned_8 (P.Mso_Len mod 256);
      for I in 0 .. P.Mso_Len - 1 loop
         Msg (Signing_Header_Len + 3 + I) := Mdoc (Mdoc'First + P.Mso_Start + I);
      end loop;
      Len := Message_Length (P);
   end Signed_Message;

   --  The SHA-256 of the signed message, streamed: the header, the
   --  three-byte head, the wrapped MSO.
   function Issuer_Digest
     (Mdoc : Byte_Array; Start, Len : Position) return Bytes_32
   with
     Global => null,
     Pre    => Mdoc'Length <= Cbor_Parse.Max_Bytes
               and then Start + Len <= Mdoc'Length and then Len <= 65_535
   is
      Ctx  : Sha256.Context := Sha256.Initial;
      Head : constant Byte_Array (0 .. 2) :=
        [16#59#, Unsigned_8 (Len / 256), Unsigned_8 (Len mod 256)];
   begin
      Sha256.Update (Ctx, Signing_Header);
      Sha256.Update (Ctx, Head);
      if Len > 0 then
         Sha256.Update (Ctx, Mdoc (Mdoc'First + Start .. Mdoc'First + Start + Len - 1));
      end if;
      return Sha256.Digest (Ctx);
   end Issuer_Digest;

   -------------------------------------------------------------------
   --  extract_attrs and compute_witness
   -------------------------------------------------------------------

   --  One issuer-signed item: the element Item_El of the root table
   --  (a tag 24 over a byte string), the namespace key Ns_El (a text),
   --  the valueDigests element VD of the MSO table.
   procedure One_Item
     (Mdoc     : Byte_Array;
      Root     : Document;
      Item_El  : Element_Index;
      Ns_El    : Element_Index;
      Mso      : Document;
      Mso_Map  : Byte_Array;
      VD       : Element_Index;
      It       : out Item;
      Result   : in out Status;
      Detail   : in out Cbor_Parse.Status)
   with
     Global => null,
     Pre    => Mdoc'Length <= Cbor_Parse.Max_Bytes
               and then Valid (Root) and then Root.Length = Mdoc'Length
               and then Item_El <= Root.Count and then Ns_El <= Root.Count
               and then Valid (Mso) and then Mso_Map'Length = Mso.Length
               and then Mso_Map'Length <= Cbor_Parse.Max_Bytes
               and then VD <= Mso.Count,
     Post   => (if Result = Ok then
                  It.Name_Start + It.Name_Len <= Mdoc'Length
                  and then It.Value_Start + It.Value_Len <= Mdoc'Length
                  and then It.Item_Start + It.Item_Len <= Mdoc'Length
                  and then It.Digest_Offset < Mso.Length)
   is
      Bs       : Element_Count;
      Inner    : Document;
      R        : Cbor_Parse.Status;
      Id_El    : Element_Count;
      Val_El   : Element_Count;
      K, V     : Element_Count;
      Ns_Map   : Element_Count;
      Dg_K     : Element_Count;
      Dg_V     : Element_Count;
      L        : Lookup;
      Slot_Of  : array (Slot_Index) of Natural range 0 .. 4 := [others => 4];
      Pair     : Natural;
      Digest_Id : Unsigned_64 := 0;
      Have_Id  : Boolean := False;
      Prefix   : Natural;
      Off      : Natural;
      Inner_First : Natural;
      Inner_Len   : Natural;
   begin
      It := (others => <>);
      if Result /= Ok then
         return;
      end if;
      --  required_tagged_bytes: tag 24 over a byte string.
      Bs := Tag_Child (Root, Item_El, 24);
      if Bs = 0 or else Root.Elements (Bs).Kind /= Byte_String then
         Result := Unexpected_Type;
         return;
      end if;
      It.Item_Start := Root.Elements (Item_El).Start;
      It.Item_Len := Root.Elements (Item_El).Stop - Root.Elements (Item_El).Start;
      Inner_First := Root.Elements (Bs).Content;
      Inner_Len := Root.Elements (Bs).Stop - Root.Elements (Bs).Content;
      --  The byte string is the tag's child, so it lies inside the tag
      --  (Valid): the bytes before the map are the tag and the head.
      pragma Assert (Root.Elements (Bs).Parent = Item_El);
      pragma Assert (Root.Elements (Item_El).Content <= Root.Elements (Bs).Start);
      pragma Assert (Root.Elements (Bs).Stop <= Root.Elements (Item_El).Stop);
      pragma Assert (Inner_Len <= It.Item_Len);
      --  The item's map, parsed on its own bytes.
      Parse_Exact (Mdoc (Mdoc'First + Inner_First
                         .. Mdoc'First + Inner_First + Inner_Len - 1),
                   Inner, R);
      if R /= Ok then
         Result := Cbor_Item;
         Detail := R;
         return;
      end if;
      declare
         --  A copy, since SPARK does not rename a slice with variable
         --  bounds; an item is small (upstream bounds it at 255 bytes
         --  for the witness; here only by the document).
         Bytes_Inner : constant Byte_Array :=
           Mdoc (Mdoc'First + Inner_First .. Mdoc'First + Inner_First + Inner_Len - 1);
      begin
         Need_Value (Inner, Bytes_Inner, 1, "elementIdentifier", Id_El, Result);
         if Result /= Ok then
            return;
         end if;
         if Inner.Elements (Id_El).Kind /= Text_String then
            Result := Unexpected_Type;
            return;
         end if;
         It.Name_Start := Inner_First + Inner.Elements (Id_El).Content;
         It.Name_Len := Inner.Elements (Id_El).Stop - Inner.Elements (Id_El).Content;
         Need_Value (Inner, Bytes_Inner, 1, "elementValue", Val_El, Result);
         if Result /= Ok then
            return;
         end if;
         It.Value_Start := Inner_First + Inner.Elements (Val_El).Start;
         It.Value_Len := Inner.Elements (Val_El).Stop - Inner.Elements (Val_El).Start;
         --  compute_witness: a map of exactly four entries.
         if Inner.Elements (1).Kind /= Map_Kind then
            Result := Unexpected_Type;
            return;
         end if;
         if Inner.Elements (1).Count /= 8 then
            Result := Invalid_Length;
            return;
         end if;
         K := Inner.Elements (1).Child;
         Pair := 0;
         while K /= 0 and then Pair < 4 loop
            pragma Loop_Invariant (K <= Inner.Count);
            pragma Loop_Invariant (Pair <= 3);
            pragma Loop_Variant (Increases => K);
            V := Inner.Elements (K).Next;
            exit when V = 0;
            if Inner.Elements (K).Kind /= Text_String then
               Result := Unexpected_Type;
               return;
            end if;
            It.Length (Slot_Index (Pair)) :=
              Inner.Elements (V).Stop - Inner.Elements (K).Start;
            if Text_Equals (Inner, Bytes_Inner, K, "digestID") then
               if Slot_Of (0) /= 4 then
                  Result := Duplicate_Field;
                  return;
               end if;
               Slot_Of (0) := Pair;
               case Inner.Elements (V).Kind is
                  when Unsigned_Int =>
                     Digest_Id := Inner.Elements (V).Value;
                     Have_Id := True;
                  when Negative_Int =>
                     Result := Invalid_Value;
                     return;
                  when others =>
                     Result := Unexpected_Type;
                     return;
               end case;
            elsif Text_Equals (Inner, Bytes_Inner, K, "random") then
               if Slot_Of (1) /= 4 then
                  Result := Duplicate_Field;
                  return;
               end if;
               Slot_Of (1) := Pair;
            elsif Text_Equals (Inner, Bytes_Inner, K, "elementIdentifier") then
               if Slot_Of (2) /= 4 then
                  Result := Duplicate_Field;
                  return;
               end if;
               Slot_Of (2) := Pair;
            elsif Text_Equals (Inner, Bytes_Inner, K, "elementValue") then
               if Slot_Of (3) /= 4 then
                  Result := Duplicate_Field;
                  return;
               end if;
               Slot_Of (3) := Pair;
            else
               Result := Unknown_Field;
               return;
            end if;
            if Pair = 0 then
               --  The first key's position inside the item's bytes.
               Off := Inner.Elements (K).Start;
               --  The bytes before the map: the tag and the string head.
               Prefix := It.Item_Len - Inner_Len;
               Off := Prefix + Off;
               if Off > Max_Bytes then
                  Result := Invalid_Value;
                  return;
               end if;
               It.Slot (0) := Off;
            end if;
            Pair := Pair + 1;
            K := Inner.Elements (V).Next;
         end loop;
      end;
      for S in Slot_Index loop
         if Slot_Of (S) = 4 then
            Result := Missing_Field;
            return;
         end if;
      end loop;
      if not Have_Id then
         Result := Missing_Field;
         return;
      end if;
      It.Permutation := 64 * Slot_Of (3) + 16 * Slot_Of (2) + 4 * Slot_Of (1) + Slot_Of (0);
      --  slot_position [1 .. 3]: each after the previous entry.
      for S in Slot_Index range 1 .. 3 loop
         Off := It.Slot (S - 1) + It.Length (S - 1);
         if Off > Max_Bytes then
            Result := Invalid_Value;
            return;
         end if;
         It.Slot (S) := Off;
      end loop;
      It.Digest_Id := Digest_Id;
      --  required_digest_offset: valueDigests [namespace] [digestID].
      Map_Bytes_Entry (Mso, Mso_Map, VD,
                       Mdoc (Mdoc'First + Root.Elements (Ns_El).Content
                             .. Mdoc'First + Root.Elements (Ns_El).Stop - 1),
                       K, Ns_Map, L);
      case L is
         when Found     => null;
         when Missing   => Result := Missing_Field; return;
         when Duplicate => Result := Duplicate_Field; return;
         when Not_A_Map => Result := Unexpected_Type; return;
      end case;
      Map_Int_Entry (Mso, Ns_Map, False, Digest_Id, Dg_K, Dg_V, L);
      case L is
         when Found     => null;
         when Missing   => Result := Missing_Field; return;
         when Duplicate => Result := Duplicate_Field; return;
         when Not_A_Map => Result := Unexpected_Type; return;
      end case;
      It.Digest_Offset := Mso.Elements (Dg_V).Start;
   end One_Item;

   -------------------------------------------------------------------
   --  parse_mdoc
   -------------------------------------------------------------------

   procedure Parse
     (Mdoc        : Byte_Array;
      Transcript  : Byte_Array;
      Doc_Type    : Byte_Array;
      Version     : Version_Number;
      P           : out Parsed_Mdoc;
      Result      : out Status;
      Cbor_Detail : out Cbor_Parse.Status)
   is
      Root    : Document;
      Wrap    : Document;
      Mso     : Document;
      R       : Cbor_Parse.Status;
      Docs    : Element_Count;
      Doc0    : Element_Count;
      Issuer_Signed : Element_Count;
      Issuer_Auth   : Element_Count;
      Auth_Arr      : Element_Count;
      Mso_Bs        : Element_Count;
      Tag_Content   : Element_Count;
      Mso_Start     : Position;
      Mso_Len       : Position;
      Map_Len       : Position;
      Dki, Dk       : Element_Count;
      Sig_Bs        : Element_Count;
      Device_Signed : Element_Count;
      Device_Auth_El : Element_Count;
      Device_Sig    : Element_Count;
      Dev_Arr       : Element_Count;
      Validity      : Element_Count;
      VD            : Element_Count;
      Unused        : Element_Count;
      Namespaces    : Element_Count;
      Ns_K, Ns_V    : Element_Count;
      Prev          : Element_Count;
      Item_El       : Element_Count;
      It            : Item;
   begin
      P := (others => <>);
      Result := Ok;
      Cbor_Detail := Cbor_Parse.Ok;

      --  The bound on the document (ADR 0086), a status and not a
      --  precondition, so that a credential of any size gets an answer.
      if Mdoc'Length > Cbor_Parse.Max_Bytes then
         Result := Document_Too_Long;
         return;
      end if;
      Parse_Exact (Mdoc, Root, R);
      if R /= Cbor_Parse.Ok then
         Result := Cbor_Root;
         Cbor_Detail := R;
         return;
      end if;

      Need_Value (Root, Mdoc, 1, "documents", Docs, Result);
      if Result /= Ok then
         return;
      end if;
      if Root.Elements (Docs).Kind /= Array_Kind then
         Result := Unexpected_Type;
         return;
      end if;
      Doc0 := Array_Item (Root, Docs, 0);
      if Doc0 = 0 then
         Result := Missing_Field;
         return;
      end if;

      Need_Value (Root, Mdoc, Doc0, "issuerSigned", Issuer_Signed, Result);
      Need_Value (Root, Mdoc, Issuer_Signed, "issuerAuth", Issuer_Auth, Result);
      Cose_Array (Root, Issuer_Auth, Auth_Arr, Result);
      Need_Bytes_Item (Root, Auth_Arr, 2, Mso_Bs, Result);
      if Result /= Ok then
         return;
      end if;
      Mso_Start := Root.Elements (Mso_Bs).Content;
      Mso_Len := Root.Elements (Mso_Bs).Stop - Root.Elements (Mso_Bs).Content;

      --  The wrapped MSO: tag 24 over a byte string, the map's bytes.
      Parse_Exact (Mdoc (Mdoc'First + Mso_Start
                         .. Mdoc'First + Mso_Start + Mso_Len - 1), Wrap, R);
      if R /= Cbor_Parse.Ok then
         Result := Cbor_Mso_Wrapper;
         Cbor_Detail := R;
         return;
      end if;
      Tag_Content := Tag_Child (Wrap, 1, 24);
      if Tag_Content = 0 then
         Result := Invalid_Value;
         return;
      end if;
      if Wrap.Elements (Tag_Content).Kind /= Byte_String then
         Result := Unexpected_Type;
         return;
      end if;
      Map_Len := Wrap.Elements (Tag_Content).Stop
                 - Wrap.Elements (Tag_Content).Content;
      Validate_Mso_Layout (Mdoc, Mso_Start, Mso_Len, Map_Len, Version, Result);
      if Result /= Ok then
         return;
      end if;
      P.Mso_Start := Mso_Start;
      P.Mso_Len := Mso_Len;
      --  The wrapped MSO is the content of a byte string of the root
      --  table, so it ends inside the document (Valid); its layout was
      --  validated: the map's bytes are the whole after the five of the
      --  head, at least Min_Mso_Map of them.
      pragma Assert (P.Mso_Start + P.Mso_Len <= Mdoc'Length);
      pragma Assert (P.Mso_Len = Map_Len + Mso_Head_Len);
      pragma Assert (P.Mso_Len >= Mso_Head_Len + Min_Mso_Map);
      P.Issuer_Sig_Digest := Issuer_Digest (Mdoc, Mso_Start, Mso_Len);

      --  The MSO map, parsed on its own bytes (five bytes in); a copy of
      --  at most Max_Wrapped_Mso bytes, since SPARK does not rename a
      --  slice with variable bounds.
      declare
         Map_First : constant Natural := Mdoc'First + Mso_Start + Mso_Head_Len;
         Mso_Map   : constant Byte_Array :=
           Mdoc (Map_First .. Map_First + Map_Len - 1);
      begin
         Parse_Exact (Mso_Map, Mso, R);
         if R /= Cbor_Parse.Ok then
            Result := Cbor_Mso_Map;
            Cbor_Detail := R;
            return;
         end if;
         pragma Assert (Mso.Length = Map_Len);
         pragma Assert (Mso.Length = P.Mso_Len - Mso_Head_Len);
         Need_Value (Mso, Mso_Map, 1, "deviceKeyInfo", Dki, Result);
         Need_Value (Mso, Mso_Map, Dki, "deviceKey", Dk, Result);
         Coordinate (Mso, Mso_Map, Dk, 1, P.Device_Pk_X, Result);
         Coordinate (Mso, Mso_Map, Dk, 2, P.Device_Pk_Y, Result);
         if Result /= Ok then
            return;
         end if;

         --  The issuer's signature, the fourth element of issuerAuth.
         Need_Bytes_Item (Root, Auth_Arr, 3, Sig_Bs, Result);
         Signature (Root, Mdoc, Sig_Bs, P.Issuer_Sig_R, P.Issuer_Sig_S, Result);
         if Result /= Ok then
            return;
         end if;

         --  The device's signature.
         Need_Value (Root, Mdoc, Doc0, "deviceSigned", Device_Signed, Result);
         Need_Value (Root, Mdoc, Device_Signed, "deviceAuth", Device_Auth_El, Result);
         Need_Value (Root, Mdoc, Device_Auth_El, "deviceSignature", Device_Sig, Result);
         Cose_Array (Root, Device_Sig, Dev_Arr, Result);
         Need_Bytes_Item (Root, Dev_Arr, 3, Sig_Bs, Result);
         Signature (Root, Mdoc, Sig_Bs, P.Device_Sig_R, P.Device_Sig_S, Result);
         if Result /= Ok then
            return;
         end if;
         P.Device_Sig_Digest := Device_Auth.Digest (Transcript, Doc_Type);

         --  The offsets of the MSO fields.
         Need_Key (Mso, Mso_Map, 1, "docType", P.Doc_Type_Offset, Unused, Result);
         Need_Value (Mso, Mso_Map, 1, "validityInfo", Validity, Result);
         Need_Key (Mso, Mso_Map, Validity, "validFrom", P.Valid_From_Offset, Unused, Result);
         Need_Key (Mso, Mso_Map, Validity, "validUntil", P.Valid_Until_Offset, Unused, Result);
         Need_Key (Mso, Mso_Map, 1, "deviceKeyInfo", P.Device_Key_Info_Offset, Unused, Result);
         Need_Key (Mso, Mso_Map, 1, "valueDigests", P.Value_Digests_Offset, VD, Result);
         if Result /= Ok then
            return;
         end if;
         --  Each offset is a key's position in the MSO map, below its
         --  length (Need_Key); one step at a time for the provers.
         pragma Assert (Mso.Length = P.Mso_Len - Mso_Head_Len);
         pragma Assert (P.Doc_Type_Offset < P.Mso_Len - Mso_Head_Len);
         pragma Assert (P.Valid_From_Offset < P.Mso_Len - Mso_Head_Len);
         pragma Assert (P.Valid_Until_Offset < P.Mso_Len - Mso_Head_Len);
         pragma Assert (P.Device_Key_Info_Offset < P.Mso_Len - Mso_Head_Len);
         pragma Assert (P.Value_Digests_Offset < P.Mso_Len - Mso_Head_Len);
         pragma Assert (P.Mso_Len >= Mso_Head_Len + Min_Mso_Map);
         pragma Assert (P.Mso_Start + P.Mso_Len <= Mdoc'Length);
         pragma Assert (Head_In_Bounds (P, Mdoc'Length));

         --  extract_attrs.
         Need_Value (Root, Mdoc, Issuer_Signed, "nameSpaces", Namespaces, Result);
         if Result /= Ok then
            return;
         end if;
         if Root.Elements (Namespaces).Kind /= Map_Kind then
            Result := Unexpected_Type;
            return;
         end if;
         Ns_K := Root.Elements (Namespaces).Child;
         while Ns_K /= 0 loop
            pragma Loop_Invariant (Ns_K <= Root.Count);
            pragma Loop_Invariant (P.Count <= Max_Items);
            pragma Loop_Invariant (P.Mso_Len = Mso_Len and then P.Mso_Start = Mso_Start);
            pragma Loop_Invariant (Mso.Length = P.Mso_Len - Mso_Head_Len);
            pragma Loop_Invariant (Head_In_Bounds (P, Mdoc'Length));
            pragma Loop_Invariant (Items_In_Bounds (P, Mdoc'Length));
            pragma Loop_Variant (Increases => Ns_K);
            Ns_V := Root.Elements (Ns_K).Next;
            exit when Ns_V = 0;
            if Root.Elements (Ns_K).Kind /= Text_String then
               Result := Unexpected_Type;
               return;
            end if;
            --  A second namespace with the same name is an error.
            Prev := Root.Elements (Namespaces).Child;
            while Prev /= 0 and then Prev < Ns_K loop
               pragma Loop_Invariant (Prev <= Root.Count);
               pragma Loop_Variant (Increases => Prev);
               if Root.Elements (Prev).Kind = Text_String
                 and then Bytes_Equal
                   (Root, Mdoc, Prev,
                    Mdoc (Mdoc'First + Root.Elements (Ns_K).Content
                          .. Mdoc'First + Root.Elements (Ns_K).Stop - 1))
               then
                  Result := Duplicate_Field;
                  return;
               end if;
               Prev := Root.Elements (Prev).Next;   --  the value
               exit when Prev = 0;
               Prev := Root.Elements (Prev).Next;   --  the next key
            end loop;
            if Root.Elements (Ns_V).Kind /= Array_Kind then
               Result := Unexpected_Type;
               return;
            end if;
            Item_El := Root.Elements (Ns_V).Child;
            while Item_El /= 0 loop
               pragma Loop_Invariant (Item_El <= Root.Count);
               pragma Loop_Invariant (P.Count <= Max_Items);
               pragma Loop_Invariant (P.Mso_Len = Mso_Len and then P.Mso_Start = Mso_Start);
               pragma Loop_Invariant (Mso.Length = P.Mso_Len - Mso_Head_Len);
               pragma Loop_Invariant (Head_In_Bounds (P, Mdoc'Length));
               pragma Loop_Invariant (Items_In_Bounds (P, Mdoc'Length));
               pragma Loop_Variant (Increases => Item_El);
               if P.Count = Max_Items then
                  Result := Too_Many_Items;
                  return;
               end if;
               One_Item (Mdoc, Root, Item_El, Ns_K, Mso, Mso_Map, VD, It,
                         Result, Cbor_Detail);
               if Result /= Ok then
                  return;
               end if;
               pragma Assert (Item_In_Bounds (It, P.Mso_Len, Mdoc'Length));
               P.Count := P.Count + 1;
               P.Items (P.Count) := It;
               Item_El := Root.Elements (Item_El).Next;
            end loop;
            Ns_K := Root.Elements (Ns_V).Next;
         end loop;
         pragma Assert (Head_In_Bounds (P, Mdoc'Length));
         pragma Assert (Items_In_Bounds (P, Mdoc'Length));
      end;
   end Parse;

   function Find_Item
     (Mdoc : Byte_Array; P : Parsed_Mdoc; Id : Byte_Array) return Item_Count
   is
   begin
      for I in 1 .. P.Count loop
         if P.Items (I).Name_Len = Id'Length then
            declare
               Same : Boolean := True;
            begin
               for K in 0 .. Id'Length - 1 loop
                  if Mdoc (Mdoc'First + P.Items (I).Name_Start + K)
                    /= Id (Id'First + K)
                  then
                     Same := False;
                  end if;
               end loop;
               if Same then
                  return I;
               end if;
            end;
         end if;
      end loop;
      return 0;
   end Find_Item;

end Mdoc_Parse;
