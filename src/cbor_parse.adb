pragma SPARK_Mode (On);

package body Cbor_Parse is

   -------------------------------------------------------------------
   --  UTF-8 (RFC 3629, as Rust's String::from_utf8 checks it): the
   --  lead byte decides the length of the sequence and the range of
   --  its first continuation byte; overlong forms and surrogates are
   --  refused.
   -------------------------------------------------------------------

   function Is_Utf8 (Data : Byte_Array; From, To : Natural) return Boolean
   with
     Global => null,
     Pre    => From >= Data'First and then To <= Data'Last
               and then To < Natural'Last
   is
      I   : Natural := From;
      B   : Unsigned_8;
      N   : Natural;       --  continuation bytes still expected
      Lo  : Unsigned_8;    --  the range of the first continuation byte
      Hi  : Unsigned_8;
   begin
      while I <= To loop
         pragma Loop_Invariant (I >= From);
         pragma Loop_Variant (Increases => I);
         B := Data (I);
         if B < 16#80# then
            I := I + 1;
         else
            if B in 16#C2# .. 16#DF# then
               N := 1; Lo := 16#80#; Hi := 16#BF#;
            elsif B = 16#E0# then
               N := 2; Lo := 16#A0#; Hi := 16#BF#;
            elsif B in 16#E1# .. 16#EC# or else B in 16#EE# .. 16#EF# then
               N := 2; Lo := 16#80#; Hi := 16#BF#;
            elsif B = 16#ED# then
               N := 2; Lo := 16#80#; Hi := 16#9F#;
            elsif B = 16#F0# then
               N := 3; Lo := 16#90#; Hi := 16#BF#;
            elsif B in 16#F1# .. 16#F3# then
               N := 3; Lo := 16#80#; Hi := 16#BF#;
            elsif B = 16#F4# then
               N := 3; Lo := 16#80#; Hi := 16#8F#;
            else
               return False;
            end if;
            if To - I < N then
               return False;
            end if;
            if Data (I + 1) < Lo or else Data (I + 1) > Hi then
               return False;
            end if;
            for K in 2 .. N loop
               if Data (I + K) < 16#80# or else Data (I + K) > 16#BF# then
                  return False;
               end if;
            end loop;
            I := I + N + 1;
         end if;
      end loop;
      return True;
   end Is_Utf8;

   -------------------------------------------------------------------
   --  The head of an item at Off: the major type, the additional
   --  information, the argument (the information itself below 24, else
   --  the next 1, 2, 4 or 8 bytes big-endian) and the length of the
   --  head. Truncated when the bytes end inside it; Reserved_Info for
   --  the values 28 to 31 (31 is the indefinite length).
   -------------------------------------------------------------------

   procedure Read_Head
     (Data     : Byte_Array;
      Off      : Position;
      Major    : out Natural;
      Info     : out Natural;
      Arg      : out Unsigned_64;
      Head_Len : out Natural;
      Result   : out Status)
   with
     Global => null,
     Pre    => Data'Length <= Max_Bytes and then Off <= Data'Length,
     Post   => Major <= 7 and then Info <= 31 and then Head_Len in 1 .. 9
               and then (if Result = Ok then
                           Off + Head_Len <= Data'Length)
   is
      B     : Unsigned_8;
      Extra : Natural;
   begin
      Major := 0; Info := 0; Arg := 0; Head_Len := 1; Result := Ok;
      if Off >= Data'Length then
         Result := Truncated;
         return;
      end if;
      B := Data (Data'First + Off);
      Major := Natural (Shift_Right (B, 5));
      Info := Natural (B and 16#1F#);
      case Info is
         when 0 .. 23 =>
            Arg := Unsigned_64 (Info);
            Extra := 0;
         when 24 => Extra := 1;
         when 25 => Extra := 2;
         when 26 => Extra := 4;
         when 27 => Extra := 8;
         when others =>
            Result := Reserved_Info;
            return;
      end case;
      Head_Len := 1 + Extra;
      if Data'Length - Off < Head_Len then
         Result := Truncated;
         return;
      end if;
      for K in 1 .. Extra loop
         pragma Loop_Invariant (Off + K <= Data'Length);
         Arg := Shift_Left (Arg, 8) or Unsigned_64 (Data (Data'First + Off + K));
      end loop;
   end Read_Head;

   -------------------------------------------------------------------
   --  The one pass. A frame per open container: the element, how many
   --  children it still expects, its last child so far (to link the
   --  next sibling). An open container keeps the provisional Stop
   --  "length of the bytes" until it closes, so that every child lies
   --  inside its parent at every step; Open marks the open elements,
   --  which are exactly the containers of the frames. The invariants
   --  are split into small ghost functions, one verification condition
   --  each, so that the provers see one property at a time.
   -------------------------------------------------------------------

   type Frame is record
      Container  : Element_Index := 1;
      Remaining  : Natural := 0;
      Last_Child : Element_Count := 0;
   end record;

   subtype Depth_Count is Natural range 0 .. Max_Depth;
   subtype Depth_Index is Depth_Count range 1 .. Max_Depth;
   type Stack is array (Depth_Index) of Frame;
   --  The frame of an open element (0 for a closed one): the open
   --  elements are exactly the frames' containers, and the frame of
   --  each is recorded, so that the provers have the witness in hand.
   type Frame_Map is array (Element_Index) of Depth_Count;

   --  Every element's range: head before content, content before the
   --  end, the end inside the bytes.
   function Ranges_Ok (Doc : Document) return Boolean is
     (for all I in 1 .. Doc.Count =>
        Doc.Elements (I).Start < Doc.Elements (I).Content
        and then Doc.Elements (I).Content <= Doc.Elements (I).Stop
        and then Doc.Elements (I).Stop <= Doc.Length)
   with Ghost;

   --  The links point forward, within the table: a child's parent is
   --  the element, a sibling's parent the same, and a sibling starts
   --  where the element ended or later.
   function Links_Ok (Doc : Document) return Boolean is
     (for all I in 1 .. Doc.Count =>
        Doc.Elements (I).Child <= Doc.Count
        and then Doc.Elements (I).Next <= Doc.Count
        and then (Doc.Elements (I).Child = 0
                  or else (Doc.Elements (I).Child > I
                           and then Doc.Elements (Doc.Elements (I).Child).Parent = I))
        and then (Doc.Elements (I).Next = 0
                  or else (Doc.Elements (I).Next > I
                           and then Doc.Elements (Doc.Elements (I).Next).Parent
                                    = Doc.Elements (I).Parent
                           and then Doc.Elements (Doc.Elements (I).Next).Start
                                    >= Doc.Elements (I).Stop)))
   with Ghost;

   --  The parent comes earlier; only the root has none; every child is
   --  inside its parent.
   function Parents_Ok (Doc : Document) return Boolean is
     (for all I in 1 .. Doc.Count =>
        Doc.Elements (I).Parent < I
        and then (Doc.Elements (I).Parent = 0) = (I = 1)
        and then (if Doc.Elements (I).Parent > 0 then
                    Doc.Elements (Doc.Elements (I).Parent).Content
                      <= Doc.Elements (I).Start
                    and then Doc.Elements (I).Stop
                      <= Doc.Elements (Doc.Elements (I).Parent).Stop))
   with Ghost;

   --  An open element ends provisionally at the length and its content
   --  starts at or before Off; a closed one ends at or before Off.
   function Open_Ok (Doc : Document; F : Frame_Map; Off : Position)
     return Boolean
   is
     (for all I in 1 .. Doc.Count =>
        (if F (I) > 0 then
           Doc.Elements (I).Stop = Doc.Length
           and then Doc.Elements (I).Content <= Off
         else
           Doc.Elements (I).Stop <= Off))
   with Ghost;

   --  The frames: open containers in the table, each expecting at least
   --  one more child, each the parent of the next and earlier than it;
   --  the first frame's container is the root. A frame's last child so
   --  far is one of its children; the top frame's is closed (a frame's
   --  below is the container of the frame above, still open).
   function Frames_Ok
     (St : Stack; Depth : Depth_Count; Doc : Document; F : Frame_Map)
      return Boolean
   is
     (for all D in 1 .. Depth =>
        St (D).Container <= Doc.Count
        and then F (St (D).Container) = D
        and then St (D).Remaining > 0
        and then St (D).Last_Child <= Doc.Count
        and then (if St (D).Last_Child > 0 then
                    Doc.Elements (St (D).Last_Child).Parent = St (D).Container
                    and then (if D = Depth then F (St (D).Last_Child) = 0))
        and then (if D = 1 then
                    Doc.Elements (St (D).Container).Parent = 0
                  else
                    Doc.Elements (St (D).Container).Parent = St (D - 1).Container
                    and then St (D - 1).Container < St (D).Container))
   with Ghost;

   --  The frame of an element is one of the frames, and names it.
   function Frames_Of_Ok
     (St : Stack; Depth : Depth_Count; Doc : Document; F : Frame_Map)
      return Boolean
   is
     (for all I in 1 .. Doc.Count =>
        F (I) <= Depth
        and then (if F (I) > 0 then St (F (I)).Container = I))
   with Ghost;

   function All_Ok
     (Doc : Document; St : Stack; Depth : Depth_Count; F : Frame_Map;
      Off : Position) return Boolean
   is
     (Ranges_Ok (Doc) and then Links_Ok (Doc) and then Parents_Ok (Doc)
      and then Open_Ok (Doc, F, Off)
      and then Frames_Ok (St, Depth, Doc, F)
      and then Frames_Of_Ok (St, Depth, Doc, F))
   with Ghost;

   --  The children of the top frame's container are all closed: an open
   --  element is a frame's container whose parent is the frame below,
   --  and no frame lies above the top one. One element at a time.
   procedure Lemma_Children_Closed
     (Doc : Document; St : Stack; Depth : Depth_Index; F : Frame_Map)
   with
     Ghost,
     Global => null,
     Pre    => Frames_Ok (St, Depth, Doc, F)
               and then Frames_Of_Ok (St, Depth, Doc, F),
     Post   => (for all I in 1 .. Doc.Count =>
                  (if Doc.Elements (I).Parent = St (Depth).Container
                   then F (I) = 0))
   is
      C : constant Element_Index := St (Depth).Container;
   begin
      for I in 1 .. Doc.Count loop
         pragma Loop_Invariant
           (for all J in 1 .. I - 1 =>
              (if Doc.Elements (J).Parent = C then F (J) = 0));
         if Doc.Elements (I).Parent = C and then F (I) > 0 then
            --  I is the container of frame F (I); its parent is the
            --  container of the frame below, which is C only if that
            --  frame is Depth, so F (I) = Depth + 1 > Depth.
            pragma Assert (St (F (I)).Container = I);
            pragma Assert (F (I) > 1);
            pragma Assert (St (F (I) - 1).Container = C);
            pragma Assert (F (C) = F (I) - 1);
            pragma Assert (F (C) = Depth);
            pragma Assert (False);
         end if;
      end loop;
   end Lemma_Children_Closed;

   --  One element enters the table under the top frame (or as the root):
   --  stored, linked after its last sibling; if it opens a container,
   --  its frame is pushed and Off moves to its content, else Off moves
   --  to its end.
   procedure Enter
     (Doc   : in out Document;
      St    : in out Stack;
      Depth : in out Depth_Count;
      F     : in out Frame_Map;
      Off   : in out Position;
      E     : Element;
      Items : Natural)
   with
     Global => null,
     Pre    => Doc.Count < Max_Elements
               and then Off <= Doc.Length
               and then All_Ok (Doc, St, Depth, F, Off)
               and then (Depth > 0 or else Doc.Count = 0)
               and then E.Start = Off
               and then E.Start < E.Content
               and then E.Content <= E.Stop
               and then E.Stop <= Doc.Length
               and then (if Items > 0 then E.Stop = Doc.Length)
               and then E.Parent = (if Depth = 0 then 0 else St (Depth).Container)
               and then E.Child = 0 and then E.Next = 0
               and then E.Count = Items
               and then (if Items > 0 then Depth < Max_Depth),
     Post   => Doc.Count = Doc.Count'Old + 1
               and then Doc.Length = Doc.Length'Old
               and then Off <= Doc.Length
               and then Depth = (if Items > 0 then Depth'Old + 1 else Depth'Old)
               and then All_Ok (Doc, St, Depth, F, Off)
   is
      Idx : constant Element_Index := Doc.Count + 1;
   begin
      Doc.Count := Idx;
      Doc.Elements (Idx) := E;
      F (Idx) := 0;
      pragma Assert (Ranges_Ok (Doc));
      pragma Assert (Parents_Ok (Doc));
      pragma Assert (Links_Ok (Doc));
      if Depth > 0 then
         if St (Depth).Last_Child = 0 then
            Doc.Elements (St (Depth).Container).Child := Idx;
         else
            Doc.Elements (St (Depth).Last_Child).Next := Idx;
         end if;
         St (Depth).Last_Child := Idx;
      end if;
      pragma Assert (Ranges_Ok (Doc));
      pragma Assert (Parents_Ok (Doc));
      pragma Assert (Links_Ok (Doc));
      if Items > 0 then
         Off := E.Content;
         Depth := Depth + 1;
         St (Depth) := (Container  => Idx,
                        Remaining  => Items,
                        Last_Child => 0);
         F (Idx) := Depth;
      else
         Off := E.Stop;
      end if;
   end Enter;

   --  The top frame's container, which expected one more child and has
   --  it, closes at Off; the frame is popped.
   procedure Close_Top
     (Doc   : in out Document;
      St    : Stack;
      Depth : in out Depth_Count;
      F     : in out Frame_Map;
      Off   : Position)
   with
     Global => null,
     Pre    => Depth > 0
               and then Off <= Doc.Length
               and then All_Ok (Doc, St, Depth, F, Off),
     Post   => Doc.Count = Doc.Count'Old
               and then Doc.Length = Doc.Length'Old
               and then Depth = Depth'Old - 1
               and then All_Ok (Doc, St, Depth, F, Off)
   is
      C : constant Element_Index := St (Depth).Container;
   begin
      Lemma_Children_Closed (Doc, St, Depth, F);
      Doc.Elements (C).Stop := Off;
      F (C) := 0;
      Depth := Depth - 1;
   end Close_Top;

   procedure Parse_Exact
     (Data   : Byte_Array;
      Doc    : out Document;
      Result : out Status)
   is
      Off    : Position := 0;
      Depth  : Depth_Count := 0;
      St     : Stack := [others => <>];
      F      : Frame_Map := [others => 0];
      Major  : Natural;
      Info   : Natural;
      Arg    : Unsigned_64;
      HL     : Natural;
      R      : Status;
      E      : Element;
      Items  : Natural;
      Len    : Position;
   begin
      Doc := (Length => Data'Length, Count => 0, Elements => [others => <>]);
      Result := Ok;
      loop
         pragma Loop_Invariant (Off <= Data'Length);
         pragma Loop_Invariant (Doc.Length = Data'Length);
         pragma Loop_Invariant (Doc.Count <= Max_Elements);
         pragma Loop_Invariant (Depth > 0 or else Doc.Count = 0);
         pragma Loop_Invariant (All_Ok (Doc, St, Depth, F, Off));
         pragma Loop_Variant (Increases => Doc.Count);

         if Doc.Count = Max_Elements then
            --  The table is full and the root is not complete.
            Result := Too_Many_Elements;
            return;
         end if;
         Read_Head (Data, Off, Major, Info, Arg, HL, R);
         if R /= Ok then
            Result := R;
            return;
         end if;
         E := (Kind    => Unsigned_Int,
               Start   => Off,
               Content => Off + HL,
               Stop    => Off + HL,
               Value   => Arg,
               Count   => 0,
               Parent  => (if Depth = 0 then 0 else St (Depth).Container),
               Child   => 0,
               Next    => 0);
         Items := 0;
         case Major is
            when 0 =>
               E.Kind := Unsigned_Int;
            when 1 =>
               E.Kind := Negative_Int;
            when 2 | 3 =>
               if Arg > Unsigned_64 (Data'Length - E.Content) then
                  Result := (if Arg > Unsigned_64 (Max_Bytes)
                             then Length_Too_Large else Truncated);
                  return;
               end if;
               Len := Position (Arg);
               E.Stop := E.Content + Len;
               if Major = 2 then
                  E.Kind := Byte_String;
               else
                  E.Kind := Text_String;
                  if Len > 0
                    and then not Is_Utf8 (Data, Data'First + E.Content,
                                          Data'First + E.Stop - 1)
                  then
                     Result := Not_Utf8;
                     return;
                  end if;
               end if;
            when 4 =>
               if Arg > Unsigned_64 (Max_Elements) then
                  Result := Too_Many_Elements;
                  return;
               end if;
               E.Kind := Array_Kind;
               Items := Natural (Arg);
            when 5 =>
               if Arg > Unsigned_64 (Max_Elements / 2) then
                  Result := Too_Many_Elements;
                  return;
               end if;
               E.Kind := Map_Kind;
               Items := 2 * Natural (Arg);
            when 6 =>
               E.Kind := Tag;
               Items := 1;
            when others =>
               case Info is
                  when 0 .. 24 => E.Kind := Simple;
                  when 25 => E.Kind := Float_16;
                  when 26 => E.Kind := Float_32;
                  when others => E.Kind := Float_64;
               end case;
         end case;
         E.Count := Items;
         if Items > 0 then
            if Depth = Max_Depth then
               Result := Too_Deep;
               return;
            end if;
            --  An open container: its children follow its head.
            E.Stop := Data'Length;
         end if;
         Enter (Doc, St, Depth, F, Off, E, Items);
         if Items = 0 then
            --  A leaf, or an empty container, is complete: it is one
            --  child of the top frame; when it was the last, the
            --  container closes, and so on up the stack.
            loop
               pragma Loop_Invariant (Depth <= Max_Depth);
               pragma Loop_Invariant (Doc.Count = Doc.Count'Loop_Entry);
               pragma Loop_Invariant (Doc.Count <= Max_Elements);
               pragma Loop_Invariant (Doc.Length = Data'Length);
               pragma Loop_Invariant (Off <= Data'Length);
               pragma Loop_Invariant (All_Ok (Doc, St, Depth, F, Off));
               pragma Loop_Variant (Decreases => Depth);
               exit when Depth = 0;
               if St (Depth).Remaining > 1 then
                  St (Depth).Remaining := St (Depth).Remaining - 1;
                  exit;
               end if;
               Close_Top (Doc, St, Depth, F, Off);
            end loop;
            exit when Depth = 0;
         end if;
      end loop;
      if Off /= Data'Length then
         Result := Trailing_Bytes;
      end if;
   end Parse_Exact;

   -------------------------------------------------------------------
   --  The accessors
   -------------------------------------------------------------------

   function Array_Item
     (Doc : Document; A : Element_Index; I : Natural) return Element_Count
   is
      C : Element_Count;
   begin
      if Doc.Elements (A).Kind /= Array_Kind then
         return 0;
      end if;
      C := Doc.Elements (A).Child;
      for K in 1 .. I loop
         pragma Loop_Invariant (C <= Doc.Count);
         pragma Loop_Invariant (if C > 0 then Doc.Elements (C).Parent = A);
         exit when C = 0;
         C := Doc.Elements (C).Next;
      end loop;
      return C;
   end Array_Item;

   function Text_Equals
     (Doc : Document; Data : Byte_Array; E : Element_Index; S : String)
      return Boolean
   is
      El : constant Element := Doc.Elements (E);
   begin
      if El.Kind /= Text_String or else El.Stop - El.Content /= S'Length then
         return False;
      end if;
      for K in 0 .. S'Length - 1 loop
         if Data (Data'First + El.Content + K)
           /= Unsigned_8 (Character'Pos (S (S'First + K)))
         then
            return False;
         end if;
      end loop;
      return True;
   end Text_Equals;

   function Bytes_Equal
     (Doc : Document; Data : Byte_Array; E : Element_Index; B : Byte_Array)
      return Boolean
   is
      El : constant Element := Doc.Elements (E);
   begin
      if (El.Kind /= Byte_String and then El.Kind /= Text_String)
        or else El.Stop - El.Content /= B'Length
      then
         return False;
      end if;
      for K in 0 .. B'Length - 1 loop
         if Data (Data'First + El.Content + K) /= B (B'First + K) then
            return False;
         end if;
      end loop;
      return True;
   end Bytes_Equal;

   procedure Map_Text_Entry
     (Doc    : Document;
      Data   : Byte_Array;
      M      : Element_Index;
      Key    : String;
      Key_El : out Element_Count;
      Val_El : out Element_Count;
      Result : out Lookup)
   is
      K : Element_Count;
      V : Element_Count;
   begin
      Key_El := 0;
      Val_El := 0;
      Result := Missing;
      if Doc.Elements (M).Kind /= Map_Kind then
         Result := Not_A_Map;
         return;
      end if;
      K := Doc.Elements (M).Child;
      while K /= 0 loop
         pragma Loop_Invariant (K <= Doc.Count);
         pragma Loop_Invariant (if K > 0 then Doc.Elements (K).Parent = M);
         pragma Loop_Invariant (Key_El <= Doc.Count and then Val_El <= Doc.Count);
         pragma Loop_Invariant
           (if Result = Found then
              Key_El > 0 and then Val_El > 0
              and then Doc.Elements (Key_El).Parent = M
              and then Doc.Elements (Val_El).Parent = M);
         pragma Loop_Variant (Increases => K);
         V := Doc.Elements (K).Next;
         exit when V = 0;
         if Text_Equals (Doc, Data, K, Key) then
            if Result = Found then
               Result := Duplicate;
               return;
            end if;
            Key_El := K;
            Val_El := V;
            Result := Found;
         end if;
         K := Doc.Elements (V).Next;
      end loop;
   end Map_Text_Entry;

   procedure Map_Bytes_Entry
     (Doc    : Document;
      Data   : Byte_Array;
      M      : Element_Index;
      Key    : Byte_Array;
      Key_El : out Element_Count;
      Val_El : out Element_Count;
      Result : out Lookup)
   is
      K : Element_Count;
      V : Element_Count;
   begin
      Key_El := 0;
      Val_El := 0;
      Result := Missing;
      if Doc.Elements (M).Kind /= Map_Kind then
         Result := Not_A_Map;
         return;
      end if;
      K := Doc.Elements (M).Child;
      while K /= 0 loop
         pragma Loop_Invariant (K <= Doc.Count);
         pragma Loop_Invariant (if K > 0 then Doc.Elements (K).Parent = M);
         pragma Loop_Invariant (Key_El <= Doc.Count and then Val_El <= Doc.Count);
         pragma Loop_Invariant
           (if Result = Found then
              Key_El > 0 and then Val_El > 0
              and then Doc.Elements (Key_El).Parent = M
              and then Doc.Elements (Val_El).Parent = M);
         pragma Loop_Variant (Increases => K);
         V := Doc.Elements (K).Next;
         exit when V = 0;
         if Doc.Elements (K).Kind = Text_String
           and then Bytes_Equal (Doc, Data, K, Key)
         then
            if Result = Found then
               Result := Duplicate;
               return;
            end if;
            Key_El := K;
            Val_El := V;
            Result := Found;
         end if;
         K := Doc.Elements (V).Next;
      end loop;
   end Map_Bytes_Entry;

   procedure Map_Int_Entry
     (Doc       : Document;
      M         : Element_Index;
      Negative  : Boolean;
      Magnitude : Unsigned_64;
      Key_El    : out Element_Count;
      Val_El    : out Element_Count;
      Result    : out Lookup)
   is
      Wanted : constant Kind := (if Negative then Negative_Int else Unsigned_Int);
      K : Element_Count;
      V : Element_Count;
   begin
      Key_El := 0;
      Val_El := 0;
      Result := Missing;
      if Doc.Elements (M).Kind /= Map_Kind then
         Result := Not_A_Map;
         return;
      end if;
      K := Doc.Elements (M).Child;
      while K /= 0 loop
         pragma Loop_Invariant (K <= Doc.Count);
         pragma Loop_Invariant (if K > 0 then Doc.Elements (K).Parent = M);
         pragma Loop_Invariant (Key_El <= Doc.Count and then Val_El <= Doc.Count);
         pragma Loop_Invariant
           (if Result = Found then
              Key_El > 0 and then Val_El > 0
              and then Doc.Elements (Key_El).Parent = M
              and then Doc.Elements (Val_El).Parent = M);
         pragma Loop_Variant (Increases => K);
         V := Doc.Elements (K).Next;
         exit when V = 0;
         if Doc.Elements (K).Kind = Wanted
           and then Doc.Elements (K).Value = Magnitude
         then
            if Result = Found then
               Result := Duplicate;
               return;
            end if;
            Key_El := K;
            Val_El := V;
            Result := Found;
         end if;
         K := Doc.Elements (V).Next;
      end loop;
   end Map_Int_Entry;

   function Tag_Child
     (Doc : Document; E : Element_Index; N : Unsigned_64) return Element_Count
   is
     (if Doc.Elements (E).Kind = Tag and then Doc.Elements (E).Value = N
      then Doc.Elements (E).Child else 0);

end Cbor_Parse;
