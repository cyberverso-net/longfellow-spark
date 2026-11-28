pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;
with Uleb128;

package body Circuit_Certificates is

   Magic : constant Byte_Array (0 .. 3) :=
     [Character'Pos ('L'), Character'Pos ('F'),
      Character'Pos ('C'), Character'Pos ('K')];

   --  One integer at Pos; Ok False with St set when it cannot be read.
   procedure Next
     (B   : Byte_Array;
      Pos : in out Natural;
      V   : out Natural;
      St  : in out Status)
   with
     Global => null,
     Pre    => B'First = 0 and then Pos <= B'Length and then St = Ok,
     Post   => Pos <= B'Length
               and then (if St = Ok then V <= Uleb128.Max_Value else V = 0)
   is
      Val  : Uleb128.Value;
      Good : Boolean;
      Long : Boolean;
   begin
      Uleb128.Read (B, Pos, Val, Good, Long);
      if Good then
         V := Val;
      else
         V := 0;
         St := (if Long then Bad_Integer else Truncated);
      end if;
   end Next;

   --  The header: magic, version, identifier, layer count.
   procedure Header
     (B   : Byte_Array;
      Pos : out Natural;
      Id  : out Bytes_32;
      NL  : out Layer_Count;
      St  : out Status)
   with
     Global => null,
     Pre    => B'First = 0,
     Post   => Pos <= B'Length
   is
      V : Natural;
   begin
      Id := [others => 0];
      NL := 0;
      Pos := 0;
      St := Ok;
      if B'Length < 4 then
         St := Truncated;
         return;
      end if;
      if B (0 .. 3) /= Magic then
         St := Bad_Magic;
         return;
      end if;
      Pos := 4;
      Next (B, Pos, V, St);
      if St /= Ok then
         return;
      end if;
      if V /= 2 then
         St := Bad_Version;
         return;
      end if;
      if B'Length - Pos < 32 then
         St := Truncated;
         return;
      end if;
      Id := B (Pos .. Pos + 31);
      Pos := Pos + 32;
      Next (B, Pos, V, St);
      if St /= Ok then
         return;
      end if;
      if V > Max_Layers then
         St := Bound_Exceeded;
         return;
      end if;
      NL := V;
   end Header;

   --  The first pass: the total of wires, every integer read and
   --  bounded, and nothing after the last layer.
   procedure Scan
     (B     : Byte_Array;
      Start : Natural;
      NL    : Layer_Count;
      NW    : out Natural;
      St    : out Status)
   with
     Global => null,
     Pre    => B'First = 0 and then Start <= B'Length,
     Post   => (if St = Ok then NW <= Max_All_Wires)
   is
      Pos : Natural := Start;
      W   : Natural;
      C   : Natural;
   begin
      NW := 0;
      St := Ok;
      for I in 1 .. NL loop
         Next (B, Pos, W, St);
         if St /= Ok then
            return;
         end if;
         if W > Max_All_Wires - NW then
            St := Bound_Exceeded;
            return;
         end if;
         NW := NW + W;
         for J in 1 .. W loop
            Next (B, Pos, C, St);
            if St /= Ok then
               return;
            end if;
            if C > Max_Count then
               St := Bound_Exceeded;
               return;
            end if;
            pragma Loop_Invariant (St = Ok and then Pos <= B'Length);
         end loop;
         pragma Loop_Invariant
           (St = Ok and then Pos <= B'Length and then NW <= Max_All_Wires);
      end loop;
      if Pos /= B'Length then
         St := Trailing;
      end if;
   end Scan;

   --  The second pass, over bytes the first pass accepted: the integers
   --  are read again, in the same order, into K.
   procedure Fill
     (B     : Byte_Array;
      Start : Natural;
      K     : in out Certificate;
      St    : out Status)
   with
     Global => null,
     Pre    => B'First = 0 and then Start <= B'Length
               and then K.NW <= Max_All_Wires,
     Post   => (if St = Ok then Spans_Ok (K))
   is
      Pos : Natural := Start;
      W   : Natural;
      C   : Natural;
      FW  : Natural := 0;
   begin
      St := Ok;
      for I in 1 .. K.NL loop
         K.Layers (I) := (First_Wire => FW, Wires => 0);
         Next (B, Pos, W, St);
         if St /= Ok then
            return;
         end if;
         if W > K.NW - FW then
            St := Bound_Exceeded;
            return;
         end if;
         K.Layers (I) := (First_Wire => FW, Wires => W);
         for J in 1 .. W loop
            Next (B, Pos, C, St);
            if St /= Ok then
               return;
            end if;
            if C > Max_Count then
               St := Bound_Exceeded;
               return;
            end if;
            K.Counts (FW + J) := C;
            pragma Loop_Invariant (St = Ok and then Pos <= B'Length);
         end loop;
         FW := FW + W;
         pragma Loop_Invariant
           (St = Ok and then Pos <= B'Length
            and then FW <= K.NW
            and then K.Layers (1).First_Wire = 0
            and then (for all L in 1 .. I =>
                        K.Layers (L).Wires <= K.NW
                        and then K.Layers (L).First_Wire
                                   <= K.NW - K.Layers (L).Wires)
            and then (for all L in 2 .. I =>
                        K.Layers (L).First_Wire
                          = K.Layers (L - 1).First_Wire
                            + K.Layers (L - 1).Wires)
            and then FW = K.Layers (I).First_Wire + K.Layers (I).Wires);
      end loop;
      --  The spans end at the first pass's total. The second pass reads
      --  the same bytes, so this refuses nothing the first accepted; it
      --  states the end of the tiling where the proof sees it.
      if St = Ok and then FW /= K.NW then
         St := Bound_Exceeded;
      end if;
   end Fill;

   procedure Read
     (B  : Byte_Array;
      K  : out Cert_Access;
      St : out Status)
   is
      Pos : Natural;
      Id  : Bytes_32;
      NL  : Layer_Count;
      NW  : Natural;
   begin
      K := null;
      Header (B, Pos, Id, NL, St);
      if St /= Ok then
         return;
      end if;
      Scan (B, Pos, NL, NW, St);
      if St /= Ok then
         return;
      end if;
      K := new Certificate'
        (NL => NL, NW => NW,
         Circuit_Id => Id,
         Layers     => [others => (others => 0)],
         Counts     => [others => 0]);
      Fill (B, Pos, K.all, St);
      if St /= Ok then
         Free (K);
      end if;
   end Read;

   procedure Free (K : in out Cert_Access) is
      procedure Dispose is new Ada.Unchecked_Deallocation
        (Certificate, Cert_Access);
   begin
      Dispose (K);
   end Free;

end Circuit_Certificates;
