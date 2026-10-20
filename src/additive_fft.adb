pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;

package body Additive_Fft is

   use GF2_128;

   --  The two work arrays of Extend, of up to 2^16 elements each, on the
   --  heap (ADR 0047).
   type Elems_Access is access Element_Array;

   procedure Free_Elems is
     new Ada.Unchecked_Deallocation (Element_Array, Elems_Access);

   ----------------------------------------------------------------------
   --  The table and the twiddle factors
   ----------------------------------------------------------------------

   type W_Table is array (Coord, Coord) of Element;

   function Make_W_Hat return W_Table with Global => null;

   function Make_W_Hat return W_Table is
      W : W_Table := [others => [others => Zero]];
   begin
      --  W_0 (beta_J) = beta_J.
      for J in Coord loop
         W (0, J) := Subfield_Basis (J);
      end loop;
      --  W_I+1 (beta_J) = W_I (beta_J) (W_I (beta_J) + W_I (beta_I)).
      for I in 0 .. Dim - 2 loop
         declare
            Wb : constant Element := W (I, I);
         begin
            for J in Coord loop
               W (I + 1, J) := Mul (W (I, J), Add (W (I, J), Wb));
            end loop;
         end;
      end loop;
      --  Normalised by W_I (beta_I), which is not zero: beta_I is not in
      --  the span of beta_0 .. beta_I-1, where W_I vanishes.
      for I in Coord loop
         declare
            S : constant Element := Inv (W (I, I));
         begin
            for J in Coord loop
               W (I, J) := Mul (W (I, J), S);
            end loop;
         end;
      end loop;
      return W;
   end Make_W_Hat;

   Table : constant W_Table := Make_W_Hat;

   function W_Hat (I, J : Coord) return Element is (Table (I, J));

   function Twiddle (I : Coord; U : Natural) return Element is
      T : Element := Zero;
      V : Natural := U;
   begin
      for K in Coord loop
         if V mod 2 = 1 then
            T := Add (T, W_Hat (I, K));
         end if;
         V := V / 2;
      end loop;
      return T;
   end Twiddle;

   ----------------------------------------------------------------------
   --  The three butterflies (lch14.rs); in characteristic 2 subtraction
   --  is addition.
   ----------------------------------------------------------------------

   procedure Fwd (B : in out Element_Array; X, Y : Natural; T : Element)
   with
     Global => null,
     Pre    => X in B'Range and then Y in B'Range,
     Inline
   is
   begin
      B (X) := Add (B (X), Mul (B (Y), T));
      B (Y) := Add (B (Y), B (X));
   end Fwd;

   procedure Bwd (B : in out Element_Array; X, Y : Natural; T : Element)
   with
     Global => null,
     Pre    => X in B'Range and then Y in B'Range,
     Inline
   is
   begin
      B (Y) := Add (B (Y), B (X));
      B (X) := Add (B (X), Mul (B (Y), T));
   end Bwd;

   procedure Diag (B : in out Element_Array; X, Y : Natural; T : Element)
   with
     Global => null,
     Pre    => X in B'Range and then Y in B'Range,
     Inline
   is
      B1 : constant Element := B (Y);
   begin
      B (Y) := Add (B (Y), B (X));
      B (X) := Add (B (X), Mul (B1, T));
   end Diag;

   ----------------------------------------------------------------------
   --  The transforms
   ----------------------------------------------------------------------

   procedure Fft
     (L     : Level;
      Coset : Natural;
      B     : in out Element_Array;
      Off   : Natural)
   is
   begin
      if L > 0 then
         declare
            S : constant Positive := 2**(L - 1);
            T : constant Element := Twiddle (L - 1, Coset);
         begin
            pragma Assert (2**L = 2 * S);
            for V in 0 .. S - 1 loop
               Fwd (B, Off + V, Off + V + S, T);
            end loop;
            Fft (L - 1, Coset, B, Off);
            Fft (L - 1, Coset + S, B, Off + S);
         end;
      end if;
   end Fft;

   procedure Ifft
     (L     : Level;
      Coset : Natural;
      B     : in out Element_Array;
      Off   : Natural)
   is
   begin
      if L > 0 then
         declare
            S : constant Positive := 2**(L - 1);
            T : constant Element := Twiddle (L - 1, Coset);
         begin
            pragma Assert (2**L = 2 * S);
            Ifft (L - 1, Coset, B, Off);
            Ifft (L - 1, Coset + S, B, Off + S);
            for V in 0 .. S - 1 loop
               Bwd (B, Off + V, Off + V + S, T);
            end loop;
         end;
      end if;
   end Ifft;

   procedure Bidir
     (L     : Level;
      Coset : Natural;
      K     : Natural;
      B     : in out Element_Array;
      Off   : Natural)
   is
   begin
      if L > 0 then
         declare
            S : constant Positive := 2**(L - 1);
            T : constant Element := Twiddle (L - 1, Coset);
         begin
            pragma Assert (2**L = 2 * S);
            if K < S then
               for V in K .. S - 1 loop
                  Fwd (B, Off + V, Off + V + S, T);
               end loop;
               Bidir (L - 1, Coset, K, B, Off);
               for V in 0 .. K - 1 loop
                  Diag (B, Off + V, Off + V + S, T);
               end loop;
               Fft (L - 1, Coset + S, B, Off + S);
            else
               Ifft (L - 1, Coset, B, Off);
               for V in K - S .. S - 1 loop
                  Diag (B, Off + V, Off + V + S, T);
               end loop;
               Bidir (L - 1, Coset + S, K - S, B, Off + S);
               for V in 0 .. K - S - 1 loop
                  Bwd (B, Off + V, Off + V + S, T);
               end loop;
            end if;
         end;
      end if;
   end Bidir;

   ----------------------------------------------------------------------
   --  Extend
   ----------------------------------------------------------------------

   procedure Extend (Row : Element_Array; Enc : out Element_Array) is
      N   : constant Positive := Row'Length;
      M   : constant Positive := Enc'Length;
      L   : Level := 0;
      Len : Positive := 1;
   begin
      Enc := [others => Zero];
      for X in 0 .. N - 1 loop
         Enc (X) := Row (X);
         pragma Loop_Invariant
           (for all X2 in 0 .. X => Field_GF2_128.Same (Enc (X2), Row (X2)));
      end loop;

      --  2^L, the smallest power of two at least N.
      while L < Dim and then Len < N loop
         pragma Loop_Invariant (Len = 2**L and then Len < N);
         pragma Loop_Variant (Increases => L);
         L   := L + 1;
         Len := 2 * Len;
      end loop;
      --  Not taken: N is at most 2^16, so the loop ends with N <= 2^L.
      --  The provers do not evaluate 2^16 for a variable exponent, so the
      --  case stays, and returns the systematic part alone.
      if Len < N then
         return;
      end if;
      pragma Assert (Len = 2**L and then N <= Len);

      declare
         C   : Elems_Access := new Element_Array'(0 .. Len - 1 => Zero);
         Tmp : Elems_Access := new Element_Array'(0 .. Len - 1 => Zero);
         Lim : constant Positive := Natural'Min (M, Len);
         Bc  : Natural := Len;
      begin
         --  The values on the first 2^L points, from the first N.
         for X in 0 .. N - 1 loop
            C (X) := Row (X);
         end loop;
         Bidir (L, 0, N, C.all, 0);
         for X in N .. Lim - 1 loop
            Enc (X) := C (X);
            pragma Loop_Invariant
              (for all X2 in 0 .. N - 1 =>
                 Field_GF2_128.Same (Enc (X2), Row (X2)));
         end loop;

         --  C becomes the coefficients alone, then one forward transform
         --  per coset of 2^L points up to M.
         for X in N .. Len - 1 loop
            C (X) := Zero;
         end loop;
         while Bc < M loop
            pragma Loop_Invariant (Bc >= Len and then Bc < M);
            pragma Loop_Invariant
              (for all X2 in 0 .. N - 1 =>
                 Field_GF2_128.Same (Enc (X2), Row (X2)));
            pragma Loop_Invariant (C /= null and then C'First = 0
                                   and then C'Last = Len - 1);
            pragma Loop_Invariant (Tmp /= null and then Tmp'First = 0
                                   and then Tmp'Last = Len - 1);
            pragma Loop_Variant (Increases => Bc);
            for X in 0 .. Len - 1 loop
               Tmp (X) := C (X);
            end loop;
            Fft (L, Bc, Tmp.all, 0);
            for X in 0 .. Natural'Min (M - Bc, Len) - 1 loop
               Enc (Bc + X) := Tmp (X);
               pragma Loop_Invariant
                 (for all X2 in 0 .. N - 1 =>
                    Field_GF2_128.Same (Enc (X2), Row (X2)));
            end loop;
            exit when M - Bc <= Len;
            Bc := Bc + Len;
         end loop;
         Free_Elems (C);
         Free_Elems (Tmp);
      end;
   end Extend;

end Additive_Fft;
