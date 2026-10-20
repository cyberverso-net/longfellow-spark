pragma SPARK_Mode (On);

with Ada.Unchecked_Deallocation;

package body Rfft_P256 is

   use P256_Field;

   --  The work arrays, of up to 2^16 elements each, on the heap (ADR
   --  0047).
   type Elems_Access is access Element_Array;
   procedure Free_Elems is
     new Ada.Unchecked_Deallocation (Element_Array, Elems_Access);

   type Fp2_Access is access Fp2_Array;
   procedure Free_Fp2 is
     new Ada.Unchecked_Deallocation (Fp2_Array, Fp2_Access);

   type Index_Array is array (Natural range <>) of Natural;
   type Index_Access is access Index_Array;
   procedure Free_Index is
     new Ada.Unchecked_Deallocation (Index_Array, Index_Access);

   ----------------------------------------------------------------------
   --  F_p^2 (fp2.rs) and the two complex products of rfft.rs
   ----------------------------------------------------------------------

   function Mul2 (A, B : Fp2) return Fp2 is
     (Re => Sub (Mul (A.Re, B.Re), Mul (A.Im, B.Im)),
      Im => Add (Mul (A.Re, B.Im), Mul (A.Im, B.Re)))
   with Global => null;

   One2 : constant Fp2 := (Re => One, Im => Zero);

   --  cmul: (xr + i xi) (br + i bi), with three products.
   function Cmul (Xr, Xi, Br, Bi : Element) return Fp2 with Global => null is
      A01 : constant Element := Add (Xr, Xi);
      B01 : constant Element := Add (Br, Bi);
      P1  : constant Element := Mul (Xi, Bi);
      P0  : constant Element := Mul (Xr, Br);
   begin
      return (Re => Sub (P0, P1), Im => Sub (Sub (Mul (A01, B01), P0), P1));
   end Cmul;

   --  cmul_conj: (xr + i xi) (br - i bi), with three products.
   function Cmul_Conj (Xr, Xi, Br, Bi : Element) return Fp2
   with Global => null is
      A01 : constant Element := Add (Xr, Xi);
      B01 : constant Element := Sub (Br, Bi);
      P1  : constant Element := Mul (Xi, Bi);
      P0  : constant Element := Mul (Xr, Br);
   begin
      return (Re => Add (P0, P1), Im => Add (Sub (Mul (A01, B01), P0), P1));
   end Cmul_Conj;

   ----------------------------------------------------------------------
   --  The roots (rfft.rs, Twiddle::reroot and Twiddle::new)
   ----------------------------------------------------------------------

   --  The root of order 2^L: the reference's, squared 31 - L times.
   function Reroot (L : Log_Size) return Fp2 with Global => null is
      W : Fp2 := Root;
   begin
      for K in L .. Log_Root - 1 loop
         W := Mul2 (W, W);
      end loop;
      return W;
   end Reroot;

   --  T (J) = W^J for J below T'Length.
   procedure Powers (W : Fp2; T : out Fp2_Array) with
     Global => null,
     Pre    => T'First = 0
   is
      Cur : Fp2 := One2;
   begin
      T := [others => One2];
      for J in T'Range loop
         T (J) := Cur;
         Cur := Mul2 (Cur, W);
      end loop;
   end Powers;

   --  The table of the level a quarter the size: every fourth entry.
   procedure Quarter (T : Fp2_Array; Tc : out Fp2_Array) with
     Global => null,
     Pre    => T'First = 0 and then Tc'First = 0
               and then T'Last >= 0 and then Tc'Last <= T'Last / 4
   is
   begin
      Tc := [others => One2];
      for J in Tc'Range loop
         Tc (J) := T (4 * J);
      end loop;
   end Quarter;

   ----------------------------------------------------------------------
   --  The input permutation (rfft.rs, bitrev)
   ----------------------------------------------------------------------

   procedure Bitrev (A : in out Element_Array; L : Log_Size) with
     Global => null,
     Pre    => A'First = 0 and then A'Length = 2**L
   is
      N   : constant Positive := A'Length;
      H   : constant Natural := N / 2;
      Rev : Index_Access := new Index_Array'(0 .. N - 1 => 0);
   begin
      pragma Assert (2**L = 2 * 2**(L - 1));
      for I in 1 .. N - 1 loop
         pragma Loop_Invariant (Rev /= null and then Rev'First = 0
                                and then Rev'Last = N - 1);
         pragma Loop_Invariant (for all K in 0 .. I - 1 => Rev (K) < N);
         Rev (I) := Rev (I / 2) / 2 + (if I mod 2 = 1 then H else 0);
      end loop;
      for I in 0 .. N - 1 loop
         pragma Loop_Invariant (Rev /= null and then Rev'First = 0
                                and then Rev'Last = N - 1);
         pragma Loop_Invariant (for all K in 0 .. N - 1 => Rev (K) < N);
         if I < Rev (I) then
            declare
               T : constant Element := A (I);
            begin
               A (I) := A (Rev (I));
               A (Rev (I)) := T;
            end;
         end if;
      end loop;
      Free_Index (Rev);
   end Bitrev;

   ----------------------------------------------------------------------
   --  The butterflies of rfft.rs, each on A (I + k S), k = 0 .. 3
   ----------------------------------------------------------------------

   procedure R2hc_I_2 (A : in out Element_Array; I, S : Natural) with
     Global => null,
     Pre    => A'First = 0 and then I < A'Length
               and then S <= A'Length - 1 - I
   is
      T : constant Element := A (I + S);
   begin
      A (I + S) := Sub (A (I), T);
      A (I) := Add (A (I), T);
   end R2hc_I_2;

   procedure R2hc_I_4 (A : in out Element_Array; I, S : Natural) with
     Global => null,
     Pre    => A'First = 0 and then I < A'Length
               and then S <= (A'Length - 1 - I) / 3
   is
      X1 : constant Element := A (I + S);
      X3 : constant Element := A (I + 3 * S);
      X2 : Element;
      Z1 : Element;
   begin
      A (I + S) := Sub (A (I), X1);
      A (I) := Add (A (I), X1);
      X2 := A (I + 2 * S);
      A (I + 3 * S) := Sub (X3, X2);
      A (I + 2 * S) := Add (X2, X3);
      Z1 := A (I + 2 * S);
      A (I + 2 * S) := Sub (A (I), Z1);
      A (I) := Add (A (I), Z1);
   end R2hc_I_4;

   procedure R2hc_Ii_4 (A : in out Element_Array; I, S : Natural; W8 : Fp2)
   with
     Global => null,
     Pre    => A'First = 0 and then I < A'Length
               and then S <= (A'Length - 1 - I) / 3
   is
      X0 : constant Element := A (I);
      X1 : constant Element := A (I + S);
      X2 : constant Element := A (I + 2 * S);
      X3 : constant Element := A (I + 3 * S);
      Z0 : constant Element := Mul (Add (X2, X3), W8.Im);
      Z1 : constant Element := Mul (Sub (X2, X3), W8.Re);
   begin
      A (I + S) := Sub (X0, Z1);
      A (I) := Add (X0, Z1);
      A (I + 3 * S) := Neg (Add (X1, Z0));
      A (I + 2 * S) := Sub (X1, Z0);
   end R2hc_Ii_4;

   procedure Hc2hc_F_4
     (A          : in out Element_Array;
      Ir, Ii, S  : Natural;
      Tw1, Tw2, Tw3 : Fp2)
   with
     Global => null,
     Pre    => A'First = 0 and then Ir < A'Length and then Ii < A'Length
               and then S <= (A'Length - 1 - Ir) / 3
               and then S <= (A'Length - 1 - Ii) / 3
   is
      X0r : constant Element := A (Ir);
      X0i : constant Element := A (Ii);
      X1  : constant Fp2 := Cmul_Conj (A (Ir + S), A (Ii + S), Tw2.Re, Tw2.Im);
      X2  : constant Fp2 :=
        Cmul_Conj (A (Ir + 2 * S), A (Ii + 2 * S), Tw1.Re, Tw1.Im);
      X3  : constant Fp2 :=
        Cmul_Conj (A (Ir + 3 * S), A (Ii + 3 * S), Tw3.Re, Tw3.Im);
      Y0r : constant Element := Add (X0r, X1.Re);
      Y0i : constant Element := Add (X0i, X1.Im);
      Y1r : constant Element := Sub (X0r, X1.Re);
      Y1i : constant Element := Sub (X0i, X1.Im);
      Y2r : constant Element := Add (X3.Re, X2.Re);
      Y3r : constant Element := Sub (X3.Re, X2.Re);
      Y2i : constant Element := Add (X2.Im, X3.Im);
      Y3i : constant Element := Sub (X2.Im, X3.Im);
   begin
      A (Ir) := Add (Y0r, Y2r);
      A (Ii + S) := Sub (Y0r, Y2r);
      A (Ir + S) := Add (Y1r, Y3i);
      A (Ii) := Sub (Y1r, Y3i);
      A (Ii + 3 * S) := Add (Y2i, Y0i);
      A (Ir + 2 * S) := Sub (Y2i, Y0i);
      A (Ii + 2 * S) := Add (Y3r, Y1i);
      A (Ir + 3 * S) := Sub (Y3r, Y1i);
   end Hc2hc_F_4;

   procedure Hc2r_I_4 (A : in out Element_Array; I, S : Natural) with
     Global => null,
     Pre    => A'First = 0 and then I < A'Length
               and then S <= (A'Length - 1 - I) / 3
   is
      Y0 : constant Element := Add (A (I), A (I + 2 * S));
      Y1 : constant Element := Sub (A (I), A (I + 2 * S));
      Y2 : constant Element := Add (A (I + S), A (I + S));
      Y3 : constant Element := Add (A (I + 3 * S), A (I + 3 * S));
   begin
      A (I) := Add (Y0, Y2);
      A (I + S) := Sub (Y0, Y2);
      A (I + 2 * S) := Sub (Y1, Y3);
      A (I + 3 * S) := Add (Y1, Y3);
   end Hc2r_I_4;

   procedure Hc2r_Iii_4 (A : in out Element_Array; I, S : Natural; W8 : Fp2)
   with
     Global => null,
     Pre    => A'First = 0 and then I < A'Length
               and then S <= (A'Length - 1 - I) / 3
   is
      X0 : constant Element := Add (A (I), A (I));
      X1 : constant Element := Add (A (I + S), A (I + S));
      X2 : constant Element := Add (A (I + 2 * S), A (I + 2 * S));
      X3 : constant Element := Add (A (I + 3 * S), A (I + 3 * S));
      Z0 : constant Element := Mul (Sub (X0, X1), W8.Re);
      Z1 : constant Element := Mul (Add (X3, X2), W8.Im);
   begin
      A (I) := Add (X0, X1);
      A (I + S) := Sub (X2, X3);
      A (I + 2 * S) := Sub (Z0, Z1);
      A (I + 3 * S) := Neg (Add (Z0, Z1));
   end Hc2r_Iii_4;

   procedure Hc2hc_B_4
     (A          : in out Element_Array;
      Ir, Ii, S  : Natural;
      Tw1, Tw2, Tw3 : Fp2)
   with
     Global => null,
     Pre    => A'First = 0 and then Ir < A'Length and then Ii < A'Length
               and then S <= (A'Length - 1 - Ir) / 3
               and then S <= (A'Length - 1 - Ii) / 3
   is
      X0r : constant Element := A (Ir);
      X0i : constant Element := A (Ii);
      X1r : constant Element := A (Ir + S);
      X1i : constant Element := A (Ii + S);
      X2r : constant Element := A (Ir + 2 * S);
      X2i : constant Element := A (Ii + 2 * S);
      X3r : constant Element := A (Ir + 3 * S);
      X3i : constant Element := A (Ii + 3 * S);
      Z0  : constant Element := Add (X0r, X1i);
      Z1  : constant Element := Sub (X0r, X1i);
      Z2  : constant Element := Add (X1r, X0i);
      Z3  : constant Element := Sub (X1r, X0i);
      Z4  : constant Element := Add (X3i, X2r);
      Z5  : constant Element := Sub (X3i, X2r);
      Z6  : constant Element := Add (X2i, X3r);
      Z7  : constant Element := Sub (X2i, X3r);
      O1  : constant Fp2 := Cmul (Sub (Z0, Z2), Sub (Z5, Z7), Tw2.Re, Tw2.Im);
      O2  : constant Fp2 := Cmul (Sub (Z1, Z6), Add (Z4, Z3), Tw1.Re, Tw1.Im);
      O3  : constant Fp2 := Cmul (Add (Z1, Z6), Sub (Z4, Z3), Tw3.Re, Tw3.Im);
   begin
      A (Ir) := Add (Z0, Z2);
      A (Ii) := Add (Z5, Z7);
      A (Ir + S) := O1.Re;
      A (Ii + S) := O1.Im;
      A (Ir + 2 * S) := O2.Re;
      A (Ii + 2 * S) := O2.Im;
      A (Ir + 3 * S) := O3.Re;
      A (Ii + 3 * S) := O3.Im;
   end Hc2hc_B_4;

   ----------------------------------------------------------------------
   --  The transforms, recursing on quarters
   ----------------------------------------------------------------------

   --  r2hc on A (Off .. Off + 2^L - 1), already permuted; Tab (J) is the
   --  root of order 2^L to the power J, J below 2^(L-1).
   procedure R2hc_Rec
     (A   : in out Element_Array;
      Off : Natural;
      L   : Log_Size;
      Tab : Fp2_Array)
   with
     Global            => null,
     Always_Terminates => True,
     Pre               => A'First = 0 and then Off <= A'Length
                          and then 2**L <= A'Length - Off
                          and then Tab'First = 0
                          and then Tab'Length = 2**(L - 1),
     Subprogram_Variant => (Decreases => L)
   is
   begin
      if L = 1 then
         R2hc_I_2 (A, Off, 1);
      elsif L = 2 then
         R2hc_I_4 (A, Off, 1);
      else
         declare
            Q  : constant Positive := 2**(L - 2);
            Tc : Fp2_Array (0 .. Q / 2 - 1);
         begin
            pragma Assert (2**L = 4 * Q and then 2**(L - 1) = 2 * Q);
            pragma Assert (Q >= 2 and then Q mod 2 = 0);
            Quarter (Tab, Tc);
            R2hc_Rec (A, Off, L - 2, Tc);
            R2hc_Rec (A, Off + Q, L - 2, Tc);
            R2hc_Rec (A, Off + 2 * Q, L - 2, Tc);
            R2hc_Rec (A, Off + 3 * Q, L - 2, Tc);
            R2hc_I_4 (A, Off, Q);
            for J in 1 .. Q / 2 - 1 loop
               Hc2hc_F_4 (A, Off + J, Off + Q - J, Q,
                          Tab (J), Tab (2 * J), Tab (3 * J));
            end loop;
            R2hc_Ii_4 (A, Off + Q / 2, Q, Tab (Q / 2));
         end;
      end if;
   end R2hc_Rec;

   --  hc2r on A (Off .. Off + 2^L - 1), before the final permutation.
   procedure Hc2r_Rec
     (A   : in out Element_Array;
      Off : Natural;
      L   : Log_Size;
      Tab : Fp2_Array)
   with
     Global            => null,
     Always_Terminates => True,
     Pre               => A'First = 0 and then Off <= A'Length
                          and then 2**L <= A'Length - Off
                          and then Tab'First = 0
                          and then Tab'Length = 2**(L - 1),
     Subprogram_Variant => (Decreases => L)
   is
   begin
      if L = 1 then
         R2hc_I_2 (A, Off, 1);
      elsif L = 2 then
         Hc2r_I_4 (A, Off, 1);
      else
         declare
            Q  : constant Positive := 2**(L - 2);
            Tc : Fp2_Array (0 .. Q / 2 - 1);
         begin
            pragma Assert (2**L = 4 * Q and then 2**(L - 1) = 2 * Q);
            pragma Assert (Q >= 2 and then Q mod 2 = 0);
            Hc2r_I_4 (A, Off, Q);
            for J in 1 .. Q / 2 - 1 loop
               Hc2hc_B_4 (A, Off + J, Off + Q - J, Q,
                          Tab (J), Tab (2 * J), Tab (3 * J));
            end loop;
            Hc2r_Iii_4 (A, Off + Q / 2, Q, Tab (Q / 2));
            Quarter (Tab, Tc);
            Hc2r_Rec (A, Off, L - 2, Tc);
            Hc2r_Rec (A, Off + Q, L - 2, Tc);
            Hc2r_Rec (A, Off + 2 * Q, L - 2, Tc);
            Hc2r_Rec (A, Off + 3 * Q, L - 2, Tc);
         end;
      end if;
   end Hc2r_Rec;

   procedure R2hc (A : in out Element_Array; L : Log_Size) is
   begin
      if L = 1 then
         R2hc_I_2 (A, 0, 1);
         return;
      end if;
      declare
         T : Fp2_Access := new Fp2_Array'(0 .. 2**(L - 1) - 1 => One2);
      begin
         Powers (Reroot (L), T.all);
         Bitrev (A, L);
         R2hc_Rec (A, 0, L, T.all);
         Free_Fp2 (T);
      end;
   end R2hc;

   procedure Hc2r (A : in out Element_Array; L : Log_Size) is
   begin
      if L = 1 then
         R2hc_I_2 (A, 0, 1);
         return;
      end if;
      declare
         T : Fp2_Access := new Fp2_Array'(0 .. 2**(L - 1) - 1 => One2);
      begin
         Powers (Reroot (L), T.all);
         Hc2r_Rec (A, 0, L, T.all);
         Bitrev (A, L);
         Free_Fp2 (T);
      end;
   end Hc2r;

   ----------------------------------------------------------------------
   --  Extend (reed_solomon.rs, ReedSolomon::new and interpolate, with the
   --  middle product of middle_product.rs, FFTExtMiddleProduct)
   ----------------------------------------------------------------------

   procedure Extend (Row : Element_Array; Enc : out Element_Array) is
      N   : constant Positive := Row'Length;
      M   : constant Positive := Enc'Length;
      D   : constant Natural := N - 1;
      L   : Natural := 1;
      Len : Positive := 2;
   begin
      Enc := [others => Zero];
      for X in 0 .. N - 1 loop
         Enc (X) := Row (X);
         pragma Loop_Invariant
           (for all X2 in 0 .. X => Field_P256.Same (Enc (X2), Row (X2)));
      end loop;
      if M = N then
         return;
      end if;

      --  P = 2^L, the smallest power of two at least M, and at least 2.
      while L < 16 and then Len < M loop
         pragma Loop_Invariant (Len = 2**L and then Len < M and then L >= 1);
         pragma Loop_Variant (Increases => L);
         L   := L + 1;
         Len := 2 * Len;
      end loop;
      --  Not taken: M is at most 2^16. The provers do not evaluate 2^16
      --  for a variable exponent, so the case stays, and returns the
      --  systematic part alone.
      if Len < M then
         return;
      end if;
      pragma Assert (Len = 2**L and then M <= Len and then L in Log_Size);

      declare
         Inv_T : Elems_Access := new Element_Array'(0 .. M - 1 => Zero);
         Pre_T : Elems_Access := new Element_Array'(0 .. M - 1 => One);
         Lead  : Elems_Access := new Element_Array'(0 .. M - N => Zero);
         Xf    : Elems_Access := new Element_Array'(0 .. Len - 1 => Zero);
         Yf    : Elems_Access := new Element_Array'(0 .. Len - 1 => Zero);
         All_I : Element;
         Deg   : Element;
         Fac   : Element;
         Binom : Element;
         Bv    : Element;
         Inv_P : Element;
      begin
         --  inverses (t) = 1 / t for t = 1 .. M - 1 (batch inverse).
         for T in 1 .. M - 1 loop
            Pre_T (T) := Mul (Pre_T (T - 1), Of_Natural (T));
         end loop;
         All_I := Inv (Pre_T (M - 1));
         for T in reverse 1 .. M - 1 loop
            Inv_T (T) := Mul (All_I, Pre_T (T - 1));
            All_I := Mul (All_I, Of_Natural (T));
         end loop;

         --  leading_constant (i) = C(i + d, d), then times (k - d) and
         --  the sign (-1)^d, k = i + d.
         Lead (0) := One;
         Deg := Of_Natural (D + 1);
         for I in 1 .. M - N loop
            Lead (I) := Mul (Lead (I - 1), Mul (Deg, Inv_T (I)));
            Deg := Add (Deg, One);
         end loop;
         Fac := Zero;
         for Idx in 0 .. M - N loop
            Lead (Idx) := Mul (Lead (Idx), Fac);
            if D mod 2 = 1 then
               Lead (Idx) := Neg (Lead (Idx));
            end if;
            Fac := Add (Fac, One);
         end loop;

         --  x_j = (-1)^j C(d, j) p(j), into the first operand.
         Binom := One;
         Bv := Of_Natural (D);
         for J in 0 .. N - 1 loop
            if J > 0 then
               Binom := Mul (Binom, Mul (Bv, Inv_T (J)));
               Bv := Sub (Bv, One);
            end if;
            Xf (J) := (if J mod 2 = 1 then Neg (Mul (Binom, Row (J)))
                       else Mul (Binom, Row (J)));
         end loop;

         --  The second operand, the inverses, transformed and scaled by
         --  1 / P (FFTExtMiddleProduct::new).
         for T in 0 .. M - 1 loop
            Yf (T) := Inv_T (T);
         end loop;
         R2hc (Yf.all, L);
         Inv_P := Inv (Of_Natural (Len));
         for T in 0 .. Len - 1 loop
            Yf (T) := Mul (Yf (T), Inv_P);
         end loop;

         --  The product on the half-complex pairs, then back.
         R2hc (Xf.all, L);
         Xf (0) := Mul (Xf (0), Yf (0));
         for K in 1 .. Len / 2 - 1 loop
            declare
               Z : constant Fp2 :=
                 Cmul (Xf (K), Xf (Len - K), Yf (K), Yf (Len - K));
            begin
               Xf (K) := Z.Re;
               Xf (Len - K) := Z.Im;
            end;
         end loop;
         Xf (Len / 2) := Mul (Xf (Len / 2), Yf (Len / 2));
         Hc2r (Xf.all, L);

         for K in N .. M - 1 loop
            Enc (K) := Mul (Lead (K - D), Xf (K));
            pragma Loop_Invariant
              (for all X2 in 0 .. N - 1 =>
                 Field_P256.Same (Enc (X2), Row (X2)));
         end loop;

         Free_Elems (Inv_T);
         Free_Elems (Pre_T);
         Free_Elems (Lead);
         Free_Elems (Xf);
         Free_Elems (Yf);
      end;
   end Extend;

end Rfft_P256;
