pragma SPARK_Mode (On);

package body Clmul64 is

   subtype Cls is Natural range 0 .. 3;

   --  The positions of class C: C, C + 4, C + 8, ..., C + 60.
   function Mask (C : Cls) return U64 is
     (Shift_Left (16#1111_1111_1111_1111#, C))
   with Global => null;

   -------------------------------------------------------------------
   --  Bits, digits and carries
   -------------------------------------------------------------------

   function Bit (V : U64; K : Natural) return U64 is
     (Shift_Right (V, K) and 1)
   with Ghost => Proof_Only, Global => null, Pre => K < 64;

   --  The bits of V below K.
   function Below (V : U64; K : Natural) return U64 is
     (V and (Shift_Left (1, K) - 1))
   with Ghost => Proof_Only, Global => null, Pre => K < 64;

   --  The four bits of V from K.
   function Dig (V : U64; K : Natural) return U64 is
     (Shift_Right (V, K) and 15)
   with Ghost => Proof_Only, Global => null, Pre => K < 64;

   --  P + T carries nothing into bit K.
   function No_Carry (P, T : U64; K : Natural) return Boolean is
     (Below (P, K) + Below (T, K) < Shift_Left (1, K))
   with Ghost => Proof_Only, Global => null, Pre => K < 64;

   procedure Lemma_Bit_Xor (P, T : U64; K : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => K < 64 and then No_Carry (P, T, K),
     Post   => Bit (P + T, K) = (Bit (P, K) xor Bit (T, K))
   is
   begin
      null;
   end Lemma_Bit_Xor;

   --  A window of four bits whose digits add up to at most 15.
   procedure Lemma_Window (P, T : U64; K : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => K < 60 and then No_Carry (P, T, K)
               and then Dig (P, K) + Dig (T, K) <= 15,
     Post   => No_Carry (P, T, K + 4)
               and then Dig (P + T, K) = Dig (P, K) + Dig (T, K)
   is
   begin
      null;
   end Lemma_Window;

   --  A word whose 64 bits are zero is zero, bit by bit.
   procedure Lemma_Zero (D : U64) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => (for all I in 0 .. 63 => Bit (D, I) = 0),
     Post   => D = 0
   is
   begin
      for I in 0 .. 63 loop
         pragma Assert (Bit (D, I) = 0);
         pragma Loop_Invariant
           (I = 63 or else (D and (Shift_Left (1, I + 1) - 1)) = 0);
      end loop;
   end Lemma_Zero;

   --  Two words that agree on the positions of class E agree once
   --  masked to that class.
   procedure Lemma_Ext (V, W : U64; E : Cls) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => (W and not Mask (E)) = 0
               and then (for all T in 0 .. 15 =>
                           Bit (V, 4 * T + E) = Bit (W, 4 * T + E)),
     Post   => (V and Mask (E)) = W
   is
      D : constant U64 := (V and Mask (E)) xor W;
   begin
      for I in 0 .. 63 loop
         pragma Loop_Invariant (for all J in 0 .. I - 1 => Bit (D, J) = 0);
         if I mod 4 = E then
            pragma Assert
              (Bit (V, 4 * (I / 4) + E) = Bit (W, 4 * (I / 4) + E));
         else
            pragma Assert (Bit (Mask (E), I) = 0);
         end if;
         pragma Assert (Bit (D, I) = 0);
      end loop;
      Lemma_Zero (D);
   end Lemma_Ext;

   -------------------------------------------------------------------
   --  The integer product as a sum of shifts
   -------------------------------------------------------------------

   --  The bits of Y below N (all of them from 64).
   function Low (Y : U64; N : Natural) return U64 is
     (if N >= 64 then Y else Y and (Shift_Left (1, N) - 1))
   with Ghost => Proof_Only, Global => null;

   procedure Lemma_Low_Step (Y : U64; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N < 64,
     Post   => Low (Y, N + 1)
               = Low (Y, N) + (if (Shift_Right (Y, N) and 1) = 1
                               then Shift_Left (1, N) else 0)
   is
   begin
      null;
   end Lemma_Low_Step;

   procedure Lemma_Distrib (X, U, V : U64) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => X * (U + V) = X * U + X * V
   is
   begin
      null;
   end Lemma_Distrib;

   procedure Lemma_Pow2 (X : U64; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N < 64,
     Post   => X * Shift_Left (1, N) = Shift_Left (X, N)
   is
   begin
      null;
   end Lemma_Pow2;

   --  The integer product of X by the bits of Y below N, hidden so that
   --  the multiplication stays out of the contexts of the steps.
   function Prod (X, Y : U64; N : Natural) return U64 is (X * Low (Y, N))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   procedure Lemma_Prod_Step (X, Y : U64; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N < 64,
     Post   => Prod (X, Y, N + 1)
               = Prod (X, Y, N) + (if (Shift_Right (Y, N) and 1) = 1
                                   then Shift_Left (X, N) else 0)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Prod);
   begin
      Lemma_Low_Step (Y, N);
      if (Shift_Right (Y, N) and 1) = 1 then
         pragma Assert (Low (Y, N + 1) = Low (Y, N) + Shift_Left (1, N));
         Lemma_Distrib (X, Low (Y, N), Shift_Left (1, N));
         Lemma_Pow2 (X, N);
         pragma Assert
           (X * Low (Y, N + 1) = X * (Low (Y, N) + Shift_Left (1, N)));
         pragma Assert
           (X * (Low (Y, N) + Shift_Left (1, N))
            = X * Low (Y, N) + Shift_Left (X, N));
      else
         pragma Assert (Low (Y, N + 1) = Low (Y, N));
      end if;
   end Lemma_Prod_Step;

   procedure Lemma_Prod_Ends (X, Y : U64) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Prod (X, Y, 0) = 0 and then Prod (X, Y, 64) = X * Y
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Prod);
   begin
      null;
   end Lemma_Prod_Ends;

   -------------------------------------------------------------------
   --  The product of two words of one class each
   -------------------------------------------------------------------

   function In_Class (V : U64; C : Cls) return Boolean is
     ((V and not Mask (C)) = 0)
   with Ghost => Proof_Only, Global => null;

   --  The positions J below N in class B with J <= K: a bound on the
   --  terms that reach the digit at K.
   function Cnt (N : Natural; B : Cls; K : Natural) return Natural is
     (if Natural'Min (N, K + 1) > B
      then (Natural'Min (N, K + 1) - B + 3) / 4 else 0)
   with Ghost => Proof_Only, Global => null, Pre => N <= 64 and then K < 64;

   --  The digits at E, E + 4, ..., E + 56 within their bounds.
   function Digits_Ok (P : U64; N : Natural; B, E : Cls) return Boolean is
     (for all T in 0 .. 14 =>
        Dig (P, 4 * T + E) <= U64 (Cnt (N, B, 4 * T + E)))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => N <= 64;

   --  P and R agree on the positions of class E.
   function Bits_Eq (P, R : U64; E : Cls) return Boolean is
     (for all T in 0 .. 15 => Bit (P, 4 * T + E) = Bit (R, 4 * T + E))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   procedure Lemma_Cnt_Mono (N : Natural; B : Cls) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N < 64,
     Post   => (for all K in 0 .. 63 => Cnt (N + 1, B, K) >= Cnt (N, B, K))
   is
   begin
      null;
   end Lemma_Cnt_Mono;

   procedure Lemma_Digits_Mono (P : U64; N : Natural; B, E : Cls) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N < 64 and then Digits_Ok (P, N, B, E),
     Post   => Digits_Ok (P, N + 1, B, E)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Digits_Ok);
   begin
      Lemma_Cnt_Mono (N, B);
   end Lemma_Digits_Mono;

   procedure Lemma_Digits_Zero (B, E : Cls) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Digits_Ok (0, 0, B, E)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Digits_Ok);
   begin
      null;
   end Lemma_Digits_Zero;

   procedure Lemma_Bits_Step (P, T, R : U64; E : Cls) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => Bits_Eq (P, R, E)
               and then (for all U in 0 .. 15 =>
                           Bit (P + T, 4 * U + E)
                           = (Bit (P, 4 * U + E) xor Bit (T, 4 * U + E))),
     Post   => Bits_Eq (P + T, R xor T, E)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Bits_Eq);
   begin
      pragma Assert
        (for all U in 0 .. 15 =>
           Bit (R xor T, 4 * U + E)
           = (Bit (R, 4 * U + E) xor Bit (T, 4 * U + E)));
   end Lemma_Bits_Step;

   procedure Lemma_Bits_Zero (E : Cls) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Bits_Eq (0, 0, E)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Bits_Eq);
   begin
      null;
   end Lemma_Bits_Zero;

   procedure Lemma_Ext_B (V, W : U64; E : Cls) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => (W and not Mask (E)) = 0 and then Bits_Eq (V, W, E),
     Post   => (V and Mask (E)) = W
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Bits_Eq);
   begin
      Lemma_Ext (V, W, E);
   end Lemma_Ext_B;

   --  Adding T, one bit in class E from bit N on, to a partial product
   --  whose digits are within their bounds: no digit below the top one
   --  carries, so the bits of class E add as xor.
   procedure Lemma_Add_Step (P, T : U64; N : Natural; B, E : Cls) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N < 64 and then N mod 4 = B
               and then Below (P, E) = 0 and then In_Class (T, E)
               and then Below (T, N) = 0
               and then Digits_Ok (P, N, B, E),
     Post   => Below (P + T, E) = 0
               and then Digits_Ok (P + T, N + 1, B, E)
               and then (for all U in 0 .. 15 =>
                           Bit (P + T, 4 * U + E)
                           = (Bit (P, 4 * U + E) xor Bit (T, 4 * U + E)))
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Digits_Ok);
   begin
      pragma Assert (No_Carry (P, T, E));
      for U in 0 .. 15 loop
         pragma Loop_Invariant (No_Carry (P, T, 4 * U + E));
         pragma Loop_Invariant
           (for all S in 0 .. U - 1 =>
              Bit (P + T, 4 * S + E)
              = (Bit (P, 4 * S + E) xor Bit (T, 4 * S + E)));
         pragma Loop_Invariant
           (for all S in 0 .. Natural'Min (U, 15) - 1 =>
              (if S <= 14
               then Dig (P + T, 4 * S + E)
                    <= U64 (Cnt (N + 1, B, 4 * S + E))));
         Lemma_Bit_Xor (P, T, 4 * U + E);
         if U <= 14 then
            pragma Assert
              (Dig (P, 4 * U + E) <= U64 (Cnt (N, B, 4 * U + E)));
            pragma Assert (Dig (T, 4 * U + E) <= 1);
            pragma Assert (if 4 * U + E < N then Dig (T, 4 * U + E) = 0);
            pragma Assert
              (Cnt (N + 1, B, 4 * U + E)
               = Cnt (N, B, 4 * U + E) + (if N <= 4 * U + E then 1 else 0));
            pragma Assert (Cnt (N + 1, B, 4 * U + E) <= 15);
            Lemma_Window (P, T, 4 * U + E);
            pragma Assert
              (Dig (P + T, 4 * U + E) <= U64 (Cnt (N + 1, B, 4 * U + E)));
         end if;
      end loop;
      pragma Assert (Below (P + T, E) = 0);
   end Lemma_Add_Step;

   --  The state after the bits of Y below N.
   function Inv (X, Y : U64; N : Natural; B, E : Cls) return Boolean is
     (Below (Prod (X, Y, N), E) = 0
      and then In_Class (Lo_Ref (X, Y, N), E)
      and then Bits_Eq (Prod (X, Y, N), Lo_Ref (X, Y, N), E)
      and then Digits_Ok (Prod (X, Y, N), N, B, E))
   with Ghost => Proof_Only, Global => null, Pre => N <= 64;

   procedure Lemma_Product_Step (X, Y : U64; A, B : Cls; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N < 64 and then In_Class (X, A) and then In_Class (Y, B)
               and then Inv (X, Y, N, B, (A + B) mod 4),
     Post   => Inv (X, Y, N + 1, B, (A + B) mod 4)
   is
      E : constant Cls := (A + B) mod 4;
      P : constant U64 := Prod (X, Y, N);
      R : constant U64 := Lo_Ref (X, Y, N);
   begin
      Lemma_Prod_Step (X, Y, N);
      Lemma_Cnt_Mono (N, B);
      if (Shift_Right (Y, N) and 1) = 1 then
         pragma Assert (N mod 4 = B);
         declare
            T : constant U64 := Shift_Left (X, N);
         begin
            pragma Assert (Prod (X, Y, N + 1) = P + T);
            pragma Assert (Lo_Ref (X, Y, N + 1) = (R xor T));
            pragma Assert (In_Class (T, E));
            pragma Assert (Below (T, N) = 0);
            pragma Assert (Digits_Ok (P, N, B, E));
            Lemma_Add_Step (P, T, N, B, E);
            Lemma_Bits_Step (P, T, R, E);
            pragma Assert (In_Class (R xor T, E));
         end;
      else
         pragma Assert (Prod (X, Y, N + 1) = P);
         pragma Assert (Lo_Ref (X, Y, N + 1) = R);
         Lemma_Digits_Mono (P, N, B, E);
      end if;
   end Lemma_Product_Step;

   --  The integer product of a word of class A by a word of class B,
   --  masked to class (A + B) mod 4, is the low carry-less product.
   procedure Lemma_Class_Product (X, Y : U64; A, B : Cls) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => In_Class (X, A) and then In_Class (Y, B),
     Post   => ((X * Y) and Mask ((A + B) mod 4)) = Lo_Ref (X, Y, 64)
   is
      E : constant Cls := (A + B) mod 4;
   begin
      Lemma_Prod_Ends (X, Y);
      Lemma_Bits_Zero (E);
      Lemma_Digits_Zero (B, E);
      pragma Assert (Inv (X, Y, 0, B, E));
      for N in 0 .. 63 loop
         pragma Loop_Invariant (Inv (X, Y, N, B, E));
         Lemma_Product_Step (X, Y, A, B, N);
      end loop;
      pragma Assert (Inv (X, Y, 64, B, E));
      pragma Assert (Bits_Eq (X * Y, Lo_Ref (X, Y, 64), E));
      Lemma_Ext_B (X * Y, Lo_Ref (X, Y, 64), E);
   end Lemma_Class_Product;

   -------------------------------------------------------------------
   --  The lemmas of the specification
   -------------------------------------------------------------------

   procedure Lemma_Lo_Lin_X (X1, X2, Y : U64; N : Natural) is
   begin
      if N > 0 then
         Lemma_Lo_Lin_X (X1, X2, Y, N - 1);
         pragma Assert
           (Shift_Left (X1 xor X2, N - 1)
            = (Shift_Left (X1, N - 1) xor Shift_Left (X2, N - 1)));
      end if;
   end Lemma_Lo_Lin_X;

   procedure Lemma_Lo_Lin_Y (X, Y1, Y2 : U64; N : Natural) is
   begin
      if N > 0 then
         Lemma_Lo_Lin_Y (X, Y1, Y2, N - 1);
         pragma Assert
           ((Shift_Right (Y1 xor Y2, N - 1) and 1)
            = ((Shift_Right (Y1, N - 1) and 1)
               xor (Shift_Right (Y2, N - 1) and 1)));
      end if;
   end Lemma_Lo_Lin_Y;

   procedure Lemma_Hi_Lin_X (X1, X2, Y : U64; N : Natural) is
   begin
      if N > 0 then
         Lemma_Hi_Lin_X (X1, X2, Y, N - 1);
         pragma Assert
           (Shift_Right (X1 xor X2, N)
            = (Shift_Right (X1, N) xor Shift_Right (X2, N)));
      end if;
   end Lemma_Hi_Lin_X;

   procedure Lemma_Hi_Lin_Y (X, Y1, Y2 : U64; N : Natural) is
   begin
      if N > 0 then
         Lemma_Hi_Lin_Y (X, Y1, Y2, N - 1);
         pragma Assert
           ((Shift_Right (Y1 xor Y2, 64 - N) and 1)
            = ((Shift_Right (Y1, 64 - N) and 1)
               xor (Shift_Right (Y2, 64 - N) and 1)));
      end if;
   end Lemma_Hi_Lin_Y;

   procedure Lemma_Lo_Bit (X : U64; K, N : Natural) is
   begin
      if N > 0 then
         Lemma_Lo_Bit (X, K, N - 1);
         pragma Assert
           (((Shift_Right (Shift_Left (U64'(1), K), N - 1) and 1) = 1)
            = (N - 1 = K));
      end if;
   end Lemma_Lo_Bit;

   procedure Lemma_Hi_Bit (X : U64; K, N : Natural) is
   begin
      if N > 0 then
         Lemma_Hi_Bit (X, K, N - 1);
         pragma Assert
           (((Shift_Right (Shift_Left (U64'(1), K), 64 - N) and 1) = 1)
            = (64 - N = K));
      end if;
   end Lemma_Hi_Bit;

   procedure Lemma_By_Zero (X : U64; N : Natural) is
   begin
      if N > 0 then
         Lemma_By_Zero (X, N - 1);
      end if;
   end Lemma_By_Zero;

   -------------------------------------------------------------------
   --  clmul64_lo
   -------------------------------------------------------------------

   function Clmul_Lo (X, Y : U64) return U64 is
      M0 : constant U64 := 16#1111_1111_1111_1111#;
      M1 : constant U64 := 16#2222_2222_2222_2222#;
      M2 : constant U64 := 16#4444_4444_4444_4444#;
      M3 : constant U64 := 16#8888_8888_8888_8888#;
      X0 : constant U64 := X and M0;
      X1 : constant U64 := X and M1;
      X2 : constant U64 := X and M2;
      X3 : constant U64 := X and M3;
      Y0 : constant U64 := Y and M0;
      Y1 : constant U64 := Y and M1;
      Y2 : constant U64 := Y and M2;
      Y3 : constant U64 := Y and M3;
      Z0 : constant U64 :=
        (X0 * Y0) xor (X1 * Y3) xor (X2 * Y2) xor (X3 * Y1);
      Z1 : constant U64 :=
        (X0 * Y1) xor (X1 * Y0) xor (X2 * Y3) xor (X3 * Y2);
      Z2 : constant U64 :=
        (X0 * Y2) xor (X1 * Y1) xor (X2 * Y0) xor (X3 * Y3);
      Z3 : constant U64 :=
        (X0 * Y3) xor (X1 * Y2) xor (X2 * Y1) xor (X3 * Y0);
      R  : constant U64 :=
        (Z0 and M0) or (Z1 and M1) or (Z2 and M2) or (Z3 and M3);
   begin
      pragma Assert
        (M0 = Mask (0) and then M1 = Mask (1)
         and then M2 = Mask (2) and then M3 = Mask (3));
      --  The sixteen products of one class by one class.
      Lemma_Class_Product (X0, Y0, 0, 0);
      Lemma_Class_Product (X1, Y3, 1, 3);
      Lemma_Class_Product (X2, Y2, 2, 2);
      Lemma_Class_Product (X3, Y1, 3, 1);
      Lemma_Class_Product (X0, Y1, 0, 1);
      Lemma_Class_Product (X1, Y0, 1, 0);
      Lemma_Class_Product (X2, Y3, 2, 3);
      Lemma_Class_Product (X3, Y2, 3, 2);
      Lemma_Class_Product (X0, Y2, 0, 2);
      Lemma_Class_Product (X1, Y1, 1, 1);
      Lemma_Class_Product (X2, Y0, 2, 0);
      Lemma_Class_Product (X3, Y3, 3, 3);
      Lemma_Class_Product (X0, Y3, 0, 3);
      Lemma_Class_Product (X1, Y2, 1, 2);
      Lemma_Class_Product (X2, Y1, 2, 1);
      Lemma_Class_Product (X3, Y0, 3, 0);
      pragma Assert
        (Proof_Only =>
           R = (Lo_Ref (X0, Y0, 64) xor Lo_Ref (X1, Y3, 64)
                xor Lo_Ref (X2, Y2, 64) xor Lo_Ref (X3, Y1, 64)
                xor Lo_Ref (X0, Y1, 64) xor Lo_Ref (X1, Y0, 64)
                xor Lo_Ref (X2, Y3, 64) xor Lo_Ref (X3, Y2, 64)
                xor Lo_Ref (X0, Y2, 64) xor Lo_Ref (X1, Y1, 64)
                xor Lo_Ref (X2, Y0, 64) xor Lo_Ref (X3, Y3, 64)
                xor Lo_Ref (X0, Y3, 64) xor Lo_Ref (X1, Y2, 64)
                xor Lo_Ref (X2, Y1, 64) xor Lo_Ref (X3, Y0, 64)));
      --  The sixteen low words add up to the product of X by Y, by
      --  linearity over the classes of X and of Y.
      pragma Assert (X = (X0 xor X1 xor X2 xor X3));
      pragma Assert (Y = (Y0 xor Y1 xor Y2 xor Y3));
      Lemma_Lo_Lin_X (X0 xor X1 xor X2, X3, Y, 64);
      Lemma_Lo_Lin_X (X0 xor X1, X2, Y, 64);
      Lemma_Lo_Lin_X (X0, X1, Y, 64);
      Lemma_Lo_Lin_Y (X0, Y0 xor Y1 xor Y2, Y3, 64);
      Lemma_Lo_Lin_Y (X0, Y0 xor Y1, Y2, 64);
      Lemma_Lo_Lin_Y (X0, Y0, Y1, 64);
      Lemma_Lo_Lin_Y (X1, Y0 xor Y1 xor Y2, Y3, 64);
      Lemma_Lo_Lin_Y (X1, Y0 xor Y1, Y2, 64);
      Lemma_Lo_Lin_Y (X1, Y0, Y1, 64);
      Lemma_Lo_Lin_Y (X2, Y0 xor Y1 xor Y2, Y3, 64);
      Lemma_Lo_Lin_Y (X2, Y0 xor Y1, Y2, 64);
      Lemma_Lo_Lin_Y (X2, Y0, Y1, 64);
      Lemma_Lo_Lin_Y (X3, Y0 xor Y1 xor Y2, Y3, 64);
      Lemma_Lo_Lin_Y (X3, Y0 xor Y1, Y2, 64);
      Lemma_Lo_Lin_Y (X3, Y0, Y1, 64);
      return R;
   end Clmul_Lo;

   -------------------------------------------------------------------
   --  clmul64_hi, by bit reversal
   -------------------------------------------------------------------

   --  reverse_bits: bit I of the result is bit 63 - I of V.
   function Rev (V : U64) return U64 with
     Global => null,
     Post   => (Proof_Only =>
                  (for all I in 0 .. 63 =>
                     Bit (Rev'Result, I) = Bit (V, 63 - I)));

   function Rev (V : U64) return U64 is
      X : U64 := V;
   begin
      X := Shift_Right (X and 16#AAAA_AAAA_AAAA_AAAA#, 1)
           or Shift_Left (X and 16#5555_5555_5555_5555#, 1);
      X := Shift_Right (X and 16#CCCC_CCCC_CCCC_CCCC#, 2)
           or Shift_Left (X and 16#3333_3333_3333_3333#, 2);
      X := Shift_Right (X and 16#F0F0_F0F0_F0F0_F0F0#, 4)
           or Shift_Left (X and 16#0F0F_0F0F_0F0F_0F0F#, 4);
      X := Shift_Right (X and 16#FF00_FF00_FF00_FF00#, 8)
           or Shift_Left (X and 16#00FF_00FF_00FF_00FF#, 8);
      X := Shift_Right (X and 16#FFFF_0000_FFFF_0000#, 16)
           or Shift_Left (X and 16#0000_FFFF_0000_FFFF#, 16);
      X := Shift_Right (X, 32) or Shift_Left (X, 32);
      return X;
   end Rev;

   procedure Lemma_Rev_Shift (V : U64; K : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => K < 64,
     Post   => Rev (Shift_Left (V, K)) = Shift_Right (Rev (V), K)
   is
      D : constant U64 := Rev (Shift_Left (V, K)) xor Shift_Right (Rev (V), K);
   begin
      for I in 0 .. 63 loop
         pragma Loop_Invariant (for all J in 0 .. I - 1 => Bit (D, J) = 0);
         pragma Assert
           (Bit (Rev (Shift_Left (V, K)), I)
            = Bit (Shift_Left (V, K), 63 - I));
         if I + K <= 63 then
            pragma Assert
              (Bit (Shift_Left (V, K), 63 - I) = Bit (V, 63 - I - K));
            pragma Assert
              (Bit (Shift_Right (Rev (V), K), I) = Bit (Rev (V), I + K));
            pragma Assert (Bit (Rev (V), I + K) = Bit (V, 63 - I - K));
         else
            pragma Assert (Bit (Shift_Left (V, K), 63 - I) = 0);
            pragma Assert (Bit (Shift_Right (Rev (V), K), I) = 0);
         end if;
         pragma Assert (Bit (D, I) = 0);
      end loop;
      Lemma_Zero (D);
   end Lemma_Rev_Shift;

   procedure Lemma_Rev_Xor (A, B : U64) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Rev (A xor B) = (Rev (A) xor Rev (B))
   is
      D : constant U64 := Rev (A xor B) xor (Rev (A) xor Rev (B));
   begin
      for I in 0 .. 63 loop
         pragma Loop_Invariant (for all J in 0 .. I - 1 => Bit (D, J) = 0);
         pragma Assert (Bit (D, I) = 0);
      end loop;
      Lemma_Zero (D);
   end Lemma_Rev_Xor;

   procedure Lemma_Rev_Zero with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Rev (0) = 0
   is
      D : constant U64 := Rev (0);
   begin
      for I in 0 .. 63 loop
         pragma Loop_Invariant (for all J in 0 .. I - 1 => Bit (D, J) = 0);
         pragma Assert (Bit (D, I) = Bit (0, 63 - I));
      end loop;
      Lemma_Zero (D);
   end Lemma_Rev_Zero;

   procedure Lemma_Rev_Rev (A : U64) with
     Ghost  => Proof_Only,
     Global => null,
     Post   => Rev (Rev (A)) = A
   is
      D : constant U64 := Rev (Rev (A)) xor A;
   begin
      for I in 0 .. 63 loop
         pragma Loop_Invariant (for all J in 0 .. I - 1 => Bit (D, J) = 0);
         pragma Assert (Bit (Rev (Rev (A)), I) = Bit (Rev (A), 63 - I));
         pragma Assert (Bit (D, I) = 0);
      end loop;
      Lemma_Zero (D);
   end Lemma_Rev_Rev;

   --  The low word of the reversed operands, reversed and shifted
   --  right by one, is the high word.
   procedure Lemma_Hi_Rev (X, Y : U64; N : Natural) with
     Ghost  => Proof_Only,
     Global => null,
     Pre    => N <= 64,
     Post   => Shift_Right (Rev (Lo_Ref (Rev (X), Rev (Y), N)), 1)
               = Hi_Ref (X, Y, N),
     Subprogram_Variant => (Decreases => N)
   is
   begin
      if N > 0 then
         Lemma_Hi_Rev (X, Y, N - 1);
         declare
            RX : constant U64 := Rev (X);
            L  : constant U64 := Lo_Ref (RX, Rev (Y), N - 1);
            S  : constant U64 := Shift_Left (RX, N - 1);
         begin
            pragma Assert (Bit (Rev (Y), N - 1) = Bit (Y, 64 - N));
            Lemma_Rev_Shift (RX, N - 1);
            Lemma_Rev_Rev (X);
            pragma Assert (Rev (S) = Shift_Right (X, N - 1));
            if (Shift_Right (Y, 64 - N) and 1) = 1 then
               pragma Assert (Lo_Ref (RX, Rev (Y), N) = (L xor S));
               Lemma_Rev_Xor (L, S);
               pragma Assert
                 (Rev (L xor S) = (Rev (L) xor Shift_Right (X, N - 1)));
               pragma Assert
                 (Shift_Right (Rev (L) xor Shift_Right (X, N - 1), 1)
                  = (Shift_Right (Rev (L), 1)
                     xor Shift_Right (Shift_Right (X, N - 1), 1)));
               pragma Assert
                 (Shift_Right (Shift_Right (X, N - 1), 1)
                  = Shift_Right (X, N));
               pragma Assert
                 (Shift_Right (Rev (L xor S), 1)
                  = (Shift_Right (Rev (L), 1) xor Shift_Right (X, N)));
               pragma Assert
                 (Hi_Ref (X, Y, N)
                  = (Hi_Ref (X, Y, N - 1) xor Shift_Right (X, N)));
               pragma Assert
                 (Shift_Right (Rev (Lo_Ref (RX, Rev (Y), N)), 1)
                  = Hi_Ref (X, Y, N));
            else
               pragma Assert (Lo_Ref (RX, Rev (Y), N) = L);
               pragma Assert (Hi_Ref (X, Y, N) = Hi_Ref (X, Y, N - 1));
            end if;
         end;
      else
         Lemma_Rev_Zero;
      end if;
   end Lemma_Hi_Rev;

   function Clmul_Hi (X, Y : U64) return U64 is
   begin
      Lemma_Hi_Rev (X, Y, 64);
      return Shift_Right (Rev (Clmul_Lo (Rev (X), Rev (Y))), 1);
   end Clmul_Hi;

end Clmul64;
