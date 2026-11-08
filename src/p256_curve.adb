pragma SPARK_Mode (On);

package body P256_Curve is

   use P256_Field;

   --  3 b, as upstream computes it (b + b + b) on every call.
   function Three_B return Element is
     (Add (Coef_B, Add (Coef_B, Coef_B)))
   with Global => null;

   function Affine (P : Point) return Affine_Point is
      Zi : constant Element := Inv (P.Z);
   begin
      return (X => Mul (P.X, Zi), Y => Mul (P.Y, Zi));
   end Affine;

   --  ec.rs add: the variables keep upstream's names and order, so that
   --  a reader can follow the two side by side.
   function Add (P1, P2 : Point) return Point is
      A   : constant Element := Coef_A;
      K3B : constant Element := Three_B;
      T0  : constant Element := Mul (P1.X, P2.X);
      T1  : constant Element := Mul (P1.Y, P2.Y);
      T2  : constant Element := Mul (P1.Z, P2.Z);
      T3A : constant Element := Add (P1.X, P1.Y);
      T4A : constant Element := Add (P2.X, P2.Y);
      T3B : constant Element := Mul (T3A, T4A);
      T4B : constant Element := Add (T0, T1);
      T3C : constant Element := Sub (T3B, T4B);
      T4C : constant Element := Add (P1.X, P1.Z);
      T5A : constant Element := Add (P2.X, P2.Z);
      T4D : constant Element := Mul (T4C, T5A);
      T5B : constant Element := Add (T0, T2);
      T4E : constant Element := Sub (T4D, T5B);
      T5C : constant Element := Add (P1.Y, P1.Z);
      X3T : constant Element := Add (P2.Y, P2.Z);
      T5D : constant Element := Mul (T5C, X3T);
      X3B : constant Element := Add (T1, T2);
      T5E : constant Element := Sub (T5D, X3B);
      Z3A : constant Element := Mul (A, T4E);
      X3C : constant Element := Mul (K3B, T2);
      Z3B : constant Element := Add (X3C, Z3A);
      X3D : constant Element := Sub (T1, Z3B);
      Z3C : constant Element := Add (T1, Z3B);
      Y3A : constant Element := Mul (X3D, Z3C);
      T1A : constant Element := Add (T0, T0);
      T1B : constant Element := Add (T1A, T0);
      T2A : constant Element := Mul (A, T2);
      T4F : constant Element := Mul (K3B, T4E);
      T1C : constant Element := Add (T1B, T2A);
      T2B : constant Element := Sub (T0, T2A);
      T2C : constant Element := Mul (A, T2B);
      T4G : constant Element := Add (T4F, T2C);
      T0A : constant Element := Mul (T1C, T4G);
      Y3B : constant Element := Add (Y3A, T0A);
      T0B : constant Element := Mul (T5E, T4G);
      X3E : constant Element := Mul (T3C, X3D);
      X3R : constant Element := Sub (X3E, T0B);
      T0C : constant Element := Mul (T3C, T1C);
      Z3D : constant Element := Mul (T5E, Z3C);
      Z3R : constant Element := Add (Z3D, T0C);
   begin
      return (X => X3R, Y => Y3B, Z => Z3R);
   end Add;

   --  ec.rs double.
   function Double (P : Point) return Point is
      A   : constant Element := Coef_A;
      K3B : constant Element := Three_B;
      T0A : constant Element := Mul (P.X, P.X);
      T1  : constant Element := Mul (P.Y, P.Y);
      T2A : constant Element := Mul (P.Z, P.Z);
      T3A : constant Element := Mul (P.X, P.Y);
      T3B : constant Element := Add (T3A, T3A);
      Z3A : constant Element := Mul (P.X, P.Z);
      Z3B : constant Element := Add (Z3A, Z3A);
      X3A : constant Element := Mul (A, Z3B);
      Y3T : constant Element := Mul (K3B, T2A);
      Y3A : constant Element := Add (X3A, Y3T);
      X3B : constant Element := Sub (T1, Y3A);
      Y3B : constant Element := Add (T1, Y3A);
      Y3C : constant Element := Mul (X3B, Y3B);
      X3C : constant Element := Mul (T3B, X3B);
      Z3C : constant Element := Mul (K3B, Z3B);
      T2B : constant Element := Mul (A, T2A);
      T3C : constant Element := Sub (T0A, T2B);
      T3D : constant Element := Mul (A, T3C);
      T3E : constant Element := Add (T3D, Z3C);
      Z3D : constant Element := Add (T0A, T0A);
      T0B : constant Element := Add (Z3D, T0A);
      T0C : constant Element := Add (T0B, T2B);
      T0D : constant Element := Mul (T0C, T3E);
      Y3R : constant Element := Add (Y3C, T0D);
      T2C : constant Element := Mul (P.Y, P.Z);
      T2D : constant Element := Add (T2C, T2C);
      T0E : constant Element := Mul (T2D, T3E);
      X3R : constant Element := Sub (X3C, T0E);
      Z3E : constant Element := Mul (T2D, T1);
      Z3F : constant Element := Add (Z3E, Z3E);
      Z3R : constant Element := Add (Z3F, Z3F);
   begin
      return (X => X3R, Y => Y3R, Z => Z3R);
   end Double;

   --  D or -D has its top bit set exactly when D is not zero.
   function Mask_Of_Zero (D : Unsigned_64) return Unsigned_64 is
      NZ : constant Unsigned_64 := Shift_Right (D or (0 - D), 63);
   begin
      pragma Assert (NZ = (if D = 0 then 0 else 1));
      return NZ - 1;
   end Mask_Of_Zero;

   function Select_Element (A, B : Element; Mask : Unsigned_64)
     return Element
   is
      Keep : constant Unsigned_64 := not Mask;
   begin
      return (L0 => (A.L0 and Keep) or (B.L0 and Mask),
              L1 => (A.L1 and Keep) or (B.L1 and Mask),
              L2 => (A.L2 and Keep) or (B.L2 and Mask),
              L3 => (A.L3 and Keep) or (B.L3 and Mask));
   end Select_Element;

   function Select_Point (A, B : Point; Mask : Unsigned_64) return Point is
     (X => Select_Element (A.X, B.X, Mask),
      Y => Select_Element (A.Y, B.Y, Mask),
      Z => Select_Element (A.Z, B.Z, Mask));

   function Select_8 (T : Point_Table; I : Table_Index) return Point is
      R : Point := T (0);
      M : Unsigned_64;
   begin
      for K in Table_Index range 1 .. 7 loop
         M := Mask_Of_Zero (Unsigned_64 (I) xor Unsigned_64 (K));
         R := Select_Point (R, T (K), M);
         pragma Loop_Invariant (R = (if I <= K then T (I) else T (0)));
      end loop;
      return R;
   end Select_8;

   function Scalar_Mul (K : Limb_Array; P : Point) return Point is
      Res  : Point := Infinity;
      Tmp  : Point := P;
      Bit  : Unsigned_64;
      Mask : Unsigned_64;
   begin
      for I in 0 .. 255 loop
         Bit  := Shift_Right (K (I / 64), I mod 64) and 1;
         Mask := 0 - Bit;
         Res  := Select_Point (Res, Add (Res, Tmp), Mask);
         Tmp  := Double (Tmp);
      end loop;
      return Res;
   end Scalar_Mul;

end P256_Curve;
