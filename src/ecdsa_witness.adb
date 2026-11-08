pragma SPARK_Mode (On);

package body Ecdsa_Witness is

   package PF renames P256_Field;
   package QF renames Q256_Field;
   package PC renames P256_Curve;

   --  Back from the scalar field's word array.
   function Of_Q (L : QF.Limb_Array) return Nat_256 is
     ([L (0), L (1), L (2), L (3)])
   with Global => null;

   procedure Push_Legacy
     (Pk    : PC.Affine_Point;
      E, R, S : Nat_256;
      W     : in out SAP.Element_Array;
      First : Natural)
   is
      --  The scalars e s^-1 and r s^-1 mod q, and -s mod q.
      S_Q   : constant QF.Element := QF.From_Canonical (To_Q (S));
      S_Inv : constant QF.Element := QF.Inv (S_Q);
      Nes   : constant Nat_256 :=
        Of_Q (QF.To_Canonical (QF.Mul (QF.From_Canonical (To_Q (E)), S_Inv)));
      Nrs   : constant Nat_256 :=
        Of_Q (QF.To_Canonical (QF.Mul (QF.From_Canonical (To_Q (R)), S_Inv)));
      Nms   : constant Nat_256 := Of_Q (QF.To_Canonical (QF.Neg (S_Q)));

      G   : constant PC.Point := PC.Base_Point;
      PKP : constant PC.Point := PC.To_Point (Pk);

      --  R = e s^-1 G + r s^-1 Pk: rx from r, ry from the point.
      R_Proj : constant PC.Point :=
        PC.Add (PC.Scalar_Mul (Nes, G), PC.Scalar_Mul (Nrs, PKP));
      Rx     : constant PF.Element := PF.From_Canonical (R);
      Ry     : constant PF.Element :=
        PF.Mul (R_Proj.Y, PF.Inv (R_Proj.Z));
      R_Pt   : constant PC.Point := (X => Rx, Y => Ry, Z => PF.One);

      G_Pk   : constant PC.Affine_Point := PC.Affine (PC.Add (G, PKP));
      G_R    : constant PC.Affine_Point := PC.Affine (PC.Add (G, R_Pt));
      Pk_R   : constant PC.Affine_Point := PC.Affine (PC.Add (PKP, R_Pt));
      G_Pk_R : constant PC.Affine_Point :=
        PC.Affine (PC.Add (G, PC.To_Point (Pk_R)));

      Nms_P : constant PF.Element := PF.From_Canonical (Nms);

      T : constant PC.Point_Table :=
        [0 => PC.Infinity,
         1 => R_Pt,
         2 => PKP,
         3 => PC.To_Point (Pk_R),
         4 => G,
         5 => PC.To_Point (G_R),
         6 => PC.To_Point (G_Pk),
         7 => PC.To_Point (G_Pk_R)];

      P   : PC.Point := PC.Infinity;
      B   : Natural;
      Pos : Natural;
   begin
      W (First)      := Rx;
      W (First + 1)  := Ry;
      W (First + 2)  := PF.Inv (Rx);
      W (First + 3)  := PF.Inv (Nms_P);
      W (First + 4)  := PF.Inv (Pk.X);
      W (First + 5)  := G_Pk.X;
      W (First + 6)  := G_Pk.Y;
      W (First + 7)  := G_R.X;
      W (First + 8)  := G_R.Y;
      W (First + 9)  := Pk_R.X;
      W (First + 10) := Pk_R.Y;
      W (First + 11) := G_Pk_R.X;
      W (First + 12) := G_Pk_R.Y;
      --  Round I handles bit 255 - I: its digit at First + 13 + 4 I,
      --  then the point after the round, except for the last.
      for I in 0 .. 255 loop
         pragma Loop_Invariant
           (for all J in W'Range =>
              (if J < First or else J > First + Count - 1
               then W (J) = W'Loop_Entry (J)));
         B   := Digit (E, R, Nms, 255 - I);
         P   := PC.Add (PC.Double (P),
                        PC.Select_8 (T, Table_Index_Of (E, R, Nms, 255 - I)));
         Pos := First + 13 + 4 * I;
         W (Pos) := Digit_Element (B);
         if I < 255 then
            W (Pos + 1) := P.X;
            W (Pos + 2) := P.Y;
            W (Pos + 3) := P.Z;
         end if;
      end loop;
   end Push_Legacy;

end Ecdsa_Witness;
