pragma SPARK_Mode (Off);

with Interfaces; use Interfaces;
with Sha256;

package body Checker_Facts is

   package CC renames Circuit_Certificates;
   use type SA.Element;

   type Shape_Ptr is access CK.Shape_Array;
   type Coef_Ptr is access CK.Coef_Array;
   type Flag_Ptr is access CK.Flag_Array;
   type Mono_Ptr is access CK.Mono_Array;
   type Pool_Ptr is access CK.Coef_Pool;

   procedure Put_U32 (Ctx : in out Sha256.Context; V : Natural) is
      X : constant Unsigned_32 := Unsigned_32 (V);
   begin
      Sha256.Update
        (Ctx, [0 => Unsigned_8 (X and 255),
               1 => Unsigned_8 (Shift_Right (X, 8) and 255),
               2 => Unsigned_8 (Shift_Right (X, 16) and 255),
               3 => Unsigned_8 (Shift_Right (X, 24))]);
   end Put_U32;

   procedure Put_Tag (Ctx : in out Sha256.Context; C : Character) is
   begin
      Sha256.Update (Ctx, [0 => Character'Pos (C)]);
   end Put_Tag;

   procedure Put_Elt (Ctx : in out Sha256.Context; E : SA.Element) is
   begin
      Sha256.Update (Ctx, To_Bytes (E));
   end Put_Elt;

   --  A meaning: the number of its entries, then each entry, the
   --  variable and then the coefficient.
   procedure Put_Form
     (Ctx : in out Sha256.Context; Sh : CK.Form_Shape; Cf : CK.Coef_List) is
   begin
      Put_U32 (Ctx, Sh.N);
      for E in 1 .. Sh.N loop
         Put_U32 (Ctx, Sh.V (E));
         Put_Elt (Ctx, Cf (E));
      end loop;
   end Put_Form;

   --  The digest of the facts of P with the accepted certificate K: for
   --  each layer from the last, its assertions in term order, then its
   --  declared wires; then the outputs.
   function Facts_Digest
     (P : PC.Packed_Circuit; K : Circuit_Certificates.Certificate)
      return Bytes.Bytes_32
   is
      Ctx  : Sha256.Context := Sha256.Initial;
      M    : Shape_Ptr := new CK.Shape_Array'(CK.Input_Shapes (P));
      CM   : Coef_Ptr := new CK.Coef_Array'(CK.Input_Coefs (P));
      Mono : constant Mono_Ptr :=
        new CK.Mono_Array'(1 .. Pool_Size => (A => 0, B => 0));
      C    : constant Pool_Ptr :=
        new CK.Coef_Pool'(1 .. Pool_Size => SA.Zero);
      Vb   : Natural := P.Ninput;
      Fits : Boolean;
   begin
      for J in reverse 0 .. P.Last_Layer loop
         declare
            NO   : constant Natural := CK.Out_Count (P, J);
            S    : constant CC.Layer_Span := K.Layers (CK.Walk_Index (P, J));
            NM   : constant Shape_Ptr :=
              new CK.Shape_Array'(0 .. NO - 1 => CK.No_Shape);
            NC   : constant Coef_Ptr :=
              new CK.Coef_Array'(0 .. NO - 1 => CK.No_Coefs);
            Lin  : constant Flag_Ptr :=
              new CK.Flag_Array'(0 .. NO - 1 => False);
            Cur  : PC.Cursor := PC.Start (P, J);
            Tm   : SA.Term;
            Base : Natural := 0;
            Decl : Natural := 0;
         begin
            CK.Layer_Coefficients (P, K, J, M.all, CM.all, Mono.all, C.all,
                                   Fits);
            if not Fits then
               raise Program_Error with "an accepted layer does not fit";
            end if;
            for N in 1 .. CK.Len (P, J) loop
               Tm := PC.Term_Of (P, Cur);
               Cur := PC.Step (P, Cur);
               if Tm.K = SA.Zero then
                  Put_Tag (Ctx, 'A');
                  Put_Form (Ctx, M (Tm.H1), CM (Tm.H1));
                  Put_Form (Ctx, M (Tm.H0), CM (Tm.H0));
               end if;
            end loop;
            CK.Next_Layer (P, K, J, Vb, Mono.all, C.all, NM.all, NC.all,
                           Lin.all);
            for G in 0 .. NO - 1 loop
               declare
                  Cnt : constant Natural := K.Counts (S.First_Wire + G + 1);
               begin
                  if not Lin (G) then
                     Put_Tag (Ctx, 'D');
                     Put_U32 (Ctx, NM (G).V (1));
                     Put_U32 (Ctx, Cnt);
                     for X in 1 .. Cnt loop
                        Put_U32 (Ctx, Mono (Base + X).A);
                        Put_U32 (Ctx, Mono (Base + X).B);
                        Put_Elt (Ctx, C (Base + X));
                     end loop;
                     Decl := Decl + 1;
                  end if;
                  Base := Base + Cnt;
               end;
            end loop;
            if J = 0 then
               for G in 0 .. NO - 1 loop
                  Put_Tag (Ctx, 'O');
                  Put_U32 (Ctx, G);
                  Put_Form (Ctx, NM (G), NC (G));
               end loop;
            end if;
            M := NM;
            CM := NC;
            Vb := Vb + Decl;
         end;
      end loop;
      return Sha256.Digest (Ctx);
   end Facts_Digest;

end Checker_Facts;
