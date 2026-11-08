pragma SPARK_Mode (On);

package body Mdoc_Mac is

   function Legacy_Tags (Av : Element; Ap : Pads; M : Messages) return Tags
   is
      T : Tags := [others => Zero];
   begin
      for I in Message_Index loop
         T (2 * I)     := Mul (Add (Av, Ap (I) (0)), Half (M (I), 0));
         T (2 * I + 1) := Mul (Add (Av, Ap (I) (1)), Half (M (I), 1));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              T (2 * J) = Mul (Add (Av, Ap (J) (0)), Half (M (J), 0))
              and then T (2 * J + 1)
                = Mul (Add (Av, Ap (J) (1)), Half (M (J), 1)));
      end loop;
      return T;
   end Legacy_Tags;

end Mdoc_Mac;
