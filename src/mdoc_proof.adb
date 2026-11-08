pragma SPARK_Mode (On);

package body Mdoc_Proof is

   procedure Write_Tags (T : Tags; B : out Byte_Array) is
   begin
      B := [others => 0];
      for I in Tag_Index loop
         B (Tag_Bytes * I .. Tag_Bytes * I + Tag_Bytes - 1) :=
           To_Bytes (T (I));
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              B (Tag_Bytes * J .. Tag_Bytes * J + Tag_Bytes - 1)
              = To_Bytes (T (J)));
      end loop;
   end Write_Tags;

   function Read_Tags (B : Byte_Array) return Tags is
      T  : Tags := [others => Zero];
      E  : Element;
      Ok : Boolean;
   begin
      for I in Tag_Index loop
         From_Bytes
           (B (Tag_Bytes * I .. Tag_Bytes * I + Tag_Bytes - 1), E, Ok);
         T (I) := E;
         pragma Loop_Invariant
           (for all J in 0 .. I =>
              T (J).Limbs
              = Limbs_Of_Bytes
                  (B (Tag_Bytes * J .. Tag_Bytes * J + Tag_Bytes - 1)));
      end loop;
      return T;
   end Read_Tags;

end Mdoc_Proof;
