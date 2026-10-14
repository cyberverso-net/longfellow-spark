pragma SPARK_Mode (On);

package body Bytes is

   function Append (S : Byte_Seq; D : Byte_Array) return Byte_Seq is
      R : Byte_Seq := S;
   begin
      for I in D'Range loop
         R := Byte_Seqs.Add (R, D (I));
         pragma Loop_Invariant
           (Byte_Seqs.Length (R)
            = Byte_Seqs.Length (S) + To_Big_Integer (I - D'First + 1));
         pragma Loop_Invariant (Byte_Seqs.Equal_Prefix (S, R));
         pragma Loop_Invariant
           (for all J in D'First .. I =>
              Byte_Seqs.Get
                (R, Byte_Seqs.Length (S) + To_Big_Integer (J - D'First + 1))
              = D (J));
      end loop;
      return R;
   end Append;

end Bytes;
