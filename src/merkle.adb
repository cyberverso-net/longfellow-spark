pragma SPARK_Mode (On);

with Sha256;

package body Merkle is

   Zero_Digest : constant Digest := [others => 0];

   function Hash_Pair (A, B : Digest) return Digest is
      Ctx : Sha256.Context := Sha256.Initial;
   begin
      Sha256.Update (Ctx, A);
      Sha256.Update (Ctx, B);
      return Sha256.Digest (Ctx);
   end Hash_Pair;

   procedure Build (Leaves : Digest_Array; Heap : out Digest_Array) is
      N : constant Leaf_Count := Leaves'Length;
   begin
      Heap := [others => Zero_Digest];
      for I in N .. 2 * N - 1 loop
         Heap (I) := Leaves (Leaves'First + (I - N));
         pragma Loop_Invariant
           (for all J in N .. I => Heap (J) = Leaves (Leaves'First + (J - N)));
      end loop;
      for I in reverse 1 .. N - 1 loop
         Heap (I) := Hash_Pair (Heap (2 * I), Heap (2 * I + 1));
         pragma Loop_Invariant
           (for all J in N .. 2 * N - 1 =>
              Heap (J) = Leaves (Leaves'First + (J - N)));
         pragma Loop_Invariant
           (for all J in I .. N - 1 =>
              Heap (J) = Hash_Pair (Heap (2 * J), Heap (2 * J + 1)));
      end loop;
   end Build;

   ----------------------------------------------------------------------
   --  Lemmas on Missing_Before, from its hidden definition
   ----------------------------------------------------------------------

   --  Nothing is consumed before the first node visited.
   procedure Lemma_Missing_Top
     (I : Node_Index; N : Leaf_Count; On_Path : Flag_Array)
   with
     Ghost,
     Global => null,
     Pre    => On_Path'First = 0 and then On_Path'Length = 2 * N
               and then I = N - 1,
     Post   => Missing_Before (I, N, On_Path) = 0
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Missing_Before);
   begin
      null;
   end Lemma_Missing_Top;

   --  One node down: what node I consumes adds to the count.
   procedure Lemma_Missing_Step
     (I : Node_Index; N : Leaf_Count; On_Path : Flag_Array)
   with
     Ghost,
     Global => null,
     Pre    => On_Path'First = 0 and then On_Path'Length = 2 * N
               and then I >= 1 and then I <= N - 1,
     Post   => Missing_Before (I - 1, N, On_Path)
               = Missing_Before (I, N, On_Path) + Missing (I, On_Path)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Missing_Before);
   begin
      null;
   end Lemma_Missing_Step;

   ----------------------------------------------------------------------
   --  Verification
   ----------------------------------------------------------------------

   function Path_Flags
     (N : Leaf_Count; Indices : Index_Array) return Flag_Array
   is
      Flags : Flag_Array (0 .. 2 * N - 1) := [others => False];
   begin
      for K in Indices'Range loop
         Flags (N + Indices (K)) := True;
         pragma Loop_Invariant (not Flags (0));
         pragma Loop_Invariant
           (for all L in N .. 2 * N - 1 =>
              Flags (L) = (for some K2 in Indices'First .. K =>
                             N + Indices (K2) = L));
         pragma Loop_Invariant (for all I in 1 .. N - 1 => not Flags (I));
      end loop;
      for I in reverse 1 .. N - 1 loop
         Flags (I) := Flags (2 * I) or Flags (2 * I + 1);
         pragma Loop_Invariant (not Flags (0));
         pragma Loop_Invariant
           (for all L in N .. 2 * N - 1 =>
              Flags (L) = (for some K in Indices'Range =>
                             N + Indices (K) = L));
         pragma Loop_Invariant
           (for all J in I .. N - 1 =>
              Flags (J) = (Flags (2 * J) or Flags (2 * J + 1)));
      end loop;
      return Flags;
   end Path_Flags;

   ----------------------------------------------------------------------
   --  Open (4.1.3)
   ----------------------------------------------------------------------

   --  Missing_Before decreases with its first argument.
   procedure Lemma_Missing_Mono
     (I, J : Node_Index; N : Leaf_Count; On_Path : Flag_Array)
   with
     Ghost,
     Global => null,
     Pre    => On_Path'First = 0 and then On_Path'Length = 2 * N
               and then I <= J and then J <= N - 1,
     Post   => Missing_Before (J, N, On_Path)
               <= Missing_Before (I, N, On_Path),
     Subprogram_Variant => (Decreases => J)
   is
   begin
      if J > I then
         Lemma_Missing_Step (J, N, On_Path);
         Lemma_Missing_Mono (I, J - 1, N, On_Path);
      end if;
   end Lemma_Missing_Mono;

   --  The path positions node J reads (Missing_Before (J) and the one
   --  after) lie below Missing_Before (I) for every J above I.
   procedure Lemma_Reads_Below
     (I : Node_Index; N : Leaf_Count; On_Path : Flag_Array)
   with
     Ghost,
     Global => null,
     Pre    => On_Path'First = 0 and then On_Path'Length = 2 * N
               and then I <= N - 1,
     Post   =>
       (for all J in I + 1 .. N - 1 =>
          Missing_Before (J, N, On_Path) + Missing (J, On_Path)
          <= Missing_Before (I, N, On_Path))
   is
   begin
      for J in I + 1 .. N - 1 loop
         Lemma_Missing_Step (J, N, On_Path);
         Lemma_Missing_Mono (I, J - 1, N, On_Path);
         pragma Loop_Invariant
           (for all J2 in I + 1 .. J =>
              Missing_Before (J2, N, On_Path) + Missing (J2, On_Path)
              <= Missing_Before (I, N, On_Path));
      end loop;
   end Lemma_Reads_Below;

   procedure Open
     (N       : Leaf_Count;
      Heap    : Digest_Array;
      Indices : Index_Array;
      Path    : out Digest_Array;
      Count   : out Natural)
   is
      On_Path : constant Flag_Array := Path_Flags (N, Indices);
   begin
      Path  := [others => Zero_Digest];
      Count := 0;
      Lemma_Missing_Top (N - 1, N, On_Path);
      for I in reverse 1 .. N - 1 loop
         pragma Loop_Invariant (Count = Missing_Before (I, N, On_Path));
         pragma Loop_Invariant (Count <= 2 * (N - 1 - I));
         pragma Loop_Invariant
           (for all J in I + 1 .. N - 1 =>
              (if On_Path (J) then
                 Child (J, 2 * J, N, On_Path, Heap, Path) = Heap (2 * J)
                 and then Child (J, 2 * J + 1, N, On_Path, Heap, Path)
                          = Heap (2 * J + 1)));
         Lemma_Reads_Below (I, N, On_Path);
         if On_Path (I) then
            if not On_Path (2 * I) then
               Path (Count) := Heap (2 * I);
               Count := Count + 1;
            end if;
            if not On_Path (2 * I + 1) then
               Path (Count) := Heap (2 * I + 1);
               Count := Count + 1;
            end if;
         end if;
         Lemma_Missing_Step (I, N, On_Path);
      end loop;
   end Open;

   ----------------------------------------------------------------------
   --  Verify (4.1.4)
   ----------------------------------------------------------------------

   procedure Verify
     (N       : Leaf_Count;
      Root    : Digest;
      Indices : Index_Array;
      Leaves  : Digest_Array;
      Path    : Digest_Array;
      Ok      : out Boolean)
   is
      Seen     : Flag_Array (0 .. N - 1) := [others => False];
      Nodes    : Digest_Array (0 .. 2 * N - 1) := [others => Zero_Digest];
      Consumed : Natural := 0;
      Left     : Digest;
      Right    : Digest;
   begin
      Ok := False;
      if Indices'Length = 0 then
         return;
      end if;
      --  Every index below N and none twice.
      for K in Indices'Range loop
         if Indices (K) >= N or else Seen (Indices (K)) then
            return;
         end if;
         Seen (Indices (K)) := True;
         pragma Loop_Invariant
           (for all K2 in Indices'First .. K => Indices (K2) < N);
         pragma Loop_Invariant
           (for all L in 0 .. N - 1 =>
              Seen (L) = (for some K2 in Indices'First .. K =>
                            Indices (K2) = L));
         pragma Loop_Invariant (Distinct (Indices, K));
      end loop;
      declare
         On_Path : constant Flag_Array := Path_Flags (N, Indices);
      begin
         for K in Indices'Range loop
            Nodes (N + Indices (K)) := Leaves (K);
         end loop;
         --  From N - 1 down to 1: a node on a path is the hash of its
         --  children, a child not on a path taken from the proof.
         Lemma_Missing_Top (N - 1, N, On_Path);
         for I in reverse 1 .. N - 1 loop
            pragma Loop_Invariant (Consumed = Missing_Before (I, N, On_Path));
            pragma Loop_Invariant (Consumed <= Path'Length);
            pragma Loop_Invariant
              (for all J in I + 1 .. N - 1 =>
                 (if On_Path (J) then
                    Nodes (J) = Hash_Pair
                      (Child (J, 2 * J, N, On_Path, Nodes, Path),
                       Child (J, 2 * J + 1, N, On_Path, Nodes, Path))));
            if On_Path (I) then
               if On_Path (2 * I) then
                  Left := Nodes (2 * I);
               else
                  if Consumed >= Path'Length then
                     return;
                  end if;
                  Left := Path (Consumed);
                  Consumed := Consumed + 1;
               end if;
               if On_Path (2 * I + 1) then
                  Right := Nodes (2 * I + 1);
               else
                  if Consumed >= Path'Length then
                     return;
                  end if;
                  Right := Path (Consumed);
                  Consumed := Consumed + 1;
               end if;
               Nodes (I) := Hash_Pair (Left, Right);
            end if;
            Lemma_Missing_Step (I, N, On_Path);
         end loop;
         --  The root compared is node 1 of the reconstruction, and the
         --  proof must have been consumed exactly.
         Ok := Consumed = Path'Length and then Nodes (1) = Root;
      end;
   end Verify;

end Merkle;
