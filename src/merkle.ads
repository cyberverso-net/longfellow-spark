--  Merkle: the Merkle tree of draft Section 4.1 over SHA-256: heap
--  construction (4.1.2), batch opening (4.1.3, the prover's, Phase C)
--  and batch proof verification (4.1.4). The nonce-blinded leaves of
--  4.1.1 are built by the Ligero verifier and the Ligero prover, which
--  hand this package leaf digests.
--
--  Documentation: docs/guide/05-ligero.md, 07-prover.md. Decisions: ADR
--  0035 (scope), 0038 (Gold perimeter), 0039 (sizes, status), 0052 (the
--  opening); frame: ADR 0003, 0020, 0029 (SHA-256 Silver plus vectors).
--  Index: docs/adr/README.md.
--
--  Layout (Section 4.1): a tree of N leaves is an array of 2 N digests,
--  the leaves at N .. 2 N - 1, node I the hash of nodes 2 I and 2 I + 1
--  for I from N - 1 down to 1, the root at 1; index 0 is unused. N need
--  not be a power of two. Hash_Pair (A, B) is SHA-256 of A || B.
--
--  Proof status (Silver = absence of run-time errors, Gold = proved
--  functional contracts).
--
--    Build        : Gold, structural: the heap is the leaves at
--                   N .. 2 N - 1 and, for 1 <= I < N, Hash_Pair of its
--                   two children.
--    Open         : Gold in Verify's model (ADR 0052): the opening
--                   holds exactly Missing_Before (0, N, Path_Flags)
--                   digests, and every child Verify reads for a node on
--                   a path, from the nodes or from the opening, is that
--                   node of the heap; so Verify recomputes the heap on
--                   the honest opening and accepts (tested).
--    Verify       : Gold on the path discipline (ADR 0038): the
--                   verification succeeds only if there is at least one
--                   index, every index is below N, no index repeats, and
--                   the proof holds exactly the digests the reconstruction
--                   consumes; and Gold on the reconstruction, through the
--                   ghost On_Path and Missing_Before: every node on a
--                   path is Hash_Pair of its two children, each child the
--                   computed node when it is on a path and otherwise the
--                   next digest of the proof, left before right, nodes
--                   from N - 1 down to 1, and the root compared is node 1.
--                   What SHA-256 does with the bytes is tested (ADR 0029).
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0037:
--  the commitment's opened columns are public data.

pragma SPARK_Mode (On);

with Bytes; use Bytes;

package Merkle is

   subtype Digest is Bytes_32;

   --  Trees of up to Max_Leaves leaves; the verifier keeps 2 N digests
   --  and 2 N Booleans for a verification (ADR 0039 states the scale).
   Max_Leaves : constant := 2**16;

   subtype Leaf_Count is Positive range 1 .. Max_Leaves;

   --  Node indices of a heap: 0 .. 2 N - 1, with 0 unused.
   subtype Node_Index is Natural range 0 .. 2 * Max_Leaves - 1;

   type Digest_Array is array (Node_Index range <>) of Digest;

   type Index_Array is array (Natural range <>) of Natural;

   --  SHA-256 of A followed by B: the node function of Section 4.1.2.
   function Hash_Pair (A, B : Digest) return Digest with
     Global => null;

   --  Section 4.1.2: the heap of the leaves. Heap (0) is left zero.
   procedure Build (Leaves : Digest_Array; Heap : out Digest_Array) with
     Global => null,
     Pre    =>
       Leaves'Length in Leaf_Count
       and then Heap'First = 0
       and then Heap'Length = 2 * Leaves'Length,
     Post   =>
       (for all I in Leaves'Length .. Heap'Last =>
          Heap (I) = Leaves (Leaves'First + (I - Leaves'Length)))
       and then
         (for all I in 1 .. Leaves'Length - 1 =>
            Heap (I) = Hash_Pair (Heap (2 * I), Heap (2 * I + 1)));

   ----------------------------------------------------------------------
   --  Section 4.1.4: batch proof verification
   ----------------------------------------------------------------------

   --  No index repeats in Indices (Indices'First .. Upto).
   function Distinct (Indices : Index_Array; Upto : Integer) return Boolean
   is
     (for all I in Indices'First .. Upto =>
        (for all J in Indices'First .. Upto =>
           (if I /= J then Indices (I) /= Indices (J))))
   with Ghost, Pre => Upto <= Indices'Last;

   --  The nodes on a path from a requested leaf to the root: the leaves
   --  N + Indices (K), and every ancestor of one of them (Section 4.1.4,
   --  is_on_path). Ghost, proof-only: it mirrors the executable marking.
   type Flag_Array is array (Node_Index range <>) of Boolean;

   function Marks_Paths
     (N : Leaf_Count; Indices : Index_Array; On_Path : Flag_Array)
      return Boolean
   is
     (On_Path'First = 0 and then On_Path'Length = 2 * N
      and then not On_Path (0)
      and then
        (for all L in N .. 2 * N - 1 =>
           On_Path (L) = (for some K in Indices'Range => N + Indices (K) = L))
      and then
        (for all I in 1 .. N - 1 =>
           On_Path (I) = (On_Path (2 * I) or On_Path (2 * I + 1))))
   with Ghost, Pre => (for all K in Indices'Range => Indices (K) < N);

   --  The flags of the paths from the requested leaves to the root
   --  (Section 4.1.4, is_on_path), as the verification computes them.
   function Path_Flags
     (N : Leaf_Count; Indices : Index_Array) return Flag_Array
   with
     Global => null,
     Pre    => (for all K in Indices'Range => Indices (K) < N),
     Post   => Marks_Paths (N, Indices, Path_Flags'Result);

   --  Digests the proof supplies for node I: one per child of I that is
   --  not on a path, when I is.
   function Missing (I : Node_Index; On_Path : Flag_Array) return Natural is
     (if On_Path (I)
      then (if On_Path (2 * I) then 0 else 1)
           + (if On_Path (2 * I + 1) then 0 else 1)
      else 0)
   with Ghost,
        Pre => On_Path'First = 0 and then I >= 1
               and then 2 * I + 1 <= On_Path'Last;

   --  Digests consumed before node I is processed: those of the nodes
   --  I + 1 .. N - 1, which the reconstruction visits first (from N - 1
   --  down to 1). Recursive, hence hidden (see Bytes.Add_Zeros).
   function Missing_Before
     (I : Node_Index; N : Leaf_Count; On_Path : Flag_Array) return Natural
   is
     (if I >= N - 1 then 0
      else Missing_Before (I + 1, N, On_Path) + Missing (I + 1, On_Path))
   with Ghost,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => On_Path'First = 0 and then On_Path'Length = 2 * N
                and then I <= N - 1,
        Post => Missing_Before'Result <= 2 * (N - 1 - I),
        Subprogram_Variant => (Increases => I);

   --  Digest K of a proof, the zero digest beyond its end: total, so
   --  that the model below needs no precondition on the proof's length;
   --  on the success path every position read lies within the proof.
   function Path_At (Path : Digest_Array; K : Natural) return Digest is
     (if K < Path'Length then Path (Path'First + K) else [others => 0])
   with Ghost;

   --  The value of child J of an on-path node I: the computed node when
   --  J is on a path, otherwise the digest of the proof at the position
   --  the discipline assigns (Section 4.1.4: left before right).
   function Child
     (I, J     : Node_Index;
      N        : Leaf_Count;
      On_Path  : Flag_Array;
      Nodes    : Digest_Array;
      Path     : Digest_Array)
      return Digest
   is
     (if On_Path (J) then Nodes (J)
      else Path_At (Path,
                    Missing_Before (I, N, On_Path)
                    + (if J = 2 * I + 1 and then not On_Path (2 * I) then 1
                       else 0)))
   with Ghost,
        Pre => On_Path'First = 0 and then On_Path'Length = 2 * N
               and then Nodes'First = 0 and then Nodes'Length = 2 * N
               and then I >= 1 and then I < N
               and then (J = 2 * I or else J = 2 * I + 1);

   --  Verification of the claim "Root is the root of an N-leaf tree with
   --  Leaves (K) at index Indices (K)", with the batch proof Path. Ok is
   --  False, with no other effect, when there is no index, an index is at
   --  or above N, an index repeats, the proof is shorter or longer than
   --  the reconstruction needs, or the reconstructed root differs.
   --  Section 4.1.3, open_merkle_heap of merkle.rs (Phase C, ADR 0052):
   --  the sibling digests the verifier needs for the leaves Indices,
   --  taken from the heap of Build, node N - 1 down to 1, one per
   --  missing child of a node on a path. Count digests are written to
   --  Path (0 .. Count - 1); the rest of Path is zero. The postcondition
   --  is Verify's model: Count is the number of digests Verify consumes
   --  (Missing_Before over Path_Flags) and every child Verify reads,
   --  from the path or from the nodes, is the heap's node, so that
   --  Verify (N, Heap (1), Indices, Heap (N + Indices), Path (0 ..
   --  Count - 1)) recomputes the heap and accepts.
   procedure Open
     (N       : Leaf_Count;
      Heap    : Digest_Array;
      Indices : Index_Array;
      Path    : out Digest_Array;
      Count   : out Natural)
   with
     Global => null,
     Pre    =>
       Heap'First = 0 and then Heap'Length = 2 * N
       and then Indices'First = 0 and then Indices'Last < N
       and then (for all K in Indices'Range => Indices (K) < N)
       and then Path'First = 0 and then Path'Length = 2 * N,
     Post   =>
       Count = Missing_Before (0, N, Path_Flags (N, Indices))
       and then Count <= 2 * (N - 1)
       and then
         (for all I in 1 .. N - 1 =>
            (if Path_Flags (N, Indices) (I) then
               Child (I, 2 * I, N, Path_Flags (N, Indices), Heap, Path)
               = Heap (2 * I)
               and then
               Child (I, 2 * I + 1, N, Path_Flags (N, Indices), Heap, Path)
               = Heap (2 * I + 1)));

   procedure Verify
     (N       : Leaf_Count;
      Root    : Digest;
      Indices : Index_Array;
      Leaves  : Digest_Array;
      Path    : Digest_Array;
      Ok      : out Boolean)
   with
     Global => null,
     Pre    =>
       Indices'First = 0 and then Leaves'First = 0
       and then Leaves'Length = Indices'Length
       and then Indices'Length <= N
       and then Path'First = 0 and then Path'Length <= 2 * N,
     Post   =>
       (if Ok then
          Indices'Length > 0
          and then (for all K in Indices'Range => Indices (K) < N)
          and then Distinct (Indices, Indices'Last)
          and then Path'Length
                   = Missing_Before (0, N, Path_Flags (N, Indices)));

end Merkle;
