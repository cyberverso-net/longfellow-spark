--  Sumcheck_HQuad: the bound quad of a layer by the merged terms of
--  upstream (rust/runtime/sumcheck/src/hquad.rs at d5e6be7: bind_g,
--  bind_h, scalar), shared by the prover and the verifier (ADR 0073).
--  The kernels bind g with the eq2 table, merge the consecutive terms
--  with the same hands, then bind one hand at a time; the coefficient
--  left at hands (0, 0) after the last round is the bound quad.
--
--  The ghost package BQ holds the invariant of the rounds of ADR 0071:
--  for every pair of hands, the sum of the coefficients of the merged
--  terms equals the sum over the terms of the layer of Bound_KT times
--  the factors of the challenges drawn so far. Merge_Terms gives it at
--  round 0, each Bind_H carries it to the next hand, and at the end it
--  gives EBQT_Ref. The prover keeps it round by round in its sumcheck;
--  Bind_Quad, the verifier's form, runs the same rounds on its own.
--
--  Generic over Sumcheck_Algebra; the sums of the proof are taken with
--  its wrappers, so that the contracts of the field stay out of them.
--  Public data only; no constant-time requirement.

pragma SPARK_Mode (On);

with Interfaces;
with Proof_Levels;
with Sumcheck_Algebra;

generic
   with package SA is new Sumcheck_Algebra (<>);
package Sumcheck_HQuad is

   subtype Element is SA.Element;
   subtype Element_Array is SA.Element_Array;
   subtype Term is SA.Term;
   subtype Term_Array is SA.Term_Array;

   use SA.F;
   use type SA.Term;

   Zero : Element renames SA.Zero;
   One  : Element renames SA.One;

   subtype Hand is Natural range 0 .. 1;

   --  vector_ref: entry I of the first N, zero beyond.
   function Ref (A : Element_Array; N, I : Natural) return Element is
     (if I < N then A (I) else Zero)
   with Global => null, Pre => A'First = 0 and then N <= A'Length;

   --  The index of hand H of a term.
   function Hand_Index (T : Term; H : Hand) return Natural is
     (if H = 0 then T.H0 else T.H1)
   with Global => null;

   -------------------------------------------------------------------
   --  The merged terms (Phase D, M1; ADR 0063), as the production
   --  prover keeps them (rust/runtime/sumcheck/src/hquad.rs, bind_g and
   --  bind_h): g bound with the eq2 table, the consecutive terms with
   --  the same hands merged into one, then at each round the two
   --  corners (2 i, 2 i + 1) of the bound hand merged by affine
   --  interpolation, so that the terms shrink with the rounds. The
   --  coefficient of every corner is linear in the terms, so the round
   --  polynomial is the one of the reference terms, which Update_Terms
   --  of Sumcheck_Prover keeps one by one: tested.
   -------------------------------------------------------------------

   --  The coefficients bound with the eq2 table E (Eq2_Table): beta
   --  times E (g) for a Z term, k times E (g) otherwise, zero beyond
   --  the table, as Bound_KT reads it; g set to 0.
   procedure Bind_G_T (T : in out Term_Array; E : Element_Array;
                       Beta : Element)
   with
     Global => null,
     Pre    => E'First = 0,
     Post   =>
       (for all I in T'Range =>
          Same (T (I).K,
                (if T'Old (I).K = Zero
                 then Beta * Ref (E, E'Length, T'Old (I).G)
                 else T'Old (I).K * Ref (E, E'Length, T'Old (I).G)))
          and then T (I).G = 0
          and then T (I).H0 = T'Old (I).H0
          and then T (I).H1 = T'Old (I).H1);

   function Same_Hands (A, B : Term) return Boolean is
     (A.H0 = B.H0 and then A.H1 = B.H1)
   with Global => null;

   --  The run of the term at offset I: 0 for the first, one more at
   --  each change of hands.
   function Run_Id (T : Term_Array; I : Natural) return Natural is
     (if I = 0 then 0
      elsif Same_Hands (T (T'First + I - 1), T (T'First + I))
      then Run_Id (T, I - 1)
      else Run_Id (T, I - 1) + 1)
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre  => I < T'Length,
        Post => Run_Id'Result <= I,
        Subprogram_Variant => (Decreases => I);

   --  The coefficient of run X after the first N terms: the sum of
   --  their coefficients, from zero, in their order.
   function Run_Sum (T : Term_Array; X : Natural; N : Natural)
      return Element
   is
     (if N = 0 then Zero
      elsif Run_Id (T, N - 1) = X
      then Run_Sum (T, X, N - 1) + T (T'First + N - 1).K
      else Run_Sum (T, X, N - 1))
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Pre => N <= T'Length,
        Subprogram_Variant => (Decreases => N);

   --  The runs of T merged in place: the first N terms are the runs,
   --  each with the hands of its terms and the sum of their
   --  coefficients.
   procedure Merge_Runs (T : in out Term_Array; N : out Natural)
   with
     Global => null,
     Post   =>
       (Runtime    => N <= T'Length,
        Proof_Only =>
          N = (if T'Length = 0 then 0
               else Run_Id (T'Old, T'Length - 1) + 1)
          and then
          (for all X in 0 .. N - 1 =>
             Same (T (T'First + X).K, Run_Sum (T'Old, X, T'Length)))
          and then
          (for all I in 0 .. T'Length - 1 =>
             Same_Hands (T (T'First + Run_Id (T'Old, I)),
                         T'Old (T'First + I))));

   --  Two corners at offset P for hand H: the next term has the same
   --  other hand and the next index of the same pair.
   function Two (T : Term_Array; P : Natural; H : Hand) return Boolean is
     (P + 1 < T'Length
      and then Hand_Index (T (T'First + P), 1 - H)
               = Hand_Index (T (T'First + P + 1), 1 - H)
      and then Hand_Index (T (T'First + P), H) / 2
               = Hand_Index (T (T'First + P + 1), H) / 2
      and then Hand_Index (T (T'First + P + 1), H)
               = Hand_Index (T (T'First + P), H) + 1)
   with Global => null,
        Pre => P < T'Length;

   --  The offset of the input read for output K: one corner or two.
   function Rd (T : Term_Array; H : Hand; K : Natural) return Natural is
     (if K = 0 then 0
      elsif Rd (T, H, K - 1) >= T'Length then Rd (T, H, K - 1)
      elsif Two (T, Rd (T, H, K - 1), H) then Rd (T, H, K - 1) + 2
      else Rd (T, H, K - 1) + 1)
   with Ghost => Proof_Only,
        Global => null,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
        Post => Rd'Result <= T'Length,
        Subprogram_Variant => (Decreases => K);

   --  The coefficient of the corner read at P, bound at R:
   --  affine_interpolation for two corners, nz_z for an even one
   --  alone, z_nz for an odd one alone.
   function Corner_K (T : Term_Array; P : Natural; H : Hand; R : Element)
      return Element
   is
     (if Two (T, P, H)
      then T (T'First + P).K
           + (T (T'First + P + 1).K - T (T'First + P).K) * R
      elsif Hand_Index (T (T'First + P), H) mod 2 = 0
      then T (T'First + P).K - T (T'First + P).K * R
      else T (T'First + P).K * R)
   with Global => null,
        Pre => P < T'Length;

   --  bind_h: the corners of hand H merged in place at R; the first N
   --  terms are the merged ones, the bound hand halved.
   procedure Bind_H (T : in out Term_Array; H : Hand; R : Element;
                     N : out Natural)
   with
     Global => null,
     Post   =>
       (Runtime    => N <= T'Length,
        Proof_Only =>
          Rd (T'Old, H, N) = T'Length
          and then
          (for all K in 0 .. N - 1 =>
             Rd (T'Old, H, K) < T'Length
             and then
             Same (T (T'First + K).K,
                   Corner_K (T'Old, Rd (T'Old, H, K), H, R))
             and then
             Hand_Index (T (T'First + K), H)
             = Hand_Index (T'Old (T'First + Rd (T'Old, H, K)), H) / 2
             and then
             Hand_Index (T (T'First + K), 1 - H)
             = Hand_Index (T'Old (T'First + Rd (T'Old, H, K)), 1 - H)));

   -------------------------------------------------------------------
   --  The bound quad of a layer (ADR 0071). The coefficients of the
   --  terms, summed by hands, are kept round by round: Bind_G_T and
   --  Merge_Runs give the sums of Bound_KT, each Bind_H turns the low
   --  bit of a hand into the factor of its challenge. After the last
   --  round the sum at hands (0, 0) is EBQT_Ref.
   -------------------------------------------------------------------

   --  The sums are taken with the wrappers of Sumcheck_Algebra, so that
   --  the contracts of the field stay out of these proofs.
   package BQ with Ghost => Proof_Only is

      function "+" (A, B : Element) return Element renames SA."+";
      function "-" (A, B : Element) return Element renames SA."-";
      function "*" (A, B : Element) return Element renames SA."*";

      subtype U64 is Interfaces.Unsigned_64;
      use type U64;
      function Shl (V : U64; N : Natural) return U64
        renames Interfaces.Shift_Left;

      --  The factor of challenge C for the low bit of X.
      function Fac (X : Natural; C : Element) return Element is
        (if X mod 2 = 0 then One - C else C)
      with Ghost => Proof_Only, Global => null;

      --  X without its K low bits.
      function Shr (X : Natural; K : Natural) return Natural is
        (if K = 0 then X else Shr (X, K - 1) / 2)
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Post => Shr'Result <= X,
           Subprogram_Variant => (Decreases => K);

      --  The factors of C (0 .. R - 1) for the low R bits of X, the low
      --  bit with C (0) first, as Bindeq_Ref reads them.
      function Pre_F (C : Element_Array; R : Natural; X : Natural)
         return Element
      is
        (if R = 0 then One
         else Pre_F (C, R - 1, X) * Fac (Shr (X, R - 1), C (R - 1)))
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Pre => C'First = 0 and then R <= C'Length,
           Subprogram_Variant => (Decreases => R);

      --  The sum of the coefficients of the first N terms whose hand H is
      --  A and whose other hand is B.
      function W_Sum (T : Term_Array; N : Natural; H : Hand; A, B : Natural)
         return Element
      is
        (if N = 0 then Zero
         elsif Hand_Index (T (T'First + N - 1), H) = A
           and then Hand_Index (T (T'First + N - 1), 1 - H) = B
         then W_Sum (T, N - 1, H, A, B) + T (T'First + N - 1).K
         else W_Sum (T, N - 1, H, A, B))
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Pre => N <= T'Length,
           Subprogram_Variant => (Decreases => N);

      --  The sum, over the first N terms whose hands without their R0 and
      --  R1 low bits are A and B, of the coefficient times the factors of
      --  the challenges C0 (0 .. R0 - 1) and C1 (0 .. R1 - 1).
      function V_Sum
        (T  : Term_Array;
         N  : Natural;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural) return Element
      is
        (if N = 0 then Zero
         elsif Shr (T (T'First + N - 1).H0, R0) = A
           and then Shr (T (T'First + N - 1).H1, R1) = B
         then V_Sum (T, N - 1, C0, R0, C1, R1, A, B)
              + (T (T'First + N - 1).K
                 * Pre_F (C0, R0, T (T'First + N - 1).H0))
                * Pre_F (C1, R1, T (T'First + N - 1).H1)
         else V_Sum (T, N - 1, C0, R0, C1, R1, A, B))
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Pre => N <= T'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length,
           Subprogram_Variant => (Decreases => N);

      --  The coefficient of the corner read at P, bound at R, in the
      --  form of the wrappers: Corner_K, with the affine interpolation
      --  written (1 - R) k0 + R k1.
      function Corner_W (T : Term_Array; P : Natural; H : Hand; R : Element)
         return Element
      is
        (if Two (T, P, H)
         then (One - R) * T (T'First + P).K + R * T (T'First + P + 1).K
         elsif Hand_Index (T (T'First + P), H) mod 2 = 0
         then (One - R) * T (T'First + P).K
         else R * T (T'First + P).K)
      with Ghost => Proof_Only, Global => null,
           Pre => P < T'Length;

      --  Run_Sum with the wrapper addition.
      function Run_Sum_W (T : Term_Array; X : Natural; N : Natural)
         return Element
      is
        (if N = 0 then Zero
         elsif Run_Id (T, N - 1) = X
         then Run_Sum_W (T, X, N - 1) + T (T'First + N - 1).K
         else Run_Sum_W (T, X, N - 1))
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Pre => N <= T'Length,
           Subprogram_Variant => (Decreases => N);

      procedure Lemma_Corner_To_W
        (T : Term_Array; P : Natural; H : Hand; R : Element)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => P < T'Length,
        Post   => Same (Corner_K (T, P, H, R), Corner_W (T, P, H, R));

      --  The postcondition of Bind_H, its corners in the wrapper form.
      procedure Lemma_Corners_W
        (Old, New_T : Term_Array;
         H          : Hand;
         R          : Element;
         NB         : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    =>
          New_T'First = Old'First and then New_T'Length = Old'Length
          and then NB <= New_T'Length
          and then
          (for all K in 0 .. NB - 1 =>
             Rd (Old, H, K) < Old'Length
             and then
             Same (New_T (New_T'First + K).K,
                   Corner_K (Old, Rd (Old, H, K), H, R))),
        Post   =>
          (for all K in 0 .. NB - 1 =>
             Same (New_T (New_T'First + K).K,
                   Corner_W (Old, Rd (Old, H, K), H, R)));

      procedure Lemma_Run_Sum_W (T : Term_Array; X : Natural; N : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length,
        Post   => Same (Run_Sum (T, X, N), Run_Sum_W (T, X, N)),
        Subprogram_Variant => (Decreases => N);

      --  The postcondition of Merge_Runs, its sums in the wrapper form.
      procedure Lemma_Run_Sums_W (Tm, T1 : Term_Array; NT : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    =>
          NT <= Tm'Length
          and then
          (for all X in 0 .. NT - 1 =>
             Same (Tm (Tm'First + X).K, Run_Sum (T1, X, T1'Length))),
        Post   =>
          (for all X in 0 .. NT - 1 =>
             Same (Tm (Tm'First + X).K, Run_Sum_W (T1, X, T1'Length)));

      procedure Lemma_Run_Sum_W_Step (T : Term_Array; N : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N >= 1 and then N <= T'Length,
        Post   =>
          (for all X in Natural =>
             Same (Run_Sum_W (T, X, N),
                   (if Run_Id (T, N - 1) = X
                    then Run_Sum_W (T, X, N - 1) + T (T'First + N - 1).K
                    else Run_Sum_W (T, X, N - 1))));

      --  A run not reached yet has the coefficient zero.
      procedure Lemma_Run_Sum_W_Zero (T : Term_Array; X : Natural; N : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length
                  and then (N = 0 or else X > Run_Id (T, N - 1)),
        Post   => Same (Run_Sum_W (T, X, N), Zero),
        Subprogram_Variant => (Decreases => N);

      procedure Lemma_Shr_Step (X : Natural; K : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => K < Natural'Last,
        Post   => Shr (X, 0) = X and then Shr (X, K + 1) = Shr (X, K) / 2;

      procedure Lemma_Pre_Step (C : Element_Array; R : Natural; X : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => C'First = 0 and then R < C'Length,
        Post   => Same (Pre_F (C, 0, X), One)
                  and then Same (Pre_F (C, R + 1, X),
                                 Pre_F (C, R, X) * Fac (Shr (X, R), C (R)));

      procedure Lemma_Pre_Zero (C : Element_Array; X : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => C'First = 0,
        Post   => Same (Pre_F (C, 0, X), One);

      --  The hand H = 1 sums are the hand 0 sums with A and B swapped.
      procedure Lemma_W_Swap (T : Term_Array; N : Natural; A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length,
        Post   => Same (W_Sum (T, N, 1, A, B), W_Sum (T, N, 0, B, A)),
        Subprogram_Variant => (Decreases => N);

      --  A sum at a hand index no wire reaches is zero.
      procedure Lemma_W_Out (T : Term_Array; N : Natural; H : Hand;
                             A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length and then A >= SA.Max_Wires,
        Post   => Same (W_Sum (T, N, H, A, B), Zero),
        Subprogram_Variant => (Decreases => N);

      procedure Lemma_V_Out
        (T  : Term_Array;
         N  : Natural;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length
                  and then (A >= SA.Max_Wires or else B >= SA.Max_Wires),
        Post   => Same (V_Sum (T, N, C0, R0, C1, R1, A, B), Zero),
        Subprogram_Variant => (Decreases => N);

      --  One step of Lemma_Bind_H_Sum: the merged term K - 1 and the one
      --  or two corners it reads.
      procedure Lemma_Bind_H_Step
        (T0, T : Term_Array;
         H     : Hand;
         R     : Element;
         K     : Natural;
         A, B  : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    =>
          T'First = T0'First and then T'Length = T0'Length
          and then K >= 1 and then K <= T'Length
          and then A < SA.Max_Wires
          and then Rd (T0, H, K - 1) < T0'Length
          and then
          Same (T (T'First + K - 1).K, Corner_W (T0, Rd (T0, H, K - 1), H, R))
          and then
          Hand_Index (T (T'First + K - 1), H)
          = Hand_Index (T0 (T0'First + Rd (T0, H, K - 1)), H) / 2
          and then
          Hand_Index (T (T'First + K - 1), 1 - H)
          = Hand_Index (T0 (T0'First + Rd (T0, H, K - 1)), 1 - H)
          and then
          Same (W_Sum (T, K - 1, H, A, B),
                (One - R) * W_Sum (T0, Rd (T0, H, K - 1), H, 2 * A, B)
                + R * W_Sum (T0, Rd (T0, H, K - 1), H, 2 * A + 1, B)),
        Post   =>
          Same (W_Sum (T, K, H, A, B),
                (One - R) * W_Sum (T0, Rd (T0, H, K), H, 2 * A, B)
                + R * W_Sum (T0, Rd (T0, H, K), H, 2 * A + 1, B));

      --  One Bind_H of hand H at R, read off its postcondition: the sums
      --  of the first K merged terms are the sums of the corners they
      --  read, split by the parity of hand H.
      procedure Lemma_Bind_H_Sum
        (T0, T : Term_Array;
         H     : Hand;
         R     : Element;
         N, K  : Natural;
         A, B  : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    =>
          T'First = T0'First and then T'Length = T0'Length
          and then K <= N and then N <= T'Length
          and then A < SA.Max_Wires
          and then Rd (T0, H, N) = T0'Length
          and then
          (for all J in 0 .. N - 1 =>
             Rd (T0, H, J) < T0'Length
             and then
             Same (T (T'First + J).K, Corner_W (T0, Rd (T0, H, J), H, R))
             and then
             Hand_Index (T (T'First + J), H)
             = Hand_Index (T0 (T0'First + Rd (T0, H, J)), H) / 2
             and then
             Hand_Index (T (T'First + J), 1 - H)
             = Hand_Index (T0 (T0'First + Rd (T0, H, J)), 1 - H)),
        Post   =>
          Same (W_Sum (T, K, H, A, B),
                (One - R) * W_Sum (T0, Rd (T0, H, K), H, 2 * A, B)
                + R * W_Sum (T0, Rd (T0, H, K), H, 2 * A + 1, B)),
        Subprogram_Variant => (Decreases => K);

      --  Binding hand 0 at C0 (R0) splits the sums by the parity of the
      --  hand without its R0 low bits.
      procedure Lemma_V_Step0
        (T  : Term_Array;
         N  : Natural;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length
                  and then C0'First = 0 and then R0 < C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length
                  and then A < SA.Max_Wires,
        Post   =>
          Same (V_Sum (T, N, C0, R0 + 1, C1, R1, A, B),
                (One - C0 (R0)) * V_Sum (T, N, C0, R0, C1, R1, 2 * A, B)
                + C0 (R0) * V_Sum (T, N, C0, R0, C1, R1, 2 * A + 1, B)),
        Subprogram_Variant => (Decreases => N);

      procedure Lemma_V_Step1
        (T  : Term_Array;
         N  : Natural;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 < C1'Length
                  and then B < SA.Max_Wires,
        Post   =>
          Same (V_Sum (T, N, C0, R0, C1, R1 + 1, A, B),
                (One - C1 (R1)) * V_Sum (T, N, C0, R0, C1, R1, A, 2 * B)
                + C1 (R1) * V_Sum (T, N, C0, R0, C1, R1, A, 2 * B + 1)),
        Subprogram_Variant => (Decreases => N);

      --  Pre_F and V_Sum read only the challenges they bind.
      procedure Lemma_Pre_Frame (C, D : Element_Array; R : Natural;
                                 X : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => C'First = 0 and then D'First = 0
                  and then R <= C'Length and then R <= D'Length
                  and then (for all I in 0 .. R - 1 => Same (C (I), D (I))),
        Post   => Same (Pre_F (C, R, X), Pre_F (D, R, X)),
        Subprogram_Variant => (Decreases => R);

      procedure Lemma_V_Frame
        (T      : Term_Array;
         N      : Natural;
         C0, D0 : Element_Array;
         R0     : Natural;
         C1, D1 : Element_Array;
         R1     : Natural;
         A      : Natural;
         B      : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length
                  and then C0'First = 0 and then D0'First = 0
                  and then R0 <= C0'Length and then R0 <= D0'Length
                  and then C1'First = 0 and then D1'First = 0
                  and then R1 <= C1'Length and then R1 <= D1'Length
                  and then (for all I in 0 .. R0 - 1 => Same (C0 (I), D0 (I)))
                  and then (for all I in 0 .. R1 - 1 => Same (C1 (I), D1 (I))),
        Post   => Same (V_Sum (T, N, C0, R0, C1, R1, A, B),
                        V_Sum (T, N, D0, R0, D1, R1, A, B)),
        Subprogram_Variant => (Decreases => N);

      --  Before any round the factors are One.
      procedure Lemma_V_W0
        (T      : Term_Array;
         N      : Natural;
         C0, C1 : Element_Array;
         A, B   : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= T'Length and then C0'First = 0 and then C1'First = 0,
        Post   => Same (V_Sum (T, N, C0, 0, C1, 0, A, B), W_Sum (T, N, 0, A,
                                                                 B)),
        Subprogram_Variant => (Decreases => N);

      --  The merged terms, by hands: the sum over the first X runs whose
      --  hands in Tm are A and B of their coefficients after the first M
      --  terms of T.
      function Z_Sum (Tm, T : Term_Array; X, M : Natural; A, B : Natural)
         return Element
      is
        (if X = 0 then Zero
         elsif Tm (Tm'First + X - 1).H0 = A
           and then Tm (Tm'First + X - 1).H1 = B
         then Z_Sum (Tm, T, X - 1, M, A, B) + Run_Sum_W (T, X - 1, M)
         else Z_Sum (Tm, T, X - 1, M, A, B))
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Pre => X <= Tm'Length and then M <= T'Length,
           Subprogram_Variant => (Decreases => X);

      --  Term M changes only the run it belongs to.
      procedure Lemma_Z_Frame (Tm, T : Term_Array; X, M : Natural; A,
                               B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => X <= Tm'Length and then M < T'Length
                  and then Run_Id (T, M) >= X,
        Post   => Same (Z_Sum (Tm, T, X, M + 1, A, B), Z_Sum (Tm, T, X, M, A,
                                                              B)),
        Subprogram_Variant => (Decreases => X);

      --  One step of Lemma_Merge_Sum: term M - 1 joins its run.
      procedure Lemma_Merge_Step
        (Tm, T : Term_Array; M : Natural; A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => M >= 2 and then M <= T'Length
                  and then Run_Id (T, M - 2) < Tm'Length
                  and then Run_Id (T, M - 1) < Tm'Length
                  and then Same_Hands (Tm (Tm'First + Run_Id (T, M - 1)),
                                       T (T'First + M - 1))
                  and then
                  Same (W_Sum (T, M - 1, 0, A, B),
                        Z_Sum (Tm, T, Run_Id (T, M - 2) + 1, M - 1, A, B)),
        Post   =>
          Same (W_Sum (T, M, 0, A, B),
                Z_Sum (Tm, T, Run_Id (T, M - 1) + 1, M, A, B));

      --  The sums by hands of the first M terms are those of their runs.
      procedure Lemma_Merge_Sum (Tm, T : Term_Array; M : Natural; A,
                                 B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => T'Length >= 1 and then M <= T'Length
                  and then Tm'Length >= Run_Id (T, T'Length - 1) + 1
                  and then
                  (for all I in 0 .. T'Length - 1 =>
                     Run_Id (T, I) < Tm'Length
                     and then Same_Hands (Tm (Tm'First + Run_Id (T, I)),
                                          T (T'First + I))),
        Post   =>
          Same (W_Sum (T, M, 0, A, B),
                Z_Sum (Tm, T, (if M = 0 then 0 else Run_Id (T, M - 1) + 1), M,
                       A, B)),
        Subprogram_Variant => (Decreases => M);

      --  After Merge_Runs the sums of the runs are those of Tm.
      procedure Lemma_Z_Tm (Tm, T : Term_Array; X : Natural; A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => X <= Tm'Length
                  and then
                  (for all Y in 0 .. X - 1 =>
                     Same (Tm (Tm'First + Y).K, Run_Sum_W (T, Y, T'Length))),
        Post   => Same (Z_Sum (Tm, T, X, T'Length, A, B), W_Sum (Tm, X, 0, A,
                                                                 B)),
        Subprogram_Variant => (Decreases => X);

      --  The factors of the low L bits are those of Bindeq_Ref.
      procedure Lemma_Pre_Bindeq (C : Element_Array; L, K : Natural;
                                  X : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => C'First = 0 and then L <= C'Length
                  and then L <= SA.Max_Bindeq_Log and then K <= L,
        Post   =>
          Same (Pre_F (C, K, X) * SA.Bindeq_Ref (C (0 .. L - 1), K, Shr (X,
            K)),
                SA.Bindeq_Ref (C (0 .. L - 1), 0, X)),
        Subprogram_Variant => (Decreases => K);

      procedure Lemma_Pre_Beq (C : Element_Array; L : Natural; X : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => C'First = 0 and then L <= C'Length
                  and then L <= SA.Max_Bindeq_Log
                  and then X < SA.Table_Len (L),
        Post   => Same (Pre_F (C, L, X), SA.Beq (C, L, X));

      procedure Lemma_Table_Len_Step (L : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => L >= 1 and then L <= SA.Max_Bindeq_Log,
        Post   => SA.Table_Len (L) = 2 * SA.Table_Len (L - 1)
                  and then SA.Table_Len (0) = 1;

      --  An index below 2^L has no bit left after L shifts.
      procedure Lemma_Shr_Below (X : Natural; L, K : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => K <= L and then L <= SA.Max_Bindeq_Log
                  and then X < SA.Table_Len (L),
        Post   => Shr (X, K) < SA.Table_Len (L - K),
        Subprogram_Variant => (Decreases => K);

      --  After L rounds of both hands, the sum at hands (0, 0) is the
      --  bound quad of the layer.
      procedure Lemma_V_End
        (T1, T0 : Term_Array;
         N      : Natural;
         Logv   : Natural;
         G0, G1 : Element_Array;
         C0, C1 : Element_Array;
         L      : Natural;
         Alpha  : Element;
         Beta   : Element)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    =>
          T1'First = T0'First and then T1'Length = T0'Length
          and then N <= T0'Length
          and then G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= SA.Max_Bindeq_Log
          and then C0'First = 0 and then C1'First = 0
          and then L <= C0'Length and then L <= C1'Length
          and then L <= SA.Max_Bindeq_Log
          and then
          (for all I in T0'Range =>
             Same (T1 (I).K, SA.Bound_KT (T0 (I), Logv, G0, G1, Alpha,
                                             Beta))
             and then T1 (I).H0 = T0 (I).H0 and then T1 (I).H1 = T0 (I).H1
             and then T0 (I).H0 < SA.Table_Len (L)
             and then T0 (I).H1 < SA.Table_Len (L)),
        Post   =>
          Same (V_Sum (T1, N, C0, L, C1, L, 0, 0),
                SA.EBQT_Ref (T0, N, Logv, G0, G1, C0, C1, L, Alpha, Beta)),
        Subprogram_Variant => (Decreases => N);

      --  The invariant of the rounds: for every pair of hands, the sum
      --  of the coefficients of the first N terms of S equals the sum
      --  over the bound terms T1 with the factors of the challenges
      --  drawn so far.
      function Inv
        (S  : Term_Array;
         N  : Natural;
         T1 : Term_Array;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural) return Boolean
      is
        (for all A in 0 .. SA.Max_Wires - 1 =>
           (for all B in 0 .. SA.Max_Wires - 1 =>
              Same (W_Sum (S, N, 0, A, B),
                    V_Sum (T1, T1'Length, C0, R0, C1, R1, A, B))))
      with Ghost => Proof_Only,
           Global => null,
           Annotate => (GNATprove, Hide_Info, "Expression_Function_Body"),
           Pre => N <= S'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length;

      procedure Lemma_Inv_At
        (S  : Term_Array;
         N  : Natural;
         T1 : Term_Array;
         C0 : Element_Array;
         R0 : Natural;
         C1 : Element_Array;
         R1 : Natural;
         A  : Natural;
         B  : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N <= S'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length
                  and then A < SA.Max_Wires and then B < SA.Max_Wires
                  and then Inv (S, N, T1, C0, R0, C1, R1),
        Post   => Same (W_Sum (S, N, 0, A, B),
                        V_Sum (T1, T1'Length, C0, R0, C1, R1, A, B));

      --  W_Sum reads only the first N terms.
      procedure Lemma_W_Slice (S, U : Term_Array; N : Natural; A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => S'First = U'First and then N <= S'Length
                  and then N <= U'Length
                  and then (for all I in 0 .. N - 1 =>
                              Same (S (S'First + I).K, U (U'First + I).K)
                              and then Same_Hands (S (S'First + I),
                                                   U (U'First + I))),
        Post   => Same (W_Sum (S, N, 0, A, B), W_Sum (U, N, 0, A, B)),
        Subprogram_Variant => (Decreases => N);

      procedure Lemma_Inv_Slice
        (S, U : Term_Array;
         N    : Natural;
         T1   : Term_Array;
         C0   : Element_Array;
         R0   : Natural;
         C1   : Element_Array;
         R1   : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    => S'First = U'First and then N <= S'Length
                  and then N <= U'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length
                  and then (for all I in 0 .. N - 1 =>
                              Same (S (S'First + I).K, U (U'First + I).K)
                              and then Same_Hands (S (S'First + I),
                                                   U (U'First + I)))
                  and then Inv (S, N, T1, C0, R0, C1, R1),
        Post   => Inv (U, N, T1, C0, R0, C1, R1);

      --  After Merge_Runs, before any round.
      procedure Lemma_Inv_Base
        (Tm, T1 : Term_Array;
         NT     : Natural;
         C0, C1 : Element_Array)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    => Tm'First = T1'First and then Tm'Length = T1'Length
                  and then C0'First = 0 and then C1'First = 0
                  and then NT <= Tm'Length
                  and then NT = (if T1'Length = 0 then 0
                                 else Run_Id (T1, T1'Length - 1) + 1)
                  and then
                  (for all X in 0 .. NT - 1 =>
                     Same (Tm (Tm'First + X).K, Run_Sum_W (T1, X, T1'Length)))
                  and then
                  (for all I in 0 .. T1'Length - 1 =>
                     Same_Hands (Tm (Tm'First + Run_Id (T1, I)),
                                 T1 (T1'First + I))),
        Post   => Inv (Tm, NT, T1, C0, 0, C1, 0);

      --  A challenge drawn at R0 or beyond does not change the invariant.
      procedure Lemma_Inv_Frame
        (S      : Term_Array;
         N      : Natural;
         T1     : Term_Array;
         C0, D0 : Element_Array;
         R0     : Natural;
         C1, D1 : Element_Array;
         R1     : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    => N <= S'Length
                  and then C0'First = 0 and then D0'First = 0
                  and then R0 <= C0'Length and then R0 <= D0'Length
                  and then C1'First = 0 and then D1'First = 0
                  and then R1 <= C1'Length and then R1 <= D1'Length
                  and then (for all I in 0 .. R0 - 1 => Same (C0 (I), D0 (I)))
                  and then (for all I in 0 .. R1 - 1 => Same (C1 (I), D1 (I)))
                  and then Inv (S, N, T1, C0, R0, C1, R1),
        Post   => Inv (S, N, T1, D0, R0, D1, R1);

      --  One Bind_H of hand 0 at C0 (R0), then of hand 1 at C1 (R1).
      procedure Lemma_Inv_Step0
        (Old, New_T : Term_Array;
         NB         : Natural;
         T1         : Term_Array;
         C0         : Element_Array;
         R0         : Natural;
         C1         : Element_Array;
         R1         : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    =>
          New_T'First = Old'First and then New_T'Length = Old'Length
          and then NB <= New_T'Length
          and then C0'First = 0 and then R0 < C0'Length
          and then C1'First = 0 and then R1 <= C1'Length
          and then Rd (Old, 0, NB) = Old'Length
          and then
          (for all K in 0 .. NB - 1 =>
             Rd (Old, 0, K) < Old'Length
             and then
             Same (New_T (New_T'First + K).K,
                   Corner_W (Old, Rd (Old, 0, K), 0, C0 (R0)))
             and then
             Hand_Index (New_T (New_T'First + K), 0)
             = Hand_Index (Old (Old'First + Rd (Old, 0, K)), 0) / 2
             and then
             Hand_Index (New_T (New_T'First + K), 1)
             = Hand_Index (Old (Old'First + Rd (Old, 0, K)), 1))
          and then Inv (Old, Old'Length, T1, C0, R0, C1, R1),
        Post   => Inv (New_T, NB, T1, C0, R0 + 1, C1, R1);

      procedure Lemma_Inv_Step1
        (Old, New_T : Term_Array;
         NB         : Natural;
         T1         : Term_Array;
         C0         : Element_Array;
         R0         : Natural;
         C1         : Element_Array;
         R1         : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    =>
          New_T'First = Old'First and then New_T'Length = Old'Length
          and then NB <= New_T'Length
          and then C0'First = 0 and then R0 <= C0'Length
          and then C1'First = 0 and then R1 < C1'Length
          and then Rd (Old, 1, NB) = Old'Length
          and then
          (for all K in 0 .. NB - 1 =>
             Rd (Old, 1, K) < Old'Length
             and then
             Same (New_T (New_T'First + K).K,
                   Corner_W (Old, Rd (Old, 1, K), 1, C1 (R1)))
             and then
             Hand_Index (New_T (New_T'First + K), 1)
             = Hand_Index (Old (Old'First + Rd (Old, 1, K)), 1) / 2
             and then
             Hand_Index (New_T (New_T'First + K), 0)
             = Hand_Index (Old (Old'First + Rd (Old, 1, K)), 0))
          and then Inv (Old, Old'Length, T1, C0, R0, C1, R1),
        Post   => Inv (New_T, NB, T1, C0, R0, C1, R1 + 1);

      procedure Lemma_W_Step (T : Term_Array; N : Natural; H : Hand;
                              A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => N < T'Length,
        Post   =>
          Same (W_Sum (T, 0, H, A, B), Zero)
          and then
          Same (W_Sum (T, N + 1, H, A, B),
                (if Hand_Index (T (T'First + N), H) = A
                   and then Hand_Index (T (T'First + N), 1 - H) = B
                 then W_Sum (T, N, H, A, B) + T (T'First + N).K
                 else W_Sum (T, N, H, A, B)));

      procedure Lemma_W_Zero (T : Term_Array; H : Hand; A, B : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Post   => Same (W_Sum (T, 0, H, A, B), Zero);

      --  2^L as a word.
      procedure Lemma_TL_Shift (L : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => L <= SA.Max_Bindeq_Log,
        Post   => U64 (SA.Table_Len (L)) = Shl (1, L),
        Subprogram_Variant => (Decreases => L);

      --  The hands of a layer that fits are below 2^Logw.
      procedure Lemma_Hands_Below (T : Term_Array; NW : Natural; L : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => L <= SA.Max_Bindeq_Log
                  and then U64 (NW) <= Shl (1, L)
                  and then (for all I in T'Range =>
                              T (I).H0 < NW and then T (I).H1 < NW),
        Post   => (for all I in T'Range =>
                     T (I).H0 < SA.Table_Len (L)
                     and then T (I).H1 < SA.Table_Len (L));

      --  Bind_G_T with the eq2 table gives Bound_KT.
      procedure Lemma_T1_Bound
        (T0, T1 : Term_Array;
         E      : Element_Array;
         Logv   : Natural;
         G0, G1 : Element_Array;
         Alpha  : Element;
         Beta   : Element)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    =>
          T1'First = T0'First and then T1'Last = T0'Last
          and then G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= SA.Max_Bindeq_Log
          and then E'First = 0 and then E'Last = SA.Table_Len (Logv) - 1
          and then (for all X in E'Range =>
                      Same (E (X), SA.Beq2 (X, Logv, G0, G1, Alpha)))
          and then
          (for all I in T1'Range =>
             Same (T1 (I).K,
                   (if T0 (I).K = Zero
                    then SA.F."*" (Beta, Ref (E, E'Length, T0 (I).G))
                    else SA.F."*" (T0 (I).K, Ref (E, E'Length, T0 (I).G))))
             and then T1 (I).H0 = T0 (I).H0
             and then T1 (I).H1 = T0 (I).H1),
        Post   =>
          (for all I in T1'Range =>
             Same (T1 (I).K,
                   SA.Bound_KT (T0 (I), Logv, G0, G1, Alpha, Beta)));

      --  The terms of the layer with g bound: the coefficient Bound_KT,
      --  g zero, the same hands. The invariant of the rounds is stated on
      --  it, so that it reads only the circuit and the challenges.
      function Bound_Array
        (T0     : Term_Array;
         Logv   : Natural;
         G0, G1 : Element_Array;
         Alpha  : Element;
         Beta   : Element) return Term_Array
      is
        ([for I in T0'Range =>
            (K  => SA.Bound_KT (T0 (I), Logv, G0, G1, Alpha, Beta),
             G  => 0,
             H0 => T0 (I).H0,
             H1 => T0 (I).H1)])
      with Ghost => Proof_Only,
           Global => null,
           Pre  => G0'First = 0 and then G1'First = 0
                   and then Logv <= G0'Length and then Logv <= G1'Length
                   and then Logv <= SA.Max_Bindeq_Log,
           Post => Bound_Array'Result'First = T0'First
                   and then Bound_Array'Result'Last = T0'Last;

      --  V_Sum reads only the coefficients and the hands.
      procedure Lemma_V_Coef
        (T, U : Term_Array;
         N    : Natural;
         C0   : Element_Array;
         R0   : Natural;
         C1   : Element_Array;
         R1   : Natural;
         A    : Natural;
         B    : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => T'First = U'First and then N <= T'Length
                  and then N <= U'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length
                  and then
                  (for all I in 0 .. N - 1 =>
                     Same (T (T'First + I).K, U (U'First + I).K)
                     and then T (T'First + I).H0 = U (U'First + I).H0
                     and then T (T'First + I).H1 = U (U'First + I).H1),
        Post   => Same (V_Sum (T, N, C0, R0, C1, R1, A, B),
                        V_Sum (U, N, C0, R0, C1, R1, A, B)),
        Subprogram_Variant => (Decreases => N);

      procedure Lemma_Inv_Coef
        (S     : Term_Array;
         N     : Natural;
         T1, U : Term_Array;
         C0    : Element_Array;
         R0    : Natural;
         C1    : Element_Array;
         R1    : Natural)
      with
        Ghost  => Proof_Only,
        Always_Terminates,
        Global => null,
        Pre    => T1'First = U'First and then T1'Length = U'Length
                  and then N <= S'Length
                  and then C0'First = 0 and then R0 <= C0'Length
                  and then C1'First = 0 and then R1 <= C1'Length
                  and then
                  (for all I in 0 .. T1'Length - 1 =>
                     Same (T1 (T1'First + I).K, U (U'First + I).K)
                     and then T1 (T1'First + I).H0 = U (U'First + I).H0
                     and then T1 (T1'First + I).H1 = U (U'First + I).H1)
                  and then Inv (S, N, T1, C0, R0, C1, R1),
        Post   => Inv (S, N, U, C0, R0, C1, R1);

      --  An index at or above 2^L keeps a bit after L shifts.
      procedure Lemma_Shr_Above (X : Natural; L, K : Natural)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    => K <= L and then L <= SA.Max_Bindeq_Log
                  and then X >= SA.Table_Len (L),
        Post   => Shr (X, K) >= SA.Table_Len (L - K),
        Subprogram_Variant => (Decreases => K);

      --  Lemma_V_End for any hands: a term with a hand at or above 2^L
      --  is left out of the sum at (0, 0) and has the factor Zero in
      --  EBQT_Ref (ADR 0073).
      procedure Lemma_V_End_All
        (T1, T0 : Term_Array;
         N      : Natural;
         Logv   : Natural;
         G0, G1 : Element_Array;
         C0, C1 : Element_Array;
         L      : Natural;
         Alpha  : Element;
         Beta   : Element)
      with
        Ghost  => Proof_Only,
        Global => null,
        Pre    =>
          T1'First = T0'First and then T1'Length = T0'Length
          and then N <= T0'Length
          and then G0'First = 0 and then G1'First = 0
          and then Logv <= G0'Length and then Logv <= G1'Length
          and then Logv <= SA.Max_Bindeq_Log
          and then C0'First = 0 and then C1'First = 0
          and then L <= C0'Length and then L <= C1'Length
          and then L <= SA.Max_Bindeq_Log
          and then
          (for all I in T0'Range =>
             Same (T1 (I).K, SA.Bound_KT (T0 (I), Logv, G0, G1, Alpha,
                                          Beta))
             and then T1 (I).H0 = T0 (I).H0 and then T1 (I).H1 = T0 (I).H1),
        Post   =>
          Same (V_Sum (T1, N, C0, L, C1, L, 0, 0),
                SA.EBQT_Ref (T0, N, Logv, G0, G1, C0, C1, L, Alpha, Beta)),
        Subprogram_Variant => (Decreases => N);

   end BQ;

   --  Merge_Runs, with the invariant of the rounds at round 0 when the
   --  tables are in use (ADR 0071). T0 is the layer of the circuit.
   procedure Merge_Terms
     (T      : in out Term_Array;
      NT     : out Natural;
      Tab    : Boolean;
      T0     : Term_Array;
      Logv   : Natural;
      G0, G1 : Element_Array;
      Alpha  : Element;
      Beta   : Element;
      C0, C1 : Element_Array)
   with
     Global => null,
     Pre    =>
       (Proof_Only =>
          (if Tab then
             G0'First = 0 and then G1'First = 0
             and then Logv <= G0'Length and then Logv <= G1'Length
             and then Logv <= SA.Max_Bindeq_Log
             and then C0'First = 0 and then C1'First = 0
             and then T'First = T0'First and then T'Last = T0'Last
             and then
             (for all I in T'Range =>
                Same (T (I).K,
                      SA.Bound_KT (T0 (I), Logv, G0, G1, Alpha, Beta))
                and then T (I).H0 = T0 (I).H0
                and then T (I).H1 = T0 (I).H1))),
     Post   =>
       (Runtime    => NT <= T'Length,
        Proof_Only =>
          (if Tab then BQ.Inv (T, NT, BQ.Bound_Array (T0, Logv, G0, G1, Alpha,
                                                      Beta), C0, 0, C1, 0)));

   -------------------------------------------------------------------
   --  bind_quad of the verifier (ADR 0073), as upstream's
   --  symbolic_sumcheck_verifier.rs: the bound quad of a layer by the
   --  kernels above, with the same proof as the prover's.
   -------------------------------------------------------------------

   --  The terms of the layer bound with g by the eq2 table and merged,
   --  then Logw rounds of both hands bound at HC0 (R) and HC1 (R); the
   --  bound quad is the coefficient left at hands (0, 0). The terms are
   --  copied on the heap, the copy and the table freed before return.
   procedure Bind_Quad
     (T           : Term_Array;
      Logv        : Natural;
      G0, G1      : Element_Array;
      HC0, HC1    : Element_Array;
      Logw        : Natural;
      Alpha, Beta : Element;
      V           : out Element)
   with
     Global => null,
     Pre  => G0'First = 0 and then G1'First = 0
       and then Logv <= G0'Length and then Logv <= G1'Length
       and then Logv <= SA.Max_Bindeq_Log
       and then HC0'First = 0 and then HC1'First = 0
       and then Logw <= HC0'Length and then Logw <= HC1'Length
       and then Logw <= SA.Max_Bindeq_Log,
     Post => (Proof_Only =>
                Same (V,
                      SA.EBQT_Ref (T, T'Length, Logv, G0, G1, HC0, HC1,
                                   Logw, Alpha, Beta)));

end Sumcheck_HQuad;
