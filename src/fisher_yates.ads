--  Fisher_Yates: the shuffle behind the choose method of draft Section
--  3.4.2, as a pure function of the draws. Transcript.Choose draws the
--  k values nat (n - i) and hands them here; keeping the array
--  manipulation in a unit of its own gives its proof a light context
--  (in Transcript, with the sequence model in scope, the same
--  invariants ran out of steps).
--
--  Documentation: docs/guide/04-transcript.md. Decisions: ADR 0028,
--  ADR 0031 (Gold: k distinct indices below n, by the permutation
--  invariant of the array); frame: ADR 0002, 0003, 0020. Index:
--  docs/adr/README.md.
--
--  Proof status. Choose : Gold, the results are distinct and below n,
--  for every input satisfying the precondition, through a ghost
--  inverse of the array (a linear invariant, see the body). Silver
--  everywhere.
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0029
--  (public data: the transcript's draws).

pragma SPARK_Mode (On);

package Fisher_Yates is

   Max_N : constant := 2**16;

   type Index_Array is array (Natural range <>) of Natural;

   --  The draws v (0 .. Last) are each below n - i, as nat (n - i)
   --  returns them. A ghost predicate with a hidden body rather than a
   --  quantifier in the caller's invariant: Transcript proves its draw
   --  loop through Record_Draw and this name only, and the quantifier
   --  stays out of its context.
   function Draws_Below
     (V : Index_Array; N : Natural; Last : Integer) return Boolean
   is (for all P in V'Range => (if P <= Last then V (P) < N - P))
   with Ghost,
        Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   --  No draw yet: the predicate holds vacuously. The body of
   --  Draws_Below is hidden from callers, so this has to be stated.
   procedure Lemma_Draws_Below_Empty (V : Index_Array; N : Natural) with
     Ghost,
     Global => null,
     Post   => Draws_Below (V, N, V'First - 1);

   --  v (i) = x, with the draws up to i - 1 already below their bounds.
   procedure Record_Draw
     (V : in out Index_Array; N : Natural; I : Natural; X : Natural)
   with
     Global => null,
     Pre    => I in V'Range and then X < N - I
               and then Draws_Below (V, N, I - 1),
     Post   => Draws_Below (V, N, I);

   --  a = 0 .. n - 1; for i below k: j = i + v (i), swap a (i) and
   --  a (j), r (i) = a (i). Empty when k is 0.
   procedure Choose (N : Natural; V : Index_Array; R : out Index_Array) with
     Global => null,
     Pre    =>
       N <= Max_N
       and then V'First = 0 and then V'Last <= N - 1
       and then R'First = 0 and then R'Last = V'Last
       and then Draws_Below (V, N, V'Last),
     Post   =>
       (for all I in R'Range => R (I) < N)
       and then
         (for all I in R'Range =>
            (for all J in R'Range => (if I /= J then R (I) /= R (J))));

end Fisher_Yates;
