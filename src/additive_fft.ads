--  Additive_Fft: the Reed-Solomon extension of draft-03 Section 2.2.2 on
--  GF(2^128) by the additive FFT of Lin, Chung and Han (2014) in the
--  novel polynomial basis (Phase D, block 3, ADR 0057), in the form of
--  the production prover (longfellow-zk/longfellow-zk at d5e6be7,
--  rust/runtime/algebra/src/lch14.rs and lch14_reed_solomon.rs).
--
--  Extend takes the values of a polynomial of degree below n at the
--  points inj (0 .. n - 1) and returns its values at inj (0 .. m - 1),
--  the first n unchanged, where inj (i) is the XOR of the subfield basis
--  elements beta_j over the set bits j of i (GF2_128.Inject). It runs
--  the bidirectional FFT on the first 2^l points, l the smallest with
--  2^l >= n, then one forward FFT per coset of 2^l points up to m.
--
--  Two forms differ from the reference without changing a value. The
--  transforms recurse on the two halves of a block (the top level of
--  butterflies first for Fft, last for Ifft), which visits the
--  butterflies of lch14.rs in an order where every level is independent
--  of the others; and each twiddle factor is computed directly, as
--  Twiddle (i, coset + offset), where twiddles of lch14.rs builds the
--  same values incrementally.
--
--  Documentation: docs/guide/08-additive-fft.md. Decisions: ADR 0057,
--  0051 (constant time), 0047 (the work arrays on the heap).
--
--  Proof status. Silver: no run-time error for any row of 1 to 2^16
--  values and any output length up to 2^16, with the ownership checks
--  on the two work arrays. Gold, structural: Extend leaves the first n
--  values as they are (the systematic part of the code). That the other
--  values are those of the polynomial through the first n, the values
--  of the Lagrange encoding of chapter 5, is tested, not proved: on the
--  vectors of gen_fft_vectors.py, where a transcription of lch14.rs is
--  checked against barycentric Lagrange interpolation, in fft_kat
--  against Lagrange.Evaluate, and by the byte identity of the proofs
--  made with either encoder. The points stay in the subfield because m
--  is at most 2^16; Twiddle reads the sixteen low bits of its index, so
--  the bounds on the cosets below only exclude overflow.
--
--  Constant-time discipline (ADR 0051): constant time by construction.
--  Every loop bound, every index and every twiddle depends on n and m
--  only, which are public (the geometry of the proof); the values pass
--  through additions and multiplications only. The guarantee is scoped
--  to builds with assertions disabled (ADR 0006).

pragma SPARK_Mode (On);

with GF2_128;
with Field_GF2_128;
with Sumcheck_Algebra_GF2_128;

package Additive_Fft is

   subtype Element is GF2_128.Element;
   subtype Element_Array is Sumcheck_Algebra_GF2_128.Element_Array;

   --  The dimension of the subfield GF(2^16), hence the most points.
   Dim     : constant := 16;
   Max_Len : constant := 2**Dim;

   --  A bound on the coset offsets that keeps their sums from
   --  overflowing; the offsets Extend uses stay below 2^17.
   Max_Coset : constant := 2**20;

   subtype Coord is Natural range 0 .. Dim - 1;
   subtype Level is Natural range 0 .. Dim;

   --  W_Hat (I, J) is the normalised subspace vanishing polynomial
   --  W_I / W_I (beta_I) at beta_J: W_0 (X) = X and W_I+1 (X) =
   --  W_I (X) (W_I (X) + W_I (beta_I)) (lch14.rs, Lch14::new). The
   --  table is computed once, when the body is elaborated.
   function W_Hat (I, J : Coord) return Element with Global => null;

   --  The twiddle factor of level I at point U: the sum of W_Hat (I, K)
   --  over the set bits K below 16 of U (lch14.rs, twiddle).
   function Twiddle (I : Coord; U : Natural) return Element with
     Global => null;

   --  The forward transform of level L on B (Off .. Off + 2^L - 1), at
   --  the points of the coset Coset (lch14.rs, fft).
   procedure Fft
     (L     : Level;
      Coset : Natural;
      B     : in out Element_Array;
      Off   : Natural)
   with
     Global            => null,
     Always_Terminates => True,
     Pre    => B'First = 0 and then Off <= B'Length
               and then 2**L <= B'Length - Off
               and then Coset <= Max_Coset - 2**L,
     Subprogram_Variant => (Decreases => L);

   --  The inverse transform (lch14.rs, ifft).
   procedure Ifft
     (L     : Level;
      Coset : Natural;
      B     : in out Element_Array;
      Off   : Natural)
   with
     Global            => null,
     Always_Terminates => True,
     Pre    => B'First = 0 and then Off <= B'Length
               and then 2**L <= B'Length - Off
               and then Coset <= Max_Coset - 2**L,
     Subprogram_Variant => (Decreases => L);

   --  The bidirectional transform (lch14.rs, bidir_recur): the first K
   --  entries are values, the others coefficients, and it swaps the two
   --  domains.
   procedure Bidir
     (L     : Level;
      Coset : Natural;
      K     : Natural;
      B     : in out Element_Array;
      Off   : Natural)
   with
     Global            => null,
     Always_Terminates => True,
     Pre    => B'First = 0 and then Off <= B'Length
               and then 2**L <= B'Length - Off
               and then K <= 2**L
               and then Coset <= Max_Coset - 2**L,
     Subprogram_Variant => (Decreases => L);

   --  The Reed-Solomon extension (lch14_reed_solomon.rs, interpolate):
   --  Row holds the values at inj (0 .. n - 1), Enc receives the values
   --  at inj (0 .. m - 1), n = Row'Length, m = Enc'Length.
   procedure Extend (Row : Element_Array; Enc : out Element_Array) with
     Global            => null,
     Always_Terminates => True,
     Pre    => Row'First = 0 and then Enc'First = 0
               and then Row'Length >= 1
               and then Row'Length <= Enc'Length
               and then Enc'Length <= Max_Len,
     Post   =>
       (for all X in 0 .. Row'Last => Field_GF2_128.Same (Enc (X), Row (X)));

end Additive_Fft;
