--  Rfft_P256: the Reed-Solomon extension of draft-03 Section 2.2.1 on the
--  P-256 base field (Phase D, block 4, ADR 0057), as the production
--  prover computes it (google/longfellow-zk at d5e6be7,
--  rust/runtime/algebra/src/reed_solomon.rs, middle_product.rs, rfft.rs,
--  fp2.rs, p256/mod.rs).
--
--  Extend takes the values of a polynomial of degree at most d = n - 1 at
--  the points 0 .. n - 1 and returns its values at 0 .. m - 1, the first
--  n unchanged. For k >= n,
--     p(k) = (-1)^d (k - d) C(k, d) SUM over j of x_j / (k - j),
--     x_j  = (-1)^j C(d, j) p(j),
--  and the sum is a middle product of x with the inverses 1 / t, computed
--  as a cyclic convolution of size P = next_power_of_two (m), which never
--  wraps at the indices n .. m - 1. The convolution runs on F_p^2 =
--  F_p[i] / (i^2 + 1), since F_p has no root of unity of order 4 (p - 1
--  is 2 times an odd number) while p + 1 = 2^96 q: a real FFT, whose input
--  lies in F_p and whose conjugate-symmetric output is stored in the
--  half-complex form of FFTW (n elements of F_p), by a radix-4 Cooley-
--  Tukey on the real input (rfft.rs, r2hc and hc2r), with the reference's
--  root of unity of order 2^31.
--
--  Three forms differ from the reference without changing a value. The
--  transforms recurse on the four quarters of a block, where rfft.rs
--  loops over the levels and over the blocks of a level, which are
--  independent. The twiddle factors of a level are read from a table of
--  that level, built from the table of the level above by taking every
--  fourth entry, where rfft.rs reads one table of order P at stride
--  P / size: the same powers of the same root. The input permutation is
--  computed by the recurrence rev (i) = rev (i / 2) / 2 + (i mod 2) P / 2,
--  where bitrev of rfft.rs walks the reversed index with XOR: the same
--  permutation.
--
--  Documentation: docs/guide/08-additive-fft.md (section 1.5 and the P-256
--  sections). Decisions: ADR 0057, 0051 (constant time), 0047 (the work
--  arrays on the heap).
--
--  Proof status. Silver: no run-time error for any row of 1 to 2^16
--  values and any output length up to 2^16, with the ownership checks on
--  the work arrays. Gold, structural: Extend leaves the first n values as
--  they are. That the other values are the Lagrange extension is tested:
--  gen_rs_p256_vectors.py checks a transcription of the reference against
--  Lagrange interpolation, the harness against Lagrange.Evaluate, and the
--  proofs made with this encoder against those made with Lagrange.
--
--  Constant-time discipline (ADR 0051): constant time by construction.
--  Every loop bound, index and twiddle depends on n and m, the public
--  geometry; the values pass through additions, subtractions,
--  multiplications and one inversion of a public number. The guarantee
--  is scoped to builds with assertions disabled (ADR 0006).

pragma SPARK_Mode (On);

with P256_Field;
with Field_P256;
with Sumcheck_Algebra_P256;

package Rfft_P256 is

   subtype Element is P256_Field.Element;
   subtype Element_Array is Sumcheck_Algebra_P256.Element_Array;

   Max_Len  : constant := 2**16;
   Log_Root : constant := 31;

   subtype Log_Size is Natural range 1 .. 16;

   --  An element of F_p^2 = F_p[i] / (i^2 + 1).
   type Fp2 is record
      Re, Im : Element;
   end record;

   type Fp2_Array is array (Natural range <>) of Fp2;

   --  The root of unity of order 2^31 of the reference (p256/mod.rs,
   --  P256_ROOT_OF_UNITY_RE and _IM, four little-endian words each, the
   --  canonical integers, put in the Montgomery form at elaboration).
   Root : constant Fp2 :=
     (Re => P256_Field.From_Canonical
              ([16#985A_6532_4B24_2562#, 16#9FC9_563B_382A_4A4C#,
                16#5CFC_85C6_7990_E337#, 16#F90D_338E_BD84_F566#]),
      Im => P256_Field.From_Canonical
              ([16#DBF4_174F_60A4_3EAC#, 16#8473_8A64_74D2_32C6#,
                16#A04F_C2E2_0106_E340#, 16#B9E8_1E42_BC97_CC4D#]));

   --  The real-to-half-complex transform of size 2^L (rfft.rs, r2hc).
   procedure R2hc (A : in out Element_Array; L : Log_Size) with
     Global            => null,
     Always_Terminates => True,
     Pre               => A'First = 0 and then A'Length = 2**L;

   --  The half-complex-to-real transform of size 2^L (rfft.rs, hc2r).
   procedure Hc2r (A : in out Element_Array; L : Log_Size) with
     Global            => null,
     Always_Terminates => True,
     Pre               => A'First = 0 and then A'Length = 2**L;

   --  The Reed-Solomon extension (reed_solomon.rs, interpolate): Row
   --  holds the values at 0 .. n - 1, Enc receives the values at
   --  0 .. m - 1, n = Row'Length, m = Enc'Length.
   procedure Extend (Row : Element_Array; Enc : out Element_Array) with
     Global            => null,
     Always_Terminates => True,
     Pre               => Row'First = 0 and then Enc'First = 0
                          and then Row'Length >= 1
                          and then Row'Length <= Enc'Length
                          and then Enc'Length <= Max_Len,
     Post              =>
       (for all X in 0 .. Row'Last => Field_P256.Same (Enc (X), Row (X)));

end Rfft_P256;
