--  Sumcheck_Transcript: the glue between the field-agnostic Transcript
--  and the sumcheck verifier core of stage 3: the sampler of draft
--  Section 3.4.3, the element frames, the statement of Section 3.3
--  (zk/common.rs), the protocol helpers of sumcheck/common.rs, the
--  replay of every challenge of a proof into the Challenges record of
--  Sumcheck_Verifier, and the reader of the sumcheck part of a proof
--  (Section 7.3) into Sumcheck_Proof. Generic over the three stage 3
--  instances of a field.
--
--  Documentation: docs/guide/04-transcript.md. Decisions: ADR 0028
--  (scope, the absorption order of zk/verifier.rs, the status), 0030
--  (Sample as a literal rejection loop, terminating exactly when the
--  field does not reject), 0031 (Gold on the frames and the statement;
--  Silver with proved shape on the replay and the reader); frame: ADR
--  0022, 0024. Index: docs/adr/README.md.
--
--  Proof status (per instance).
--    Sample           : Silver; Always_Terminates exactly when
--                       F.Sampling_Rejects is False (ADR 0030). The
--                       result is canonical by the element type.
--    Write_Element, Write_Element_Slice, Round_Poly, End_Layer,
--    Write_Sumcheck_Statement : Gold, structural (ADR 0023): the frames
--                       appended to Transcript.Absorbed, stated with the
--                       ghost frame functions, proof-only as in
--                       Transcript. Serialise is Gold on its layout.
--    Begin_Circuit, Begin_Layer, Replay_Challenges : Silver with the
--                       Exhausted flag sticky; Replay_Challenges fills
--                       a record whose shape the preconditions fix and
--                       reports Exhausted when the generator ran out.
--    Read_Sumcheck_Proof : Silver; Bad_Element when an encoding is not
--                       canonical, as read_elt_field fails upstream.
--
--  The absorption order of Replay_Challenges is the checklist of ADR
--  0028, line by line against docs/specs/rust/src/zk/verifier.rs and
--  zk/symbolic_sumcheck_verifier.rs at d5e6be7: label, root, statement
--  (identifier, each public input as an element frame, the zero
--  element, write0 of the term count), begin_circuit (40 draws
--  discarded, 40 draws g), then per layer begin_layer (alpha, beta),
--  for each round and each hand round_poly (p (0), p (P2), one draw),
--  end_layer (the two claims as one slice), and after the last layer
--  one draw, alpha_input. Agreement with the upstream verifier is
--  tested on the recorded runs of Appendix B.3 (ADR 0032).
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0029.
--  Public data only.

pragma SPARK_Mode (On);

with Bytes;      use Bytes;
with Transcript;
with Sumcheck_Algebra;
with Sumcheck_Expression;
with Sumcheck_Verifier;

generic
   with package SA is new Sumcheck_Algebra (<>);
   with package SE is new Sumcheck_Expression (SA => SA);
   with package SV is new Sumcheck_Verifier (SA => SA, SE => SE);
package Sumcheck_Transcript is

   use SA;
   use SV;

   subtype Element is SA.Element;

   --  Bytes per element (draft Section 7.2.1).
   Size : constant Positive := SA.F.Serialized_Size;

   subtype Elt_Bytes is Byte_Array (0 .. Size - 1);

   type Status is (Ok, Exhausted, Bad_Element);

   --  At most this many elements in one slice frame; End_Layer writes
   --  two.
   Max_Slice : constant := 4096;

   --  The elements, serialised, concatenated in order.
   function Serialise (Es : Element_Array) return Byte_Array with
     Global => null,
     Pre    => Es'Length <= Max_Slice,
     Post   =>
       Serialise'Result'First = 0
       and then Serialise'Result'Length = Es'Length * Size
       and then
         (for all I in 0 .. Es'Length - 1 =>
            Serialise'Result (I * Size .. I * Size + Size - 1)
            = SA.F.To_Bytes (Es (Es'First + I)));

   ----------------------------------------------------------------------
   --  Section 3.4.3: the sampler
   ----------------------------------------------------------------------

   --  Serialized_Size bytes, From_Bytes, again until accepted. For a
   --  field that rejects nothing (GF(2^128)) one draw; for P-256 a
   --  loop with no cap (ADR 0030).
   procedure Sample (E : out Element) with
     Global            => (In_Out => Transcript.State),
     Always_Terminates => not SA.F.Sampling_Rejects,
     Post              => Transcript.Is_Exhausted'Old <= Transcript.Is_Exhausted;

   ----------------------------------------------------------------------
   --  The frames over elements, and the statement
   ----------------------------------------------------------------------

   procedure Write_Element (E : Element) with
     Global => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Post   =>
       (SPARKlib_Full =>
          Transcript.Is_Exhausted'Old <= Transcript.Is_Exhausted
          and then Byte_Seqs.Logical_Eq
            (Transcript.Absorbed,
             Transcript.Element_Frame
               (Transcript.Absorbed'Old, SA.F.To_Bytes (E))));

   procedure Write_Element_Slice (Es : Element_Array) with
     Global => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Pre    => Es'Length <= Max_Slice,
     Post   =>
       (SPARKlib_Full =>
          Transcript.Is_Exhausted'Old <= Transcript.Is_Exhausted
          and then Byte_Seqs.Logical_Eq
            (Transcript.Absorbed,
             Transcript.Slice_Frame
               (Transcript.Absorbed'Old, Es'Length, Serialise (Es))));

   --  S followed by the element frames of Pub (Pub'First .. Pub'First
   --  + N - 1), in order (ghost, proof-only). Recursive, hence hidden
   --  (see Bytes.Add_Zeros); Write_Sumcheck_Statement unhides it.
   function Publics_Frame
     (S : Byte_Seq; Pub : Element_Array; N : Natural) return Byte_Seq
   is
     (if N = 0 then S
      else Transcript.Element_Frame
             (Publics_Frame (S, Pub, N - 1),
              SA.F.To_Bytes (Pub (Pub'First + N - 1))))
   with
     Ghost              => SPARKlib_Full,
     Annotate           => (GNATprove, Hide_Info, "Expression_Function_Body"),
     Pre                => N <= Pub'Length,
     Subprogram_Variant => (Decreases => N);

   --  Section 3.3 and zk/common.rs write_sumcheck_statement: the
   --  identifier as a byte array frame, each public input as its own
   --  element frame, the zero element, then write0 of the term count
   --  over all layers (C.NT, since the layers partition the terms).
   function Statement_Frame
     (S : Byte_Seq; Id : Bytes_32; C : Circuit; Pub : Element_Array)
      return Byte_Seq
   is
     (Transcript.Zero_Frame
        (Transcript.Element_Frame
           (Publics_Frame (Transcript.Bytes_Frame (S, Id), Pub, Pub'Length),
            SA.F.To_Bytes (Zero)),
         C.NT))
   with Ghost => SPARKlib_Full;

   procedure Write_Sumcheck_Statement
     (Id : Bytes_32; C : Circuit; Pub : Element_Array)
   with
     Global => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Pre    => Pub'First = 0 and then Pub'Length = C.Npublic,
     Post   =>
       (SPARKlib_Full =>
          Transcript.Is_Exhausted'Old <= Transcript.Is_Exhausted
          and then Byte_Seqs.Logical_Eq
            (Transcript.Absorbed,
             Statement_Frame (Transcript.Absorbed'Old, Id, C, Pub)));

   ----------------------------------------------------------------------
   --  sumcheck/common.rs: the protocol helpers
   ----------------------------------------------------------------------

   --  MAX_LOGW draws discarded (reserved by the draft, Section 6.6),
   --  then MAX_LOGW draws: the output-binding challenges g.
   procedure Begin_Circuit (G : out Challenge_Vector) with
     Global            => (In_Out => Transcript.State),
     Always_Terminates => not SA.F.Sampling_Rejects,
     Post              => Transcript.Is_Exhausted'Old <= Transcript.Is_Exhausted;

   procedure Begin_Layer (Alpha, Beta : out Element) with
     Global            => (In_Out => Transcript.State),
     Always_Terminates => not SA.F.Sampling_Rejects,
     Post              => Transcript.Is_Exhausted'Old <= Transcript.Is_Exhausted;

   --  The two padded evaluations of one hand of one round, each as an
   --  element frame, then one draw.
   procedure Round_Poly (P0, P2 : Element; Ch : out Element) with
     Global            => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Always_Terminates => not SA.F.Sampling_Rejects,
     Post              =>
       (SPARKlib_Full =>
          Transcript.Is_Exhausted'Old <= Transcript.Is_Exhausted
          and then Byte_Seqs.Logical_Eq
            (Transcript.Absorbed,
             Transcript.Element_Frame
               (Transcript.Element_Frame
                  (Transcript.Absorbed'Old, SA.F.To_Bytes (P0)),
                SA.F.To_Bytes (P2))));

   --  The two padded claims of a layer, as the slice they are written
   --  as (one name for the pair, so that the postcondition of
   --  End_Layer and its body speak of the same array).
   function Claims_Pair (Claim0, Claim1 : Element) return Element_Array is
     (Element_Array'[Claim0, Claim1])
   with Global => null,
        Post   => Claims_Pair'Result'First = 0
                  and then Claims_Pair'Result'Length = 2;

   --  The two padded claims of a layer as one slice frame.
   procedure End_Layer (Claim0, Claim1 : Element) with
     Global => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Post   =>
       (SPARKlib_Full =>
          Transcript.Is_Exhausted'Old <= Transcript.Is_Exhausted
          and then Byte_Seqs.Logical_Eq
            (Transcript.Absorbed,
             Transcript.Slice_Frame
               (Transcript.Absorbed'Old, 2,
                Serialise (Claims_Pair (Claim0, Claim1)))));

   ----------------------------------------------------------------------
   --  The replay and the reader
   ----------------------------------------------------------------------

   --  Every challenge the core consumes, from the proof: Ch.G, per
   --  layer alpha, beta and the round challenges at Chal_Off (C, J),
   --  Ch.Alpha_Input. St is Exhausted when the generator passed its
   --  bound during the replay (ADR 0028); the record is then not to be
   --  used.
   procedure Replay_Challenges
     (Label : Byte_Array;
      Root  : Bytes_32;
      Id    : Bytes_32;
      C     : Circuit;
      Pub   : Element_Array;
      Proof : Sumcheck_Proof;
      Ch    : out Challenges;
      St    : out Status)
   with
     Global            => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Always_Terminates => not SA.F.Sampling_Rejects,
     Pre               =>
       Label'Length <= Transcript.Max_Payload
       and then Pub'First = 0 and then Pub'Length = C.Npublic
       and then Proof.Last + 1 = Proof_Total (C)
       and then Ch.Last + 1 = Chal_Total (C),
     Post              => St in Ok | Exhausted
       and then (St = Ok) = not Transcript.Is_Exhausted;

   --  The sumcheck part of a proof string (Section 7.3: per layer, per
   --  round the four elements hand 0 p (0), hand 1 p (0), hand 0 p (P2),
   --  hand 1 p (P2), then the two claims; no length prefix) into the
   --  pad order of Section 6.5. Bad_Element when an encoding is not
   --  canonical; the output is then not to be used.
   procedure Read_Sumcheck_Proof
     (B     : Byte_Array;
      C     : Circuit;
      Proof : out Sumcheck_Proof;
      St    : out Status)
   with
     Global => null,
     Pre    =>
       B'First = 0 and then B'Length = Proof_Total (C) * Size
       and then Proof.Last + 1 = Proof_Total (C),
     Post   => St in Ok | Bad_Element;

end Sumcheck_Transcript;
