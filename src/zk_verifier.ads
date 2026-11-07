--  Zk_Verifier: the complete verifier of Longfellow ZK, ZkVerifier::verify
--  of the reference (docs/specs/rust/src/zk/verifier.rs at d5e6be7) and
--  the reader of a complete proof string of draft Section 7.5
--  (read_zk_proof of zk/proof.rs). Generic over the Ligero verifier of a
--  field, which carries the transcript glue, the proof record and the
--  tables of the same field, and over the packed first step of the same
--  field (Packed_HQuad), which carries the packed circuit.
--
--  A proof string is the Merkle root (32 bytes), the sumcheck part
--  (Section 7.3, read by the stage 4 reader) and the Ligero part
--  (Section 7.4), with no trailing bytes. Verify checks the public
--  input count, reads the string, replays the transcript of stage 4
--  (label, root, statement, the challenges of the core), computes the
--  bound quad of each layer (Bound_Quads), runs the symbolic core of
--  stage 3 for the constraints A, b and the quadratic triples, and
--  hands them with the number of witnesses (Witness_Count of the core)
--  to the Ligero verifier under the fixed statement hash of the
--  reference, DEFAULT_STATEMENT_HASH (ADR 0035: everything
--  statement-specific is already in the transcript). Since ADR 0085 it
--  is the composition of the two phases of ZkVerifier on a fresh
--  transcript: Receive (the proof read from the start of a buffer, the
--  root written) and Verify_Received (the statement, the replay, the
--  core, Ligero), which a flow with two proofs on one transcript (the
--  mDoc layer, ADR 0058) drives itself.
--
--  The circuit is the packed form (Packed_Circuits, the memory
--  milestone, ADR 0080): its shape gives every size, the walk of each
--  layer gives the bound quads, and the expanded circuit is never
--  built. The expansion, Expand (P), exists at level Proof_Only as the
--  model the contracts name.
--
--  Documentation: docs/guide/05-ligero.md, docs/guide/06-circuits.md.
--  Decisions: ADR 0035 (scope, the statement hash), 0039 (sizes, the
--  status), 0028 (the replay), 0071 and 0073 (the bound quads), 0080
--  (the packed form); frame: ADR 0022, 0024. Index: docs/adr/README.md.
--
--  Proof status (per instance). Silver with proved shape: the status is one
--  of the listed values; Public_Input_Length exactly when the public inputs
--  are not the circuit's; Public_Input_Not_One exactly when there are
--  public inputs and the first is not 1 (ADR 0064); the two length statuses
--  of the Ligero verifier cannot occur, since the reader sizes the record
--  by the same geometry. The preconditions of the Ligero verifier (every
--  term and triple of the core below the slots of the constraint vector)
--  are discharged from the postcondition of the core (every witness index
--  below Witness_Count) and the geometry's rows covering the witnesses.
--  Bound_Quads is Gold against BQ_Ref on the expansion, from the
--  postconditions of the packed kernels; Verify asks of the circuit, at
--  level Proof_Only, what the loader's postcondition gives (Valid, and
--  the expansion well formed). Soundness is the paper's theorem, out of
--  scope.
--
--  Sizes (ADR 0039, ADR 0047): the proof, the challenges, the
--  constraints and the quadratic triples form one record sized by the
--  circuit and the geometry, allocated on the heap for the duration of
--  Verify under SPARK's ownership rules and freed on every path; the
--  Ligero verifier does the same for its own working set. The
--  supported scale is the available memory (chapter 6).
--
--  Constant-time discipline (ADR 0006): NOT APPLICABLE, by ADR 0037.
--  Public data only.

pragma SPARK_Mode (On);

with Proof_Levels;
with Bytes;            use Bytes;
with Merkle;
with Transcript;
with Ligero_Geometry;  use Ligero_Geometry;
with Verifier_Status;  use Verifier_Status;
with Ligero_Verifier;
with Packed_HQuad;

generic
   with package LV is new Ligero_Verifier (<>);
   with package PH is new Packed_HQuad
     (SA => LV.ST.SA, HQ => LV.ST.SV.HQ, others => <>);
package Zk_Verifier is

   subtype Element is LV.ST.SA.Element;
   subtype Element_Array is LV.ST.SA.Element_Array;
   subtype Circuit is LV.ST.SA.Circuit;
   subtype Shape is LV.ST.SA.Shape;
   subtype Packed_Circuit is PH.PC.Packed_Circuit;

   use type LV.ST.SA.Element;
   use type LV.ST.SA.Raw_Shape;

   --  The shape of an expanded circuit, for the sizes (Sumcheck_Algebra).
   function Shape_Of (C : Circuit) return Shape is (LV.ST.SA.Shape_Of (C))
   with Global => null;

   --  The shape of a packed circuit, for the sizes. What makes it a
   --  Shape is the loader's postcondition: the packed form is valid and
   --  its expansion is well formed (Lemma_Shape_Of of Packed_Circuits).
   function Shape_Of (P : Packed_Circuit) return Shape with
     Global => null,
     Pre    => (Proof_Only =>
                  PH.PC.Valid (P)
                  and then LV.ST.SA.Well_Formed (PH.PC.Expand (P))),
     Post   => Shape_Of'Result = PH.PC.Shape_Of (P);

   subtype Sumcheck_Proof is LV.ST.SV.Sumcheck_Proof;
   subtype Ligero_Part is LV.LP.Proof;

   --  DEFAULT_STATEMENT_HASH of zk/common.rs.
   Default_Statement_Hash : constant Bytes_32 :=
     [16#de#, 16#ad#, 16#be#, 16#ef#, others => 0];

   --  nw: the private inputs then the pads of every layer.
   function Witness_Count (S : Shape) return Natural
     renames LV.ST.SV.Witness_Count;

   --  The geometry of a circuit under a configuration (NQ = one
   --  quadratic triple per layer).
   function Geometry_Of (Cfg : Config; S : Shape) return Valid_Geometry is
     (Make (Cfg, Witness_Count (S), S.Last_Layer + 1))
   with Pre => Valid (Cfg);

   --  Bytes of the sumcheck part.
   function Sumcheck_Len (S : Shape) return Natural is
     (LV.ST.SV.Proof_Total (S) * LV.LP.Size);

   --  Section 7.5 for one proof: the root, the sumcheck part, the
   --  Ligero part, nothing after. Proof_Encoding on bytes missing or
   --  trailing, on a non-canonical element and on every violation the
   --  two readers report; the outputs are then not to be used.
   procedure Read_Proof
     (B        : Byte_Array;
      S        : Shape;
      G        : Valid_Geometry;
      Root     : out Bytes_32;
      Sumcheck : out Sumcheck_Proof;
      Lig      : out Ligero_Part;
      St       : out Status)
   with
     Global => null,
     Pre    =>
       B'First = 0 and then LV.LP.Fits (G)
       and then Sumcheck.Last + 1 = LV.ST.SV.Proof_Total (S)
       and then Lig.Ldt_Last + 1 = G.Block_Len
       and then Lig.Linear_Last + 1 = G.Dblock_Len
       and then Lig.Low_Last + 1 = G.Num_Queries
       and then Lig.High_Last + 1 = G.Dblock_Len - G.Block_Len
       and then Lig.Nonce_Last + 1 = G.Num_Queries
       and then Lig.Col_Last + 1 = LV.LP.Opened (G)
       and then Lig.Path_Last + 1 = 2 * Num_Leaves (G),
     Post   => St in Ok | Proof_Encoding;

   --  Read_Proof for a proof that starts at Off in a buffer that holds
   --  more (the mDoc proof of ADR 0058: six MACs, the hash proof, the
   --  signature proof): Next is the offset after it, at most B'Length.
   --  Read_Proof is this at Off = 0 with Next = B'Length required.
   procedure Read_Proof_Prefix
     (B        : Byte_Array;
      Off      : Natural;
      S        : Shape;
      G        : Valid_Geometry;
      Root     : out Bytes_32;
      Sumcheck : out Sumcheck_Proof;
      Lig      : out Ligero_Part;
      Next     : out Natural;
      St       : out Status)
   with
     Global => null,
     Pre    =>
       B'First = 0 and then Off <= B'Length and then LV.LP.Fits (G)
       and then Sumcheck.Last + 1 = LV.ST.SV.Proof_Total (S)
       and then Lig.Ldt_Last + 1 = G.Block_Len
       and then Lig.Linear_Last + 1 = G.Dblock_Len
       and then Lig.Low_Last + 1 = G.Num_Queries
       and then Lig.High_Last + 1 = G.Dblock_Len - G.Block_Len
       and then Lig.Nonce_Last + 1 = G.Num_Queries
       and then Lig.Col_Last + 1 = LV.LP.Opened (G)
       and then Lig.Path_Last + 1 = 2 * Num_Leaves (G),
     Post   => St in Ok | Proof_Encoding
               and then (if St = Ok then Next in Off .. B'Length);

   --  The bound quads of the verifier (ADR 0071, ADR 0073), layer by
   --  layer from the packed circuit: Bind_Quad_Packed when the eq tables
   --  fit, Eval_Bound_Quad_Packed otherwise, the choice BQ_Ref makes. S
   --  is the shape of P, taken once by the caller. The result is stated
   --  on the expansion, as the kernels state theirs.
   procedure Bound_Quads
     (P  : Packed_Circuit;
      S  : Shape;
      Ch : LV.ST.SV.Challenges;
      BQ : out Element_Array)
   with
     Global => null,
     Pre    =>
       (Runtime    =>
          S = PH.PC.Shape_Of (P)
          and then Ch.Last + 1 = LV.ST.SV.Chal_Total (S)
          and then BQ'First = 0 and then BQ'Length = S.Last_Layer + 1,
        Proof_Only =>
          PH.PC.Valid (P)
          and then LV.ST.SA.Well_Formed (PH.PC.Expand (P))),
     Post   =>
       (Proof_Only =>
          (for all J in 0 .. S.Last_Layer =>
             LV.ST.SA.Same (BQ (J),
                            LV.ST.SV.BQ_Ref (PH.PC.Expand (P), Ch, J))));

   --  The two phases of ZkVerifier (recv_commitment, verify) for a
   --  transcript the caller opened (ADR 0085): Receive reads the proof
   --  at Off in B and writes its root to the transcript;
   --  Verify_Received replays the statement and the challenges, runs the
   --  core and the Ligero verifier, and frees the record. A flow with two
   --  proofs on one transcript (the mDoc layer, ADR 0058) receives both
   --  before it verifies either; Verify below is the two phases on a
   --  fresh transcript for one proof. Between the phases Received holds
   --  the proof read, on the heap under the ownership rules of ADR 0047,
   --  freed by Verify_Received or by Release.
   type Received is private;

   --  Nothing held: after Receive failed, Verify_Received, or Release.
   function Is_Null (R : Received) return Boolean with Global => null;

   --  The record holds a proof for a circuit of the shape of P under
   --  Cfg: the precondition of Verify_Received, the postcondition of a
   --  Receive that succeeded.
   function Fits (R : Received; Cfg : Config; P : Packed_Circuit)
                  return Boolean
   with
     Global => null,
     Pre    => (Runtime    => Valid (Cfg),
                Proof_Only =>
                  PH.PC.Valid (P)
                  and then LV.ST.SA.Well_Formed (PH.PC.Expand (P)));

   --  The offset after the proof read, in the buffer given to Receive.
   function After (R : Received) return Natural with Global => null;

   procedure Release (R : in out Received) with
     Global => null,
     Post   => Is_Null (R);

   procedure Receive
     (B   : Byte_Array;
      Off : Natural;
      Cfg : Config;
      P   : Packed_Circuit;
      R   : out Received;
      St  : out Status)
   with
     Global => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Pre    =>
       (Runtime    =>
          Valid (Cfg) and then B'First = 0 and then Off <= B'Length,
        Proof_Only =>
          PH.PC.Valid (P)
          and then LV.ST.SA.Well_Formed (PH.PC.Expand (P))),
     Post   =>
       St in Ok | Proof_Encoding
       and then (if St = Ok then Fits (R, Cfg, P)
                                 and then After (R) in Off .. B'Length
                 else Is_Null (R));

   procedure Verify_Received
     (Id  : Bytes_32;
      Cfg : Config;
      P   : Packed_Circuit;
      Pub : Element_Array;
      R   : in out Received;
      St  : out Status)
   with
     Global            => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Always_Terminates => False,
     --  Fits is stated after the loader's postcondition, which its own
     --  precondition needs; at the proof-only level it is still what the
     --  body is proved from.
     Pre               =>
       (Runtime    => Valid (Cfg) and then Pub'First = 0,
        Proof_Only =>
          PH.PC.Valid (P)
          and then LV.ST.SA.Well_Formed (PH.PC.Expand (P))
          and then Fits (R, Cfg, P)),
     Post              =>
       Is_Null (R)
       and then St not in Queried_Columns_Length | Polynomial_Lengths
       and then (St = Public_Input_Length) = (Pub'Length /= P.Npublic)
       and then (St = Public_Input_Not_One)
                = (Pub'Length = P.Npublic and then P.Npublic > 0
                   and then Pub (0) /= LV.ST.SA.One);

   --  ZkVerifier::verify: Label the transcript label, Id the circuit
   --  identifier of the statement (Section 3.3), Cfg the Ligero
   --  configuration, P the circuit in its packed form, Pub the public
   --  inputs, B the proof string. Proof_Encoding also when the
   --  geometry's opened columns do not fit this implementation (ADR
   --  0039) and when bytes follow the proof. The precondition on P is
   --  the postcondition of the loader. The body is the two checks on
   --  Pub, Reset with the label, Receive at 0, Verify_Received.
   procedure Verify
     (Label : Byte_Array;
      Id    : Bytes_32;
      Cfg   : Config;
      P     : Packed_Circuit;
      Pub   : Element_Array;
      B     : Byte_Array;
      St    : out Status)
   with
     Global            => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Always_Terminates => False,
     Pre               =>
       (Runtime    =>
          Label'Length <= Transcript.Max_Payload
          and then Valid (Cfg)
          and then Pub'First = 0
          and then B'First = 0,
        Proof_Only =>
          PH.PC.Valid (P)
          and then LV.ST.SA.Well_Formed (PH.PC.Expand (P))),
     Post              =>
       St not in Queried_Columns_Length | Polynomial_Lengths
       and then (St = Public_Input_Length) = (Pub'Length /= P.Npublic)
       and then (St = Public_Input_Not_One)
                = (Pub'Length = P.Npublic and then P.Npublic > 0
                   and then Pub (0) /= LV.ST.SA.One);

private

   -------------------------------------------------------------------
   --  The working set of one verification, in one allocation on the
   --  heap (ADR 0047): the padded sumcheck proof, the Ligero part, the
   --  challenges, the constraint terms, the constants b and the
   --  quadratic triples, each sized by the circuit or the geometry
   --  through a discriminant. Here rather than in the body so that
   --  Received can hold it between the two phases.
   -------------------------------------------------------------------

   subtype Index is LV.ST.SA.Index;
   subtype Merkle_Node_Index is Merkle.Node_Index;

   type Work
     (Sum_Last    : Index;
      Ldt_Last    : Index;
      Linear_Last : Index;
      Low_Last    : Index;
      High_Last   : Index;
      Nonce_Last  : Index;
      Col_Last    : Index;
      Path_Last   : Merkle_Node_Index;
      Ch_Last     : Index;
      A_Max       : Index;
      B_Last      : Index;
      Lqc_Last    : Index)
   is record
      Sumcheck : Sumcheck_Proof (Sum_Last);
      Lig      : Ligero_Part (Ldt_Last, Linear_Last, Low_Last, High_Last,
                              Nonce_Last, Col_Last, Path_Last);
      Ch       : LV.ST.SV.Challenges (Ch_Last);
      A        : LV.ST.SV.Ligero_Terms (A_Max);
      B_Vec    : Element_Array (0 .. B_Last);
      Lqc      : LV.ST.SV.Lqc_Array (0 .. Lqc_Last);
      BQ       : Element_Array (0 .. Lqc_Last);
   end record;

   type Work_Access is access Work;

   --  The discriminants of W are those of S under G.
   function Work_Shape
     (W : Work; S : Shape; G : Valid_Geometry) return Boolean
   is
     (W.Sum_Last + 1 = LV.ST.SV.Proof_Total (S)
      and then W.Ldt_Last + 1 = G.Block_Len
      and then W.Linear_Last + 1 = G.Dblock_Len
      and then W.Low_Last + 1 = G.Num_Queries
      and then W.High_Last + 1 = G.Dblock_Len - G.Block_Len
      and then W.Nonce_Last + 1 = G.Num_Queries
      and then W.Col_Last + 1 = LV.LP.Opened (G)
      and then W.Path_Last + 1 = 2 * Num_Leaves (G)
      and then W.Ch_Last + 1 = LV.ST.SV.Chal_Total (S)
      and then W.A_Max = LV.ST.SV.A_Bound (S)
      and then W.B_Last = S.Last_Layer + 1
      and then W.Lqc_Last = S.Last_Layer)
   with Global => null, Pre => LV.LP.Fits (G);

   type Shape_Access is access Shape;

   --  The root, the offset after the proof, the working set with the
   --  proof read, and the shape the proof was read under, layer by
   --  layer, which Verify_Received requires of its circuit.
   type Received is record
      Root : Bytes_32;
      Next : Natural;
      W    : Work_Access;
      S    : Shape_Access;
   end record;

   function Is_Null (R : Received) return Boolean is
     (R.W = null and then R.S = null);

   function After (R : Received) return Natural is (R.Next);

   function Fits (R : Received; Cfg : Config; P : Packed_Circuit)
                  return Boolean
   is
     (R.W /= null and then R.S /= null
      and then R.S.all = Shape_Of (P)
      and then LV.LP.Fits (Geometry_Of (Cfg, Shape_Of (P)))
      and then Work_Shape (R.W.all, Shape_Of (P),
                           Geometry_Of (Cfg, Shape_Of (P))));

end Zk_Verifier;
