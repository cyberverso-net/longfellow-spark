--  Zk_Prover: ZkProver::commit and ZkProver::prove of the reference
--  (docs/specs/rust/src/zk/prover.rs at d5e6be7), from the circuit and
--  its inputs to the proof string of Section 7.5 (Phase C, ADR 0049,
--  0050, 0051), as two phases on a transcript the caller opens
--  (Commit, Prove_Committed; ADR 0085, for the mDoc layer of ADR 0058,
--  which commits two circuits before it proves either) and as their
--  composition on a fresh transcript for one proof (Prove). Generic
--  over the Ligero prover of a field (which carries the verifier units,
--  the sampling instance and the randomness source), the sumcheck
--  prover over the same transcript glue, the writers and the
--  evaluation of the packed circuit. Since the memory milestone (ADR
--  0080) the circuit comes in its packed form, never expanded: the
--  sizes from its shape, the wires from the walk (Packed_Eval), the
--  sumcheck from the walk (Sumcheck_Prover with Packed_HQuad).
--
--  The checks, as statuses (ADR 0049): the private inputs are
--  ninput - npublic elements and the public ones npublic
--  (Input_Length); the first public input is 1 when the circuit has
--  public inputs (Input_Not_One, OneWire of ADR 0064); the two together
--  satisfy the circuit (Not_Satisfied, from Eval_Circuit of
--  Packed_Eval: every output of layer 0 zero and every Z assertion
--  met); and the witnesses the writer will project on the subfield lie
--  in it (Not_In_Subfield): those of the witness rows wholly below the
--  subfield boundary (Proof_Writer.Sub_Rows, the rows the reference
--  writer projects and where its prover would panic), which must all
--  be private inputs (a pad there is a full-field element) and each of
--  which is projected with the fixed map of ADR 0051, re-injected and
--  compared, the differences accumulated in one mask; nothing is
--  projected when the field is its own subfield (P-256). The
--  satisfiability and subfield checks are skipped when the generic
--  formal Validate is False, which only the test project does. Commit
--  makes the checks on the private inputs, then, in the reference's
--  order, the pads (Sample_Pads), the witness vector (the private
--  inputs, then the pads), the quadratic triples (Lqc_Triples), the
--  Ligero commitment (Commit; Config_Invalid when a Lagrange
--  denominator has no inverse) and the root on the transcript.
--  Prove_Committed makes the checks on the public inputs and the
--  satisfiability check, which needs both (ADR 0085: before the
--  commitment in ADR 0049, in the proving phase since), then the
--  statement, the sumcheck proof on the live transcript with its
--  challenges recorded (Sumcheck_Prover.Prove), the verifier core on
--  those challenges for the constraints (ADR 0022, 0049), the Ligero
--  proof under the fixed statement hash of zk/ common.rs (Exhausted
--  when the generator passes its bound), and the bytes (Write_Proof).
--  Memory: the pads, the witness vector, the proofs and the constraints
--  live on the heap (ADR 0047), held by Committed between the phases;
--  the wires one heap segment per layer, each freed by the sumcheck
--  prover once its layer is proved (ADR 0080, block 4).
--
--  Documentation: docs/guide/07-prover.md.
--
--  Proof status (per instance). Silver with the ownership checks on
--  the heap objects; the lengths and offsets of the proof string by the
--  writers' contracts. Completeness (the verifier accepts the proof) is
--  tested, not proved (ADR 0052).
--
--  Constant-time discipline (ADR 0051): the two branches on witness-
--  derived values are the satisfiability check and the subfield check,
--  each a fixed loop accumulating its result without a branch on the
--  values (a byte mask in the subfield check, a Boolean `and` on the
--  comparison with Zero in Packed_Eval.Eval_Circuit) and one branch
--  on the result, the prover's own decision whether to produce a
--  proof. The rest is constant time by construction in the units it
--  calls. The guarantee is scoped to builds with assertions disabled
--  (ADR 0006).

pragma SPARK_Mode (On);

with Bytes;            use Bytes;
with Merkle;
with Transcript;
with Prover_Status;    use Prover_Status;
with Ligero_Geometry;  use Ligero_Geometry;
with Ligero_Prover;
with Sumcheck_Prover;
with Proof_Writer;
with Packed_HQuad;
with Packed_Eval;
with Proof_Levels;

generic
   with package LPR is new Ligero_Prover (<>);
   --  The first step of a layer from the packed circuit, over the
   --  algebra and the kernels of the verifier units of LPR; the sumcheck
   --  prover takes it, and the evaluation of the packed circuit shares
   --  its packed form.
   with package PH  is new Packed_HQuad
     (SA => LPR.LV.ST.SA, HQ => LPR.LV.ST.SV.HQ, others => <>);
   with package SPR is new Sumcheck_Prover
     (ST => LPR.LV.ST, PH => PH, others => <>);
   with package PW  is new Proof_Writer (LV => LPR.LV);
   with package PE  is new Packed_Eval (SA => LPR.LV.ST.SA, PC => PH.PC);
   --  Validate: the satisfiability and subfield checks run (every
   --  instance of the library and of the command-line prover). False
   --  exists for the test project only (ADR 0053): a prover that proves
   --  false inputs, whose proof the verifier must refuse.
   Validate : Boolean := True;
package Zk_Prover is

   --  As in the body (ADR 0072): the predicates of the circuit are
   --  checked once where a circuit enters the program (the loader proves
   --  them, the command line checks their executable part), and the
   --  expression functions below, which the command line calls with the
   --  circuit, do not walk it again. GNATprove proves these checks as
   --  before.
   pragma Suppress (Predicate_Check);

   subtype Element is LPR.LV.ST.SA.Element;
   subtype Element_Array is LPR.LV.ST.SA.Element_Array;
   subtype Shape is LPR.LV.ST.SA.Shape;
   subtype Packed_Circuit is PH.PC.Packed_Circuit;

   --  The shape of the packed circuit, for the sizes (Sumcheck_Algebra).
   --  Its precondition is the executable part of what the loader proves
   --  of the circuit, which the command line checks once where the
   --  circuit enters the program (ADR 0072): the indices of the form,
   --  its layers, Shape_Ok of its shape.
   function Shape_Of (P : Packed_Circuit) return Shape is
     (PH.PC.Shape_Of (P))
   with Global => null,
        Pre  => PH.PC.Indices_Ok (P) and then PH.PC.Layers_Ok (P)
                and then LPR.LV.ST.SA.Shape_Ok (PH.PC.Shape_Of (P));

   use type LPR.LV.ST.SA.Element;
   use type LPR.Commitment_Access;
   use type LPR.LV.ST.SA.Raw_Shape;

   --  The statement hash the reference passes to Ligero, fixed for
   --  backward compatibility (DEFAULT_STATEMENT_HASH of zk/common.rs);
   --  the statement itself is in the transcript already.
   Default_Statement_Hash : constant Bytes_32 :=
     [16#de#, 16#ad#, 16#be#, 16#ef#, others => 0];

   function Witness_Count (S : Shape) return Natural
     renames LPR.LV.ST.SV.Witness_Count;

   --  The geometry of a proof of C under Cfg (as the verifier's).
   function Geometry_Of (Cfg : Config; S : Shape) return Valid_Geometry is
     (Make (Cfg, Witness_Count (S), S.Last_Layer + 1))
   with Pre => Valid (Cfg);

   --  A configuration the prover handles for S.
   function Config_Fits (Cfg : Config; S : Shape) return Boolean is
     (Valid (Cfg) and then LPR.Prover_Fits (Geometry_Of (Cfg, S)));

   --  The subfield boundary within the witness vector: the circuit's,
   --  less the public inputs (saturating), as ZkProver::commit.
   function Boundary_Of (S : Shape; Sfb : Natural) return Natural is
     (if Sfb > S.Npublic then Sfb - S.Npublic else 0);

   --  The bytes a proof of C may take under Cfg: the writer's length
   --  with the longest opening.
   function Max_Proof_Len
     (Cfg : Config; S : Shape; Sfb : Natural) return Natural
   is
     (PW.Proof_Len (S, Geometry_Of (Cfg, S), Boundary_Of (S, Sfb),
                    2 * Num_Leaves (Geometry_Of (Cfg, S))))
   with Pre => Config_Fits (Cfg, S);

   --  The two phases of ZkProver (commit, prove) for a transcript the
   --  caller opened (ADR 0085). Commit takes the private inputs: it
   --  checks their count and the subfield, draws the pads, forms the
   --  witness vector, builds the Ligero commitment and writes its root
   --  to the transcript as it is. Prove_Committed takes the public
   --  inputs, which a flow may know only after the commitment (the mDoc
   --  layer of ADR 0058 draws a value from the transcript after both
   --  commitments and puts it in the public inputs): it evaluates the
   --  circuit on the two together, checks the satisfiability, writes the
   --  statement, runs the sumcheck, the core and the Ligero proof, and
   --  writes the bytes. Between the phases Committed holds the
   --  commitment and the working set on the heap under the ownership
   --  rules of ADR 0047, freed by Prove_Committed or by Release. Prove
   --  below is the two phases on a fresh transcript for one proof.
   type Committed is private;

   --  Nothing held: after Commit failed, Prove_Committed, or Release.
   function Is_Null (C : Committed) return Boolean with Global => null;

   --  The record holds a commitment for a circuit of the shape of P
   --  under Cfg and Sfb: the precondition of Prove_Committed, the
   --  postcondition of a Commit that succeeded. The commitment depends
   --  on the circuit through its shape only (the sizes, the layers'
   --  widths), as the reference's does.
   function Fits
     (C : Committed; Sfb : Natural; Cfg : Config; P : Packed_Circuit)
      return Boolean
   with
     Global => null,
     Pre    => PH.PC.Indices_Ok (P) and then PH.PC.Layers_Ok (P)
               and then LPR.LV.ST.SA.Shape_Ok (PH.PC.Shape_Of (P))
               and then Config_Fits (Cfg, Shape_Of (P));

   procedure Release (C : in out Committed) with
     Global => null,
     Post   => Is_Null (C);

   --  Priv is the private inputs, ninput - npublic of them
   --  (Input_Length otherwise). Not_In_Subfield and Config_Invalid as
   --  Prove. The root goes to the transcript on Ok.
   procedure Commit
     (Sfb  : Natural;
      Cfg  : Config;
      P    : Packed_Circuit;
      Priv : Element_Array;
      C    : out Committed;
      St   : out Status)
   with
     Always_Terminates => False,
     Pre               =>
       (Runtime    =>
          PH.PC.Indices_Ok (P) and then PH.PC.Layers_Ok (P)
          and then LPR.LV.ST.SA.Shape_Ok (PH.PC.Shape_Of (P))
          and then Config_Fits (Cfg, Shape_Of (P)) and then P.Ninput >= 1
          and then Priv'First = 0,
        Proof_Only =>
          PH.PC.Valid (P)
          and then LPR.LV.ST.SA.Well_Formed (PH.PC.Expand (P))),
     Post              =>
       St in Ok | Input_Length | Not_In_Subfield | Config_Invalid
       and then (St = Input_Length)
                = (Priv'Length /= P.Ninput - P.Npublic)
       and then (if St = Ok then Fits (C, Sfb, Cfg, P) else Is_Null (C));

   --  Pub is the public inputs, npublic of them (Input_Length
   --  otherwise), the first 1 (Input_Not_One, ADR 0064); Not_Satisfied
   --  when the circuit does not accept Pub with the private inputs of
   --  the commitment; Exhausted as Prove. B (0 .. Len - 1) holds the
   --  proof string when St is Ok; otherwise Len is 0 and B is zero. C
   --  is freed on every path.
   procedure Prove_Committed
     (Id  : Bytes_32;
      Sfb : Natural;
      Cfg : Config;
      P   : Packed_Circuit;
      Pub : Element_Array;
      C   : in out Committed;
      B   : out Byte_Array;
      Len : out Natural;
      St  : out Status)
   with
     Always_Terminates => False,
     Pre               =>
       (Runtime    =>
          PH.PC.Indices_Ok (P) and then PH.PC.Layers_Ok (P)
          and then LPR.LV.ST.SA.Shape_Ok (PH.PC.Shape_Of (P))
          and then Config_Fits (Cfg, Shape_Of (P)) and then P.Ninput >= 1
          and then Fits (C, Sfb, Cfg, P)
          and then Pub'First = 0
          and then B'First = 0
          and then B'Length = Max_Proof_Len (Cfg, Shape_Of (P), Sfb),
        Proof_Only =>
          PH.PC.Valid (P)
          and then LPR.LV.ST.SA.Well_Formed (PH.PC.Expand (P))),
     Post              =>
       Is_Null (C)
       and then St in Ok | Input_Length | Input_Not_One | Not_Satisfied
                      | Exhausted
       and then (if St = Ok then Len in 1 .. B'Length else Len = 0)
       and then (St = Input_Length) = (Pub'Length /= P.Npublic)
       and then (St = Input_Not_One)
                = (Pub'Length = P.Npublic and then P.Npublic > 0
                   and then Pub (0) /= LPR.LV.ST.SA.One);

   --  The proof of the packed circuit P on Inputs under Label and Cfg,
   --  Id the circuit identifier and Sfb the subfield boundary of the
   --  circuit file: B (0 .. Len - 1) holds the proof string when St is
   --  Ok; otherwise Len is 0 and B is zero. The circuit is asked, at
   --  level Proof_Only, what the loader proves of it: a valid form
   --  whose expansion is well formed. The global state is synthesised:
   --  the transcript and the state of the randomness source behind SPR
   --  and LPR, which the generic cannot name. The body is the two
   --  checks on the count and the first input, Reset with the label,
   --  Commit on the private inputs, Prove_Committed on the public ones.
   procedure Prove
     (Label  : Byte_Array;
      Id     : Bytes_32;
      Sfb    : Natural;
      Cfg    : Config;
      P      : Packed_Circuit;
      Inputs : Element_Array;
      B      : out Byte_Array;
      Len    : out Natural;
      St     : out Status)
   with
     Always_Terminates => False,
     Pre               =>
       (Runtime    =>
          Label'Length <= Transcript.Max_Payload
          and then PH.PC.Indices_Ok (P) and then PH.PC.Layers_Ok (P)
          and then LPR.LV.ST.SA.Shape_Ok (PH.PC.Shape_Of (P))
          and then Config_Fits (Cfg, Shape_Of (P)) and then P.Ninput >= 1
          and then Inputs'First = 0
          and then B'First = 0
          and then B'Length = Max_Proof_Len (Cfg, Shape_Of (P), Sfb),
        Proof_Only =>
          PH.PC.Valid (P)
          and then LPR.LV.ST.SA.Well_Formed (PH.PC.Expand (P))),
     Post              =>
       (if St = Ok then Len in 1 .. B'Length else Len = 0)
       and then (St = Input_Length) = (Inputs'Length /= P.Ninput)
       and then (St = Input_Not_One)
                = (Inputs'Length = P.Ninput and then P.Npublic > 0
                   and then Inputs (0) /= LPR.LV.ST.SA.One);

private

   -------------------------------------------------------------------
   --  The working set (ADR 0047): the pads, the witness vector, the
   --  triples, the sumcheck proof and its challenges, the constraints,
   --  the Ligero proof, each sized by the circuit or the geometry
   --  through a discriminant. Here rather than in the body so that
   --  Committed can hold it between the two phases.
   -------------------------------------------------------------------

   subtype Index is LPR.LV.Index;

   type Work
     (Pads_Last, Wv_Last, Lqc_Last             : Index;
      Proof_Last, Chal_Last, Terms_Max, B_Last : Index;
      Ldt_Last, Linear_Last, Low_Last, High_Last, Nonce_Last, Col_Last : Index;
      Path_Last : Merkle.Node_Index)
   is record
      Pads   : Element_Array (0 .. Pads_Last);
      Wv     : Element_Array (0 .. Wv_Last);
      Lqc    : LPR.LV.ST.SV.Lqc_Array (0 .. Lqc_Last);
      Lqc2   : LPR.LV.ST.SV.Lqc_Array (0 .. Lqc_Last);
      BQ     : Element_Array (0 .. Lqc_Last);
      SProof : LPR.LV.ST.SV.Sumcheck_Proof (Last => Proof_Last);
      Ch     : LPR.LV.ST.SV.Challenges (Last => Chal_Last);
      A      : LPR.LV.ST.SV.Ligero_Terms (Max => Terms_Max);
      Bv     : Element_Array (0 .. B_Last);
      Lig    : LPR.LV.LP.Proof (Ldt_Last, Linear_Last, Low_Last, High_Last,
                                Nonce_Last, Col_Last, Path_Last);
   end record;

   type Work_Access is access Work;

   --  The discriminants of Wk are those of S under G.
   function Work_Shape
     (Wk : Work; S : Shape; G : Valid_Geometry) return Boolean
   is
     (Wk.Pads_Last + 1 = SPR.Pad_Total (S)
      and then Wk.Wv_Last + 1 = Witness_Count (S)
      and then Wk.Lqc_Last = S.Last_Layer
      and then Wk.Proof_Last + 1 = LPR.LV.ST.SV.Proof_Total (S)
      and then Wk.Chal_Last + 1 = LPR.LV.ST.SV.Chal_Total (S)
      and then Wk.Terms_Max = LPR.LV.ST.SV.A_Bound (S)
      and then Wk.B_Last = S.Last_Layer + 1
      and then Wk.Ldt_Last + 1 = G.Block_Len
      and then Wk.Linear_Last + 1 = G.Dblock_Len
      and then Wk.Low_Last + 1 = G.Num_Queries
      and then Wk.High_Last + 1 = G.Dblock_Len - G.Block_Len
      and then Wk.Nonce_Last + 1 = G.Num_Queries
      and then Wk.Col_Last + 1 = LPR.LV.LP.Opened (G)
      and then Wk.Path_Last + 1 = 2 * Num_Leaves (G))
   with Global => null, Pre => LPR.Prover_Fits (G);

   type Shape_Access is access Shape;

   --  The commitment and the working set; the shape of the circuit the
   --  commitment was made for, layer by layer, which Prove_Committed
   --  requires of its circuit (the pads and the triples are laid out by
   --  it); and the subfield boundary within the witness vector the
   --  commitment was made with.
   type Committed is record
      Wk    : Work_Access;
      Com   : LPR.Commitment_Access;
      S     : Shape_Access;
      Sfb_W : Natural;
   end record;

   function Is_Null (C : Committed) return Boolean is
     (C.Wk = null and then C.Com = null and then C.S = null);

   function Fits
     (C : Committed; Sfb : Natural; Cfg : Config; P : Packed_Circuit)
      return Boolean
   is
     (C.Wk /= null and then C.Com /= null and then C.S /= null
      and then C.S.all = Shape_Of (P)
      and then C.Sfb_W = Boundary_Of (Shape_Of (P), Sfb)
      and then Work_Shape (C.Wk.all, Shape_Of (P),
                           Geometry_Of (Cfg, Shape_Of (P)))
      and then LPR.Com_Shape (C.Com.all, Geometry_Of (Cfg, Shape_Of (P))));

end Zk_Prover;
