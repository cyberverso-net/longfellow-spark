--  Zk_Prover: the composition of zk/prover.rs (Phase C, ADR 0049,
--  0050, 0051): ZkProver::commit and ZkProver::prove of the reference
--  (docs/specs/rust/src/zk/prover.rs at d5e6be7) in one procedure,
--  from the circuit and its inputs to the proof string of Section 7.5.
--  Generic over the Ligero prover of a field (which carries the
--  verifier units, the sampling instance and the randomness source),
--  the sumcheck prover over the same transcript glue and the writers.
--
--  Prove validates first (ADR 0049): the inputs are ninput elements
--  (Input_Length); the first is 1 when the circuit has public inputs
--  (Input_Not_One, OneWire of ADR 0064); they satisfy the circuit
--  (Not_Satisfied, from Eval_Circuit of stage 3: every output of layer
--  0 zero and every Z assertion met); and the witnesses the writer will
--  project on the subfield lie in it (Not_In_Subfield): those of the
--  witness rows wholly below the subfield boundary
--  (Proof_Writer.Sub_Rows, the rows the reference writer projects and
--  where its prover would panic), which must all be private inputs (a
--  pad there is a full-field element) and each of which is projected
--  with the fixed map of ADR 0051, re-injected and compared, the
--  differences accumulated in one mask; nothing is projected when the
--  field is its own subfield (P-256). The last two checks are skipped
--  when the generic formal Validate is False, which only the test
--  project does. Then, in the reference's order: the pads
--  (Sample_Pads), the witness vector (the private inputs, then the
--  pads), the quadratic triples (Lqc_Triples), the Ligero commitment
--  (Commit; Config_Invalid when a Lagrange denominator has no inverse),
--  the transcript (the label, the root, the statement), the sumcheck
--  proof on the live transcript with its challenges recorded
--  (Sumcheck_Prover.Prove), the verifier core on those challenges for
--  the constraints (ADR 0022, 0049), the Ligero proof under the fixed
--  statement hash of zk/ common.rs (Exhausted when the generator passes
--  its bound), and the bytes (Write_Proof). Memory: the wires, the
--  pads, the witness vector, the proofs and the constraints live on the
--  heap (ADR 0047).
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
--  each a fixed loop accumulating a mask and one branch on the result,
--  the prover's own decision whether to produce a proof. The rest is
--  constant time by construction in the units it calls. The guarantee
--  is scoped to builds with assertions disabled (ADR 0006).

pragma SPARK_Mode (On);

with Bytes;            use Bytes;
with Transcript;
with Prover_Status;    use Prover_Status;
with Ligero_Geometry;  use Ligero_Geometry;
with Ligero_Prover;
with Sumcheck_Prover;
with Proof_Writer;

generic
   with package LPR is new Ligero_Prover (<>);
   with package SPR is new Sumcheck_Prover (ST => LPR.LV.ST, others => <>);
   with package PW  is new Proof_Writer (LV => LPR.LV);
   --  Validate: the satisfiability and subfield checks run (every
   --  instance of the library and of the command-line prover). False
   --  exists for the test project only (ADR 0053): a prover that proves
   --  false inputs, whose proof the verifier must refuse.
   Validate : Boolean := True;
package Zk_Prover is

   --  As in the body (ADR 0072): the predicate of Circuit is checked
   --  once where a circuit enters the program, and the expression
   --  functions below, which the command line calls with the circuit,
   --  do not walk it again. GNATprove proves these checks as before.
   pragma Suppress (Predicate_Check);

   subtype Element is LPR.LV.ST.SA.Element;
   subtype Element_Array is LPR.LV.ST.SA.Element_Array;
   subtype Circuit is LPR.LV.ST.SA.Circuit;

   use type LPR.LV.ST.SA.Element;

   --  The statement hash the reference passes to Ligero, fixed for
   --  backward compatibility (DEFAULT_STATEMENT_HASH of zk/common.rs);
   --  the statement itself is in the transcript already.
   Default_Statement_Hash : constant Bytes_32 :=
     [16#de#, 16#ad#, 16#be#, 16#ef#, others => 0];

   function Witness_Count (C : Circuit) return Natural
     renames LPR.LV.ST.SV.Witness_Count;

   --  The geometry of a proof of C under Cfg (as the verifier's).
   function Geometry_Of (Cfg : Config; C : Circuit) return Valid_Geometry is
     (Make (Cfg, Witness_Count (C), C.Last_Layer + 1))
   with Pre => Valid (Cfg);

   --  A configuration the prover handles for C.
   function Config_Fits (Cfg : Config; C : Circuit) return Boolean is
     (Valid (Cfg) and then LPR.Prover_Fits (Geometry_Of (Cfg, C)));

   --  The subfield boundary within the witness vector: the circuit's,
   --  less the public inputs (saturating), as ZkProver::commit.
   function Boundary_Of (C : Circuit; Sfb : Natural) return Natural is
     (if Sfb > C.Npublic then Sfb - C.Npublic else 0);

   --  The bytes a proof of C may take under Cfg: the writer's length
   --  with the longest opening.
   function Max_Proof_Len
     (Cfg : Config; C : Circuit; Sfb : Natural) return Natural
   is
     (PW.Proof_Len (C, Geometry_Of (Cfg, C), Boundary_Of (C, Sfb),
                    2 * Num_Leaves (Geometry_Of (Cfg, C))))
   with Pre => Config_Fits (Cfg, C);

   --  The proof of C on Inputs under Label and Cfg, Id the circuit
   --  identifier and Sfb the subfield boundary of the circuit file:
   --  B (0 .. Len - 1) holds the proof string when St is Ok; otherwise
   --  Len is 0 and B is zero. The global state is synthesised: the
   --  transcript and the state of the randomness source behind SPR and
   --  LPR, which the generic cannot name.
   procedure Prove
     (Label  : Byte_Array;
      Id     : Bytes_32;
      Sfb    : Natural;
      Cfg    : Config;
      C      : Circuit;
      Inputs : Element_Array;
      B      : out Byte_Array;
      Len    : out Natural;
      St     : out Status)
   with
     Always_Terminates => False,
     Pre               =>
       Label'Length <= Transcript.Max_Payload
       and then Config_Fits (Cfg, C) and then C.Ninput >= 1
       and then Inputs'First = 0
       and then B'First = 0 and then B'Length = Max_Proof_Len (Cfg, C, Sfb),
     Post              =>
       (if St = Ok then Len in 1 .. B'Length else Len = 0)
       and then (St = Input_Length) = (Inputs'Length /= C.Ninput)
       and then (St = Input_Not_One)
                = (Inputs'Length = C.Ninput and then C.Npublic > 0
                   and then Inputs (0) /= LPR.LV.ST.SA.One);

end Zk_Prover;
