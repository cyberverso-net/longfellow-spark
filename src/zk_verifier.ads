--  Zk_Verifier: the complete verifier of Longfellow ZK, ZkVerifier::verify
--  of the reference (docs/specs/rust/src/zk/verifier.rs at d5e6be7) and
--  the reader of a complete proof string of draft Section 7.5
--  (read_zk_proof of zk/proof.rs). Generic over the Ligero verifier of a
--  field, which carries the transcript glue, the proof record and the
--  tables of the same field.
--
--  A proof string is the Merkle root (32 bytes), the sumcheck part
--  (Section 7.3, read by the stage 4 reader) and the Ligero part
--  (Section 7.4), with no trailing bytes. Verify checks the public
--  input count, reads the string, replays the transcript of stage 4
--  (label, root, statement, the challenges of the core), runs the
--  symbolic core of stage 3 for the constraints A, b and the quadratic
--  triples, and hands them with the number of witnesses (Witness_Count
--  of the core) to the Ligero verifier under the fixed statement hash
--  of the reference, DEFAULT_STATEMENT_HASH (ADR 0035: everything
--  statement-specific is already in the transcript).
--
--  Documentation: docs/guide/05-ligero.md. Decisions: ADR 0035 (scope,
--  the statement hash), 0039 (sizes, the status), 0028 (the replay);
--  frame: ADR 0022, 0024. Index: docs/adr/README.md.
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
--  Soundness is the paper's theorem, out of scope.
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

with Bytes;            use Bytes;
with Transcript;
with Ligero_Geometry;  use Ligero_Geometry;
with Verifier_Status;  use Verifier_Status;
with Ligero_Verifier;

generic
   with package LV is new Ligero_Verifier (<>);
package Zk_Verifier is

   subtype Element is LV.ST.SA.Element;
   subtype Element_Array is LV.ST.SA.Element_Array;
   subtype Circuit is LV.ST.SA.Circuit;
   subtype Shape is LV.ST.SA.Shape;

   --  The shape of the circuit, for the sizes (Sumcheck_Algebra).
   function Shape_Of (C : Circuit) return Shape is (LV.ST.SA.Shape_Of (C))
   with Global => null;
   subtype Sumcheck_Proof is LV.ST.SV.Sumcheck_Proof;
   subtype Ligero_Part is LV.LP.Proof;

   use type LV.ST.SA.Element;

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

   --  ZkVerifier::verify: Label the transcript label, Id the circuit
   --  identifier of the statement (Section 3.3), Cfg the Ligero
   --  configuration, C the circuit, Pub the public inputs, B the proof
   --  string. Proof_Encoding also when the geometry's opened columns
   --  do not fit this implementation (ADR 0039).
   procedure Verify
     (Label : Byte_Array;
      Id    : Bytes_32;
      Cfg   : Config;
      C     : Circuit;
      Pub   : Element_Array;
      B     : Byte_Array;
      St    : out Status)
   with
     Global            => (In_Out => (Transcript.State, Transcript.Absorbed)),
     Always_Terminates => False,
     Pre               =>
       Label'Length <= Transcript.Max_Payload
       and then Valid (Cfg)
       and then Pub'First = 0
       and then B'First = 0,
     Post              =>
       St not in Queried_Columns_Length | Polynomial_Lengths
       and then (St = Public_Input_Length) = (Pub'Length /= C.Npublic)
       and then (St = Public_Input_Not_One)
                = (Pub'Length = C.Npublic and then C.Npublic > 0
                   and then Pub (0) /= LV.ST.SA.One);

end Zk_Verifier;
