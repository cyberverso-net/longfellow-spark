# Verification approach

This document explains what formal verification with SPARK buys for a zero-knowledge proof system, what it cannot buy, and how the gap is covered. It is the key to reading every package header and every entry of the [trust model](trust-model.md).

## The system in one paragraph

Longfellow ZK proves statements about signed credentials (an mDoc with an ECDSA signature over P-256) without revealing them. The statement is expressed as an arithmetic circuit; the prover convinces the verifier that it knows a satisfying assignment by running the sumcheck protocol over the large binary field GF(2^128), where soundness follows from the Schwartz-Zippel lemma, and by committing to its intermediate values with a Ligero-style commitment: Reed-Solomon encodings of the witness, hashed into a Merkle tree, spot-checked by the verifier on randomly chosen columns. The interactive protocol is made non-interactive with Fiat-Shamir: every verifier challenge is derived by hashing the transcript so far. Characteristic 2 suits the Boolean-heavy circuits (SHA-256, CBOR parsing): addition is xor, squaring is linear, inversion is a fixed exponentiation. The ECDSA part needs prime-field arithmetic over the P-256 base field, with multi-limb integers and carries.

## What a SPARK proof is

SPARK is a subset of Ada with a verification toolset, GNATprove. The programmer writes contracts (preconditions, postconditions, loop invariants) and GNATprove turns the program and its contracts into verification conditions (VCs), logical statements that are handed to SMT solvers. A VC that is proved holds for every execution of the subprogram, for every input in the declared types: it is a universal statement, not a test on samples. A VC that is not proved is reported with its location and kind, and the programmer either strengthens the contracts, restructures the code, or supplies a lemma.

The project uses the assurance levels of the SPARK community: Silver means that every possible run-time error (overflow, index out of range, division by zero, uninitialised read) is proved absent; Gold means that in addition the declared functional contracts are proved. Platinum, full functional correctness of the whole system, is explicitly not a goal ([ADR 0003](../adr/0003-proof-policy-and-trust-model.md)).

## What the proofs establish, and why it matters here

**Absence of run-time errors, everywhere.** Proofs and circuits are attacker-controlled input by definition. A verifier that can be crashed, or made to read out of bounds, by a crafted proof is a vulnerability regardless of the cryptography. Silver on every line removes this class entirely, with no reliance on fuzzing coverage.

**Functional correctness of field arithmetic against a reference.** A reduction bug in GF(2^128) multiplication does not crash; it silently produces a different field element, the sumcheck equations no longer mean what Schwartz-Zippel assumes, and soundness is lost without any observable failure. This is the highest value per proved line in the project. The pattern is a *ghost reference*: a second implementation, written for clarity rather than speed, marked `Ghost` so it is never compiled into the product, and used as the specification. The postcondition of the real implementation says "my result equals the reference's result". GNATprove proves that for every pair of inputs. Stage 1 does this for multiplication and squaring ([ADR 0005](../adr/0005-mul-ref-as-proof-target.md)); the P-256 stage will relate a multi-limb representation to the integer it denotes, which is where hand-written lemmas are expected.

**Structural properties of the verifier.** The circuit evaluator has a proved contract that defines what "the circuit accepts" means (chapter 3); the Merkle batch verification is proved against its path discipline and node model, the geometry against its constraints, the Reed-Solomon tables and the three Ligero tests against ghost references that transcribe the reference's formulas, and the verifier core emits only terms the Ligero verifier can index (chapter 5). In Phase B the circuit loader will accept only well-formed circuits (gate arity, wire indices in range, topological order). Everything else in the verifier appeals to these.

## What the proofs cannot establish, and what covers it instead

**The reference matches the specification.** The proof says Mul = Mul_Ref. It says nothing about whether Mul_Ref is the multiplication the draft intends: the same wrong polynomial or bit order in both would prove fine. This gap is closed by known-answer vectors anchored on constants produced outside this repository ([ADR 0009](../adr/0009-known-answer-vectors.md)).

**Inverse correctness.** That E * Inv (E) = 1 follows from Fermat's little theorem, which SMT solvers cannot derive. Inv is Silver, and the property is tested on vectors with two independent references ([ADR 0008](../adr/0008-inv-fixed-chain-total-function.md)). On the verification path the question does not arise: every inverse the Ligero verifier uses is multiplied back and checked at run time, with a status when the check fails ([ADR 0037](../adr/0037-checked-inv-and-public-data-scope.md)).

**Soundness and zero knowledge.** These are probabilistic properties of the protocol, not contracts of a subprogram. No SPARK proof touches them. The compensating control is fidelity to the pinned specification, every step citing its section, so that the implementation is an instance of the analysed protocol and not a variant ([ADR 0002](../adr/0002-pin-the-specification.md)).

**Fiat-Shamir transcript completeness.** If one public element is omitted from the hash that derives a challenge, the prover can choose that element after seeing the challenge and forge proofs (the "Frozen Heart" class of vulnerabilities). The code that omits it is perfectly well-typed and proves fine. The control is the absorption checklist of ADR 0028, written as the sequence of calls of the replay and of the Ligero verifier, compared with the reference by reading and tested on the published proofs (chapters 4 and 5).

**Constant-time execution.** SPARK reasons about values, not about time. Constant time is a coding discipline: no secret-dependent branches or indexing, masks instead of conditionals, fixed operation sequences. The guarantee holds only for builds with assertions disabled, because contracts and ghost code execute when assertions are on and the ghost reference branches on its operand ([ADR 0006](../adr/0006-constant-time-discipline-and-scope.md)).

**Interoperability.** That proofs produced by the upstream prover verify here, and vice versa, is tested on vectors and real proofs, never proved.

**The toolchain.** The GNAT compiler, GNATprove and the SMT solvers are trusted. So is the pinned specification. These are listed, not hidden.

## The ghost reference pattern, in practice

A ghost function is ordinary Ada code with the aspect `Ghost`: it may be called from contracts and from other ghost code, it is checked by GNATprove like any other code, and it is removed from the executable when assertions are disabled. Writing the reference as an *expression function* (a function whose body is a single expression) lets GNATprove unfold it in proofs. A recursive reference needs a `Subprogram_Variant` to prove termination.

The implementation then mirrors the reference step by step, and the *loop invariant* states, after each iteration, exactly what the reference computes for that many steps. GNATprove reasons about a loop by induction and cannot invent the inductive hypothesis: the invariant must hold on entry (base case), be preserved by one iteration (step), and at exit imply the postcondition. When a proof fails, GNATprove says which of these failed, and that localises the bug: a base-case failure is usually an initialisation mismatch, a preservation failure usually means the invariant is too weak (the solver does not know enough inside the loop) or too strong (false).

## Reading a package header

Every package header states, subprogram by subprogram, its level (Silver or Gold), what the postcondition is proved against, which vectors anchor what the proof does not cover, the specification sections implemented, the decision records applied, and the scope of the constant-time claim. The [trust model](trust-model.md) gathers these into one list, where every claim is proved, tested or trusted. If a header and this document disagree, the header is wrong and should be fixed, not the other way round.

## Circuits as data

The circuit compiler (SHA-256, ECDSA, CBOR parsing into circuits) is the largest part of the upstream code and the least security-critical. The project consumes upstream-generated circuits as validated data and reimplements the compiler last, so a verified verifier is reachable early ([ADR 0011](../adr/0011-circuits-as-data.md)). Until then the circuit files are a declared trusted input.
