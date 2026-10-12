# Chapter 3: the sumcheck algebra and the symbolic verifier core

Stage 3 of Phase A. Three generic packages over a field, each instantiated for GF(2^128) and for the P-256 base field: `Sumcheck_Algebra` (the array vocabulary and circuit evaluation of draft Sections 6.1 to 6.4), `Sumcheck_Expression` (sparse affine expressions over the witness, Section 6.7) and `Sumcheck_Verifier` (the symbolic verifier core, Section 6.7). Decisions: [ADR 0022](../adr/0022-stage-3-scope-and-challenges-as-input.md) to [ADR 0027](../adr/0027-sumcheck-vectors-and-upstream-instrumentation.md). This chapter follows the shape of the first two: the mathematics, the algorithms, the Ada/SPARK implementation for a reader new to SPARK, then what is proved, what is tested and what stays trusted, with the verification condition table.

## 1. The mathematics

### 1.1 Layered circuits and the quad representation

A circuit has NL layers (Section 6.3.1). Layer j computes the wires V[j] from the wires V[j + 1]; V[0] are the outputs and V[NL] the inputs. The statement "the circuit accepts" means every output wire is 0. Each layer is a *quad* Q[j], a sparse three-dimensional array (Section 6.3.2):

    V[j][g] = SUM_{l, r} Q[j][g, l, r] V[j + 1][l] V[j + 1][r]

so every wire is a quadratic form of the previous layer's wires. The layer also carries *Z assertions* (Section 6.3.3): terms with coefficient 0, which state that a product of two input wires is zero. In the data this is one list of 4-tuples (g, h0, h1, k) per layer: k /= 0 is Q[g, h1, h0] = k; k = 0 asserts w[h1] w[h0] = 0.

The reference and the draft use `NW` differently (ADR 0022): for layer j this chapter writes nw_in (j) for the number of input wires (the reference's `layers[j].nw`, the draft's NW[j + 1]) and nw_out (j) for the number of output wires (nw_in (j - 1), or noutput for j = 0); logw (j) is the number of bits of an input wire index, hence of sumcheck rounds.

### 1.2 Multilinear extensions, bind and the EQ array

Sumcheck arrays are padded with zeroes to infinity (Section 6.1). Binding an array to a field element x halves it:

    bind (A, x)[i] = (1 - x) A[2 i] + x A[2 i + 1]

and binding to a vector of challenges X applies bind once per coordinate. The array EQ_n[i, j] is 1 when i = j < n and 0 otherwise (Section 6.2); its binding to X is what lets a verifier evaluate a bound array as a dot product, bindv (V, X) = SUM_j bindv (EQ, X)[j] V[j], which is the shape a commitment scheme with linear constraints can check. Two closed forms are used: `eq (r, x, nbits)`, the product over the bits b of x of r[b] when the bit is 1 and 1 - r[b] otherwise, and `bindeq (c)`, the whole array by the recursive definition b[2 i] = (1 - c0) a[i], b[2 i + 1] = c0 a[i] with a = bindeq (c[1 ..]). That the two agree, bindeq (c)[i] = eq (c, i, n), is a theorem; here it is tested, not proved (Section 4 below).

### 1.3 The sumcheck protocol in one layer

At layer j both parties hold two claims, bind (V[j], G0) and bind (V[j], G1), combined with a challenge alpha into one (Section 6.6). The quad of the layer with its outputs bound (`bind_g`, the coefficient of each term becomes k eq2 (g), or beta eq2 (g) for a Z term) turns the claim into a sum over the 2 logw bits of the two input wire indices l and r. Each round binds one bit of one hand with a fresh challenge: the prover sends a degree-two polynomial, the verifier evaluates it at the challenge and that becomes the new claim. After 2 logw rounds the sum has collapsed to a single term: the fully bound quad (`eval_bound_quad`, a field element the verifier computes alone) times the two new claims bind (V[j + 1], G'0) and bind (V[j + 1], G'1), which the prover sends and the next layer inherits.

### 1.4 Degree-two polynomials by three evaluations; the Lagrange basis

Polynomials are degree two and are kept as evaluations at P0 = 0, P1 = 1 and P2 (Section 6.4): 2 in odd characteristic, inj (2) = beta_1 on GF(2^128) ([ADR 0025](../adr/0025-polynomials-and-lagrange-constants.md)). Since p (0) + p (1) is the claim of the round, the prover sends p (0) and p (P2) and the verifier recovers p (1). The value at a challenge r is p (r) = p (0) l0 (r) + p (1) l1 (r) + p (2) l2 (r) with the Lagrange basis

    l0 = (r - 1)(r - P2) / d0,   l1 = r (r - P2) / d1,   l2 = r (r - 1) / d2

and d0 = (0 - 1)(0 - P2), d1 = (1 - 0)(1 - P2), d2 = (P2 - 0)(P2 - 1). The inverses of the three denominators are per-field constants (on GF(2^128), where subtraction is addition, d0 = P2, d1 = 1 + P2, d2 = P2 (1 + P2); on P-256, 1/2, -1, 1/2), computed by the vector generator and re-checked by the harness with the library's multiplication; `Inv` is never called by the verifier.

### 1.5 One-time pads and deferred verification: why the verifier emits constraints

Every element the prover would send, p (0), p (P2) and the two claims of each layer, is sent *padded*: minus a random pad value that is part of the committed witness (Section 6.5). The verifier therefore never knows the real polynomials. It replays the protocol on *symbolic* values, affine expressions k + SUM a[i] Var (i) over the witness variables, and at the end of each layer it has an expression that must be zero: a linear constraint for the Ligero layer. The product of the two claim pads is a third pad variable cr with a quadratic constraint W[c0] W[c1] = W[cr]. The output of the core is thus not accept or reject but the constraint system (A, b) and the quadratic triples (Section 6.7); the Ligero verifier of phase B checks them against the commitment ([ADR 0022](../adr/0022-stage-3-scope-and-challenges-as-input.md)).

### 1.6 The combined witness and its layout

Witness variables are numbered from 0: first the ninput - npublic private inputs, then the pads, layer by layer from layer 0, within a layer 4 logw round pads (round r, hand h: the pad of p (0) at 4 r + 2 h and of p (P2) at 4 r + 2 h + 1) followed by c0, c1 and cr (Section 6.5, `LayerPad::generate_indices`). The pad block of layer j starts at Pad_Off (j) = ninput - npublic + SUM_{i < j} (4 logw (i) + 3). The quadratic triple of layer j is (Pad_Off (j) + 4 logw (j), + 1, + 2).

## 2. The algorithms

### 2.1 eq, eq2, bindeq, bind

`eq` is a product over the bits of x, least significant first, starting from One. `eq2 (x, n, g0, g1, alpha) = eq (g0, x, n) + alpha eq (g1, x, n)`. `bindeq` expands in place from the last challenge to the first, doubling the array at each step, highest index first so that nothing is overwritten before it is read. `bind` applies the formula of Section 6.1 with zero padding beyond the end of the array.

### 2.2 eval_quad and eval_circuit, with the Z assertions

`eval_quad` walks the term list in order: a term with k = 0 checks w[h1] w[h0] = 0; any other term adds k w[h1] w[h0], in that association, to output wire g. `eval_circuit` runs the layers from the input layer to layer 0, keeping every layer's wires, and reports success when every Z assertion held and every output wire is zero. Nothing is raised: success is a Boolean ([ADR 0022](../adr/0022-stage-3-scope-and-challenges-as-input.md), D6).

### 2.3 bind_g and eval_bound_quad

`bind_g` replaces the coefficient of every term by k eq2 (g) (beta eq2 (g) for a Z term) and sets g to 0: the quad with its outputs bound. `eval_bound_quad` is the value of that bound quad at the two hands' challenges, SUM over terms of bound_k eq (hc0, h0, logw) eq (hc1, h1, logw), in list order.

### 2.4 The symbolic round and verify_layer

A symbolic round (Section 6.7, `symbolic_sumcheck_round`) builds p0 = Var (pad0) + hp0 and p2 = Var (pad1) + hp2 from the padded evaluations and their pad variables, deduces p1 = claim - p0, and returns next = p0 l0 + p1 l1 + p2 l2 with the basis at the round's challenge. `verify_layer` combines the two claims with alpha, runs the 2 logw rounds (round outer, hand inner), computes the bound quad eqq, forms prod = (Var (c0) cl1 + Var (c1) cl0 + Var (cr) + cl0 cl1) eqq from the padded claims cl0, cl1, subtracts it from the claim, emits "claim = 0" as a linear constraint, and hands the next layer the claims Var (c0) + cl0 and Var (c1) + cl1 with the two hands' challenge vectors.

### 2.5 The input constraint and the quadratic triples

After the last layer the two claims are combined with alpha_input and compared with the multilinear extension of the inputs at the final binding: eq2 (i) for every input i, the public inputs folded into the constant term, one variable per private input. The difference is the last linear constraint. The quadratic triples are the (c0, c1, cr) of every layer (`generate_lqc_triples`).

## 3. The Ada/SPARK implementation

### 3.1 A field as a signature package; the two instantiations

`Field_Signature` is a *signature package*: a generic whose formal part lists what the protocol needs from a field (the private type `Element`, the constants `Zero`, `One`, `P2`, the operations `"+"`, `"-"`, `"*"`, `Neg`, the three Lagrange denominator inverses and the ghost logical equality `Same`) and whose body is empty. `Field_GF2_128` and `Field_P256` instantiate it as `Sig`, naming the operations of the two field packages and holding the constants of ADR 0025. Protocol packages take `with package F is new Field_Signature (<>)` as a *formal package parameter*: one parameter stands for the whole bundle. GNATprove analyses the instances, not the generics ([ADR 0024](../adr/0024-field-genericity-by-formal-package.md)), so every proof below is made twice, once per field, and `make prove` counts both.

Inside the generic the operations are reached through wrappers `"+"`, `"-"`, `"*"`, `Neg` with `Global => null` and no postcondition. This is deliberate: the contracts of the concrete field never enter a protocol proof, and the verification conditions are the same for both instances. `Same` is explained in Section 4.

### 3.2 Circuits as data: Term, Layer, Circuit and their predicates

A `Term` is (K, G, H0, H1) with the wire indices bounded by `Max_Wires`. A `Raw_Circuit (Last_Layer, NT)` is a *discriminated record*: its discriminants size the arrays inside it (`Layers (0 .. Last_Layer)`, `Terms (1 .. NT)`), so a circuit of any size is one object with no pointers. Each `Layer` owns a contiguous range of the flat term list. `Circuit` is a subtype of `Raw_Circuit` with the *type predicate* `Well_Formed`: the layers partition the term list, every term names wires in range (g < nw_out, h < nw_in), nw_in fits in logw bits and the last layer reads exactly the inputs. The predicate lives on a subtype rather than on the record itself because its function takes the record as argument; every subprogram taking a `Circuit` may assume it, and the harness checks it when it builds a circuit from a vector file.

### 3.3 Sumcheck_Algebra: the generic and its ghost references

Each Gold kernel has a ghost reference that transcribes the formula with the operations in the order the reference implementation applies them: `Eq_Ref` (the product over bits, from One), `Bindeq_Ref` (the recursive definition read pointwise), `Acc_Ref` and `Z_Ref` (the quad sum per output wire and the conjunction of the Z assertions over the first N terms), `EBQ_Ref` (the bound quad sum). The executable code mirrors the reference step by step and its loop invariant says, after K steps, exactly what the reference computes for K steps, as in chapters 1 and 2.

`Eval_Circuit` keeps every layer in one flat buffer (`Wires`, segment j from `Off (C, j)`); its postcondition says the input segment is W, every layer segment is the quad sum of the next one (`Layer_Holds`), and the status is "every Z assertion held and every output is Zero". The proof needs *frame lemmas*: writing segment j does not disturb the references of the segments above it. These are ghost procedures (`Lemma_Acc_Frame`, `Lemma_Layer_Frame`, `Lemma_From_Frame`, `Lemma_Layer_Intro`, `Lemma_Off_Mono`, `Lemma_Off_Step`) whose bodies prove their postconditions by recursion or by ghost loops, called from the executable body at the point where their conclusion is needed.

Two devices keep the provers on track. The bodies of the recursive references and of `Off` carry `Annotate => (GNATprove, Hide_Info, "Expression_Function_Body")` and are unhidden only inside the lemmas that need them (`Unhide_Info`): without this the provers unfold the recursions without bound and exhaust the step budget on trivial goals. Powers of two are a ghost `Big_Integer` function `Pow2`, as `Weight` in chapter 2, because `2 ** N` with a variable exponent is out of reach; `Bit_Of` is an ordinary function without postcondition, so `Eq` and `Eq_Ref` agree by congruence and no bit-vector reasoning enters any proof.

### 3.4 Expression: a discriminated record under a type predicate

`Expression (Capacity)` holds `Length`, `Known` and a sorted array `Terms (1 .. Capacity)` of (variable, coefficient) pairs; the predicate `Sorted` states that the variables of the first `Length` pairs are strictly increasing, which gives "no duplicate" for free ([ADR 0026](../adr/0026-sparse-expression.md)). `Find (E, V)` returns the position of V or 0, with a postcondition that pins it down: 0 means no pair has V, otherwise exactly that index has V. The ghost model is `Has (E, V) = Find (E, V) /= 0` and `Coef (E, V)`, the stored coefficient or `Zero`.

The postconditions quantify over the *positions* of the stored pairs, never over all variables: "every variable of E is in the result", "every variable of the result is V or a variable of E", "the variable at position I of F has coefficient `Coef (E, ...) + F.Terms (I).C`". The two forms say the same thing to the provers, but only the position-bounded one is executable: with `-gnata` the test build runs every postcondition, and a `for all W in Natural` is a loop over 2^31 values. The first version of this package had the unbounded form; the harness did not finish and the contracts were rewritten.

Every operation builds its result in a local array and constructs the record once, so that the predicate is checked once, at the end. `Add_Term` and `Sub_Term` share `Combine` (sorted insertion, or an update in place); `Add` and `Sub` fold the pairs of F into E with `Combine`, and their exact lengths are `E.Length + New_Count (E, F, F.Length)`, the number of F's variables absent from E. Zero coefficients are kept (ADR 0026): dropping them would make the postconditions rest on field identities the provers do not have.

Small lemmas carry the reasoning about `Find` out of the large verification conditions: `Lemma_Find_Equiv` (two expressions with the same variables at the same positions have the same `Find`), `Lemma_Find_Insert` (an insertion at Pos shifts the positions above it by one), `Lemma_Coef_Kept` (an untouched variable keeps its coefficient), `Lemma_Has_Below`, `Lemma_Below_Union` and `Lemma_Below_Insert` (variables stay below a bound through the operations). Most have a `null` body or a one-line assertion: the provers prove their postconditions from the postcondition of `Find` alone, and the operations and the verifier call them where the conclusion is needed instead of leaving a chain of `Find` instantiations to a prover facing a large context.

### 3.5 The Challenges record and the symbolic core

`Challenges (Last)` holds the 40 output-binding challenges `G`, every per-layer challenge in one flat array `Layer` (alpha, beta, then one per round and hand, layer after layer, from `Chal_Off (C, J)`) and `Alpha_Input`. `Sumcheck_Proof (Last)` holds the padded evaluations and claims, flat, in the pad order of Section 6.5 (which differs from the serialisation order of Section 7, where the two hands' p (0) precede the two hands' p (P2) within a round). `Claims_State (Capacity)` is a discriminated record whose components are themselves discriminated (`Claim0, Claim1 : Expression (Capacity)`) plus the two challenge vectors of the hands.

`Symbolic_Round` is an *expression function*: its body is the formula of Section 2.4 written with the operations of `Expression`, so it is Gold by definition and a reader checks it against the draft by reading it. `Lemma_Round_Shape` adds what the capacity accounting needs: when the two pad variables are fresh, the result has at most two more variables than the claim and all of them lie below the next pad index (`Below`, every stored variable under a bound). `Verify_Layer` carries the invariant `Below (Claim, pad pointer)`, which is what bounds every claim expression by 4 logw + 5 terms and discharges the preconditions of `Add` and `Sub`.

Two capacities are used, not one: the claim expressions of every layer are allocated with `Layer_Capacity = 4 * Max_Logw + 5` pairs (165), and only the input constraint with `Input_Capacity_Of (C) = ninput - npublic + 2`; `Sub (Mle, Got)` mixes the two, which is why the second operand of `Add` and `Sub` may have any capacity. The first version gave every expression the larger of the two: with 32768 private inputs on P-256 each expression was 1.3 MB, `Symbolic_Round` kept five of them alive on the stack and the default 8 MiB stack of macOS overflowed (found by review on a valid circuit with one layer; the ADR 0026 bound was never exceeded, the memory was). Expressions live on the stack; `Input_Constraint` still holds three of the large kind at once, about 120 bytes per private input on P-256, so this unit is limited to a few tens of thousands of private inputs on a default stack. A stack exhaustion is a `Storage_Error`, which the absence of run-time errors proof does not cover (SPARK User's Guide, "Dealing with Storage_Error"). Circuits of phase B size need an input constraint built outside the stack and in linear time; that is a phase B change.

The Ligero output is `Ligero_Terms (Max)`, the sparse matrix A in coordinate form as three parallel arrays (coefficient, constraint number, variable) with a count, and `B`, the vector of constants. Three arrays rather than an array of records because, with a P-256 `Element` inside the record, the frame conditions of `Constrain_To_Be_Zero` cost the provers 583450 steps; with parallel arrays, 62606.

### 3.6 Errors as status

No subprogram of stage 3 raises. `Eval_Quad` and `Eval_Circuit` return a Boolean; the core's inputs are checked by preconditions on the sizes of the records (`Chal_Total`, `Proof_Total`, `A_Bound`), which the caller of phase B establishes from the circuit before building them.

## 4. What the proofs guarantee

### 4.1 Structural Gold, and what it does not say

Gold at this stage means ([ADR 0023](../adr/0023-gold-perimeter-for-protocol-code.md)): the executable code is proved equal, for all inputs, to a ghost reference that transcribes the formula of the draft or of the reference implementation in a fixed order of operations. SPARK knows nothing of the field laws of the formal operations, so no contract uses commutativity, associativity or distributivity; the algebraic truths (bindeq agrees with eq, the Lagrange basis interpolates, the emitted constraints are satisfied by an honest witness) are tested.

The equality in these contracts is `Same`, not `=`. GNATprove encodes the predefined equality of a record with an array component, which both `Element` types are, as a pointwise predicate on the array, not as equality of terms; from `P = Eq_Ref (...)` the provers could not conclude `P * R = Eq_Ref (...) * R`, and no structural proof survives without that congruence. `Same` is annotated `Logical_Equal` in each field wrapper and the provers treat it as equality of terms, which gives congruence under any function. Its body returns the predefined `=` and lies outside SPARK: it executes in the test build and is *assumed* by the provers. What is proved with `Same` implies the predefined equality, so nothing proved is weaker than stated; that `Same` is the equality of each element type is a trusted item (Section 6).

The Expression postconditions are stated with the "absent means Zero" convention made explicit by case splits (`if Has (F, W) then Coef (E, W) + Coef (F, W) else Coef (E, W)`), because `Zero + K` and `K` are different terms; where the reference's formula reads `Zero + K`, the body computes `Zero + K`.

### 4.2 The verification condition table, per instance

GNATprove 16.1 with the project's prover configuration ([ADR 0020](../adr/0020-prover-configuration-step-budget.md)), the whole project at the end of stage 3: 6835 checks, all proved, no justification, no `pragma Assume`, against 3694 at the end of stage 2. Maximum steps for a single successful proof unchanged at 429702 (a P-256 lemma); the stage 3 maximum is 171089 (a postcondition of `Add` on P-256) and the core stays below 62606.

| Category | Checks | Discharged by |
|----------|--------|---------------|
| Data dependencies (`Global => null`) | 273 | flow analysis |
| Initialization | 64 | flow analysis |
| Run-time checks (indices, ranges, overflow, predicates, discriminants) | 3990 | 32% trivial, Z3 47%, CVC5 21% |
| Assertions (`pragma Assert`, loop invariants, variants) | 575 | Z3 65%, CVC5 28%, Alt-Ergo 3% |
| Functional contracts (postconditions, lemma postconditions, preconditions at calls) | 1709 | Z3 84%, CVC5 14%, Alt-Ergo 1% |
| Termination | 224 | 170 flow, 54 provers |

Proof checks by unit (flow excluded), the two instances side by side (GF(2^128), P-256): `Sumcheck_Algebra` 574 and 601, of which `Eval_Circuit` 83 and 83, `Bindeq` 50 and 53, `Eval_Quad` 34 and 35, `Bind_G` 33 and 33, the frame lemmas `Lemma_From_Frame` 47, `Lemma_Layer_Frame` 41, `Lemma_Acc_Frame` 33, `Lemma_Layer_Intro` 20; `Sumcheck_Expression` 362 and 431, of which `Fold` 98 and 106 (the ghost loops that carry the coefficients across an insertion), `Combine` 79 and 95, `Scale` 24 and 36; `Sumcheck_Verifier` 395 and 450, of which `Verify_Layer` 113 and 136, `Verifier_Core` 68 and 72, `Constrain_To_Be_Zero` 66 and 68, `Input_Constraint` 38 and 47, `Lemma_Round_Shape` 31 and 39. The P-256 instance costs more everywhere because every `Element` carries the canonical-form predicate as a dynamic invariant. As in chapter 2, which of CVC5 and Z3 is credited with a check varies from run to run.

Lessons from closing these proofs, reusable in the next stages:

- Equality of records with array components is not equality of terms for the provers; a structural proof through opaque functions needs `Logical_Equal`.
- Recursive ghost definitions must be hidden (`Hide_Info`) where they are not needed, or the provers unfold them without bound; `2 ** N` with a variable exponent is replaced by a ghost `Big_Integer` function.
- Frame conditions on arrays of predicated records cost hundreds of thousands of steps; parallel arrays of scalars and elements cost thousands.
- Reasoning about a search function (`Find`) inside a quantifier is best isolated in lemmas with `null` bodies or one-line assertions, called where the conclusion is needed.
- A contract that quantifies over an unbounded type (`for all W in Natural`) is fine for the provers and fatal for the assertion-enabled test build, which executes it as a loop; quantify over positions.
- The Why3 session returns stale "unproved" results for unchanged checks without re-running them; after a change, `gnatprove --clean` before trusting a list of unproved checks.

In plain terms, for every input, not on samples: no run-time error occurs in any stage 3 package; `Eq`, `Bindeq`, `Bind`, `Lagrange_Basis`, `Eval_Quad`, `Eval_Circuit`, `Bind_G` and `Eval_Bound_Quad` compute their references; every `Expression` operation produces exactly the presence and coefficients its postcondition states; `Symbolic_Round` is the formula of Section 6.7; the core emits NL + 1 linear constraints and NL quadratic triples at the pad indices of Section 6.5, within the stated bounds; every subprogram terminates.

Reproduce with `make prove`.

## 5. What is only tested

### 5.1 Tier 1: the explicit circuits of Appendix B.3

`gen_sumcheck_vectors.py` carries the two circuits of draft Appendix B.3 as term lists copied from the upstream unit tests (`docs/specs/rust/tests/unit_tests.rs`), the s-gonal circuit over P-256 with witness [1, 45, 5, 6] and the quadratic circuit over GF(2^128) with witness [1, n, 5, 6], plus a small circuit with a Z assertion; each with a passing witness and failing ones, and the expected wires of every layer. The harness `sumcheck_kat` builds each circuit (the predicate `Well_Formed` is checked at that point), runs `Eval_Circuit` and compares status and wires.

### 5.2 Tier 2: the algebra against an independent reference

The same generator computes `eq`, `eq2`, `bindeq`, `bind` and `lagrange_basis` from the draft's definitions (schoolbook GF(2^128) multiplication, plain integers mod p), on structural cases (all-zero and all-one challenges, the three evaluation points, zero padding) and seeded random cases, and checks itself: bindeq (c)[i] = eq (c, i, n) on every case, the Lagrange constants by d inv (d) = 1, the basis at the three points, its sum, and the interpolation of a random degree-two polynomial. The harness re-checks the constants with the library's multiplication and `Bindeq` against `Eq` at run time. 208 cases on the two fields.

### 5.3 Tier 3: recorded upstream runs with injected challenges

Agreement of `Verifier_Core` with the upstream verifier is checked on runs of the reference recorded by `tests/vectors/upstream/record_sumcheck_core.rs`, a test added to the upstream crate at d5e6be7 that rebuilds the B.3 circuits, runs the upstream prover and verifier, replays the core step by step writing out the challenges consumed, the padded proof, the claim after each round and the constraints emitted, and asserts that its replay produces the same A and b as the library's own core ([ADR 0027](../adr/0027-sumcheck-vectors-and-upstream-instrumentation.md), format there). The harness reads every `sumcheck_core_*.txt` present under `tests/vectors/upstream/`, feeds the core the recorded challenges and compares the constraints per constraint as sets of (variable, coefficient) pairs, zero coefficients ignored on both sides, plus b and the quadratic triples: 20 checks on the two circuits. The recordings are produced outside this repository from that test; none is synthesised here.

### 5.4 Errata of draft-03 found at this stage

Appendix B.3.2 is labelled "P-256 scalar field (Field ID 2)" but prints the base field prime and the upstream code uses it; Table 1 gives p256 the identifier 0x01. B.3.3 is labelled "Field ID 5", which Table 1 assigns to GF(2^16). B.3.3 gives the witness as [1, 84, 5, 6], but the circuit requires (s + 1) m^2 + (s + 1) m + n = 0 in GF(2^128), which with m = 5 and s = 6 gives n = 0x6c; the upstream test computes n in the field exactly so. The vectors follow the code; the errata are recorded in ADR 0027 and reported upstream.

## 6. What stays trusted, and the limits

- That `Same` of each field wrapper is the equality of its element type: its body is the predefined `=` outside SPARK (chapter 3 adds this to the trust model).
- The field laws of the two instances, never stated to the provers; the algebraic truths of Section 1 are tested.
- The challenge derivation, until stage 4 replaces the injected `Challenges` record with a replayed transcript; a challenge record built from a wrong transcript gives a wrong constraint system that proves fine.
- That the upstream recordings of tier 3 were taken faithfully from d5e6be7 with the kept patch, and that the upstream reference is itself the draft's protocol.
- The soundness argument of the protocol, which no contract states, and the pinned specification itself.

Limits of this stage: no accept or reject exists yet (the Ligero check is phase B); `Expression` is linear in the number of terms and quadratic in the input constraint, and the input constraint lives on the stack (Section 3.5), adequate for the test circuits and a few tens of thousands of inputs, a phase B concern beyond that; stack exhaustion is outside the proofs; `Ceil_Lg2` and the bound `Max_Wires = 2^24` cap the circuits this unit accepts.
