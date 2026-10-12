// Recording of the upstream symbolic sumcheck verifier core for the
// longfellow-spark harness (tier 3 of ADR 0027).
//
// Drop this file into docs/specs/rust/tests/ of google/longfellow-zk at
// commit d5e6be7 and run
//
//     cargo test --test record_sumcheck_core -- --nocapture
//
// It rebuilds the two explicit circuits of draft Appendix B.3 exactly as
// unit_tests.rs does, runs the upstream prover and verifier, then replays
// symbolic_sumcheck_verifier_core step by step on a transcript built as
// zk/verifier.rs builds it, writing every challenge drawn, the padded
// proof, the claim expression after each round and the constraints
// emitted, in the line format of ADR 0027, to
// /tmp/sumcheck_core_<field>_<circuit>.txt. The replay is checked against
// the library's own core (same A, same b) before anything is written.
// The library is not modified.

use std::fs::File;
use std::io::Write;

use reference::{
    algebra::{Field, Gf2_128, P256, Rng, ceil_lg2, lagrange_basis},
    circuit::{Circuit, CircuitLayer, Term},
    ligero::{LigeroConfig, LigeroTerm},
    sumcheck::{
        CircuitPad, begin_circuit, begin_layer, end_layer, eq2, eval_bound_quad,
        round_poly,
    },
    transcript::Transcript,
    zk::{
        Expression, Var, ZkProver, ZkVerifier, generate_lqc_triples,
        symbolic_sumcheck_verifier_core, write_sumcheck_statement,
    },
};

struct SimpleRng {
    state: u64,
}

impl SimpleRng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }
}

impl Rng for SimpleRng {
    fn bytes(&mut self, len: usize) -> Vec<u8> {
        let mut out = Vec::with_capacity(len);
        let mut state = self.state;
        for _ in 0..len {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            out.push(((state >> 32) & 0xff) as u8);
        }
        self.state = state;
        out
    }
}

/// Big-endian hex of the element (to_bytes is little-endian, Section 7.2.1).
fn hex<F: Field>(x: &F) -> String {
    let mut b = x.to_bytes();
    b.reverse();
    b.iter().map(|v| format!("{:02x}", v)).collect()
}

fn join<F: Field>(v: &[F]) -> String {
    v.iter().map(hex).collect::<Vec<_>>().join(" ")
}

/// "<n> <var> <coeff> ..." with the variables in increasing order.
fn terms_line<F: Field>(e: &Expression<F>) -> String {
    let mut terms: Vec<(usize, F)> = e.terms.iter().map(|(k, v)| (*k, *v)).collect();
    terms.sort_by_key(|t| t.0);
    let mut s = format!("{}", terms.len());
    for (v, c) in terms {
        s += &format!(" {} {}", v, hex(&c));
    }
    s
}

fn constrain<F: Field>(a: &mut Vec<LigeroTerm<F>>, b: &mut Vec<F>, expr: &Expression<F>) {
    let c = b.len();
    for (&witness_idx, &coeff) in &expr.terms {
        a.push(LigeroTerm {
            coeff,
            constraint_idx: c,
            witness_idx,
        });
    }
    b.push(expr.known);
}

/// Sorted (constraint, variable, coeff) triples, for comparison.
fn sorted_a<F: Field>(a: &[LigeroTerm<F>]) -> Vec<(usize, usize, String)> {
    let mut v: Vec<(usize, usize, String)> = a
        .iter()
        .map(|t| (t.constraint_idx, t.witness_idx, hex(&t.coeff)))
        .collect();
    v.sort();
    v
}

fn record<F: Field + 'static>(
    field: &str,
    name: &str,
    circuit: &Circuit<F>,
    inputs: &[F],
    label: &str,
) {
    let config = LigeroConfig {
        rate_inv: 4,
        num_queries: 6,
        encoded_len: 64,
    };
    let mut rng = SimpleRng::new(12345);
    let prover = ZkProver::new(circuit.clone(), config.clone());
    let commit = prover.commit(inputs, &mut rng);
    let proof = prover.prove(inputs, &commit, label);
    let pub_inputs = &inputs[..circuit.npublic_input];
    let verifier = ZkVerifier::new(circuit.clone(), config);
    assert!(verifier.verify(pub_inputs, &proof, label).is_ok(), "upstream verification failed");

    // The library's own core, on a transcript built as zk/verifier.rs does.
    let pad_base = circuit.ninput - circuit.npublic_input;
    let mut ts_lib = Transcript::new(label.as_bytes());
    ts_lib.write_bytes(&proof.root);
    write_sumcheck_statement(&mut ts_lib, circuit, pub_inputs);
    let lib = symbolic_sumcheck_verifier_core(
        pad_base,
        pub_inputs,
        circuit,
        &proof.sumcheck_proof,
        &mut ts_lib,
    );

    let mut lines: Vec<String> = Vec::new();
    lines.push(format!("# Recorded run of the upstream symbolic sumcheck verifier core,"));
    lines.push(format!("# google/longfellow-zk d5e6be7, docs/specs/rust, circuit {} over {}.", name, field));
    lines.push(format!("# Produced by record_sumcheck_core.rs (tests/vectors/upstream/); format: ADR 0027."));
    lines.push(format!("field {}", field));
    lines.push(format!(
        "circuit {} {} {} {} {}",
        name,
        circuit.noutput,
        circuit.ninput,
        circuit.npublic_input,
        circuit.layers.len()
    ));
    for (j, layer) in circuit.layers.iter().enumerate() {
        lines.push(format!("layer {} {} {} {}", j, layer.logw, layer.nw, layer.quad.len()));
        for t in &layer.quad {
            lines.push(format!("term {} {} {} {}", t.g, t.h[0], t.h[1], hex(&t.k)));
        }
    }
    lines.push(format!("public {}", join(pub_inputs)));
    lines.push(format!("pad_base {}", pad_base));

    // The replay, recording as it goes.
    let mut ts = Transcript::new(label.as_bytes());
    ts.write_bytes(&proof.root);
    write_sumcheck_statement(&mut ts, circuit, pub_inputs);

    let (_q, g) = begin_circuit::<F>(&mut ts);
    lines.push(format!("g {}", join(&g)));
    let logv_output = ceil_lg2(circuit.noutput);
    let hc_init = g[0..logv_output].to_vec();
    let mut claims = [Expression::<F>::zero(), Expression::<F>::zero()];
    let mut logv = logv_output;
    let mut hc = [hc_init.clone(), hc_init];
    let mut pad_index = pad_base;
    let circuit_pad = CircuitPad::generate_indices(circuit, &mut pad_index);
    let mut a: Vec<LigeroTerm<F>> = Vec::new();
    let mut b: Vec<F> = Vec::new();
    let mut claim_lines: Vec<String> = Vec::new();

    for (ly, clr) in circuit.layers.iter().enumerate() {
        let plr = &proof.sumcheck_proof[ly];
        let pad = &circuit_pad.layers[ly];
        let (alpha, beta) = begin_layer(&mut ts);
        let mut chal_line = format!("layer_challenges {} {} {}", ly, hex(&alpha), hex(&beta));
        let mut proof_line = format!("proof {}", ly);
        let mut claim = claims[0].clone() + claims[1].clone() * alpha;
        let mut lchal: [Vec<F>; 2] = [Vec::new(), Vec::new()];
        for round in 0..clr.logw {
            for hand in 0..2 {
                let hp = &plr.hp[hand][round];
                let round_pad = &pad.rounds[round].hp[hand];
                let chal = round_poly(&mut ts, &hp.evals);
                let lag = lagrange_basis(chal);
                let p0 = Var(round_pad[0]) + hp.evals[0];
                let p2 = Var(round_pad[1]) + hp.evals[1];
                let p1 = claim - p0.clone();
                claim = p0 * lag[0] + p1 * lag[1] + p2 * lag[2];
                lchal[hand].push(chal);
                chal_line += &format!(" {}", hex(&chal));
                proof_line += &format!(" {} {}", hex(&hp.evals[0]), hex(&hp.evals[1]));
                claim_lines.push(format!(
                    "claim {} {} {} {} {}",
                    ly,
                    round,
                    hand,
                    hex(&claim.known),
                    terms_line(&claim)
                ));
            }
        }
        proof_line += &format!(" {} {}", hex(&plr.claims[0]), hex(&plr.claims[1]));
        lines.push(chal_line);
        lines.push(proof_line);
        let eqq = eval_bound_quad(
            &clr.quad, logv, &hc[0], &hc[1], &lchal[0], &lchal[1], clr.logw, alpha, beta,
        );
        let prod = (Var(pad.claims.c0) * plr.claims[1]
            + Var(pad.claims.c1) * plr.claims[0]
            + Var(pad.claims.cr)
            + (plr.claims[0] * plr.claims[1]))
            * eqq;
        claim -= prod;
        constrain(&mut a, &mut b, &claim);
        end_layer(&mut ts, &plr.claims);
        claims = [
            Var(pad.claims.c0) + plr.claims[0],
            Var(pad.claims.c1) + plr.claims[1],
        ];
        logv = clr.logw;
        hc = lchal;
    }

    let alpha_input: F = ts.get_elt_field();
    lines.push(format!("alpha_input {}", hex(&alpha_input)));
    let got = claims[0].clone() + claims[1].clone() * alpha_input;
    let num_inputs = circuit.ninput;
    let num_public = circuit.npublic_input;
    let mut eq_vec = Vec::with_capacity(num_inputs);
    for i in 0..num_inputs {
        eq_vec.push(eq2(i, logv, &hc[0], &hc[1], alpha_input));
    }
    let mut pub_binding = F::zero();
    for i in 0..num_public {
        pub_binding += eq_vec[i] * pub_inputs[i];
    }
    let mut mle = Expression::from(pub_binding);
    for w in 0..(num_inputs - num_public) {
        mle += Var(w) * eq_vec[num_public + w];
    }
    mle -= got;
    constrain(&mut a, &mut b, &mle);

    // The replay must be the library's core.
    assert_eq!(b.len(), lib.b.len(), "constraint count");
    for (x, y) in b.iter().zip(lib.b.iter()) {
        assert_eq!(hex(x), hex(y), "b differs");
    }
    assert_eq!(sorted_a(&a), sorted_a(&lib.a), "A differs");

    lines.extend(claim_lines);
    for (c, bc) in b.iter().enumerate() {
        let mut terms: Vec<(usize, F)> = a
            .iter()
            .filter(|t| t.constraint_idx == c)
            .map(|t| (t.witness_idx, t.coeff))
            .collect();
        terms.sort_by_key(|t| t.0);
        let mut s = format!("constraint {} {} {}", c, hex(bc), terms.len());
        for (v, k) in terms {
            s += &format!(" {} {}", v, hex(&k));
        }
        lines.push(s);
    }
    for (j, t) in generate_lqc_triples(circuit).iter().enumerate() {
        lines.push(format!("lqc {} {} {} {}", j, t.x, t.y, t.z));
    }
    lines.push("end".to_string());

    let path = format!("/tmp/sumcheck_core_{}_{}.txt", field, name);
    let mut f = File::create(&path).expect("create output");
    for l in &lines {
        writeln!(f, "{}", l).expect("write");
    }
    println!("wrote {} ({} lines)", path, lines.len());
}

fn p256_val(x: i64) -> P256 {
    P256::new(num_bigint::BigInt::from(x))
}

fn sgonal_p256() -> Circuit<P256> {
    let layer1_terms = vec![
        Term { k: p256_val(1), g: 0, h: [0, 0] },
        Term { k: p256_val(1), g: 1, h: [2, 2] },
        Term { k: p256_val(1), g: 2, h: [0, 3] },
        Term { k: p256_val(-2), g: 2, h: [0, 0] },
        Term { k: p256_val(1), g: 3, h: [2, 3] },
        Term { k: p256_val(-4), g: 3, h: [0, 2] },
        Term { k: p256_val(2), g: 4, h: [0, 1] },
    ];
    let layer0_terms = vec![
        Term { k: p256_val(1), g: 0, h: [1, 2] },
        Term { k: p256_val(-1), g: 0, h: [0, 3] },
        Term { k: p256_val(-1), g: 0, h: [0, 4] },
    ];
    Circuit {
        id: [0u8; 32],
        field_id: 2,
        noutput: 1,
        logv: 0,
        npublic_input: 1,
        subfield_boundary: 0,
        ninput: 4,
        layers: vec![
            CircuitLayer { logw: 3, nw: 5, quad: layer0_terms },
            CircuitLayer { logw: 2, nw: 4, quad: layer1_terms },
        ],
    }
}

fn sgonal_gf2_128() -> Circuit<Gf2_128> {
    let one = Gf2_128::one();
    let layer1_terms = vec![
        Term { k: one, g: 0, h: [0, 0] },
        Term { k: one, g: 1, h: [2, 2] },
        Term { k: one, g: 2, h: [0, 3] },
        Term { k: one, g: 2, h: [0, 0] },
        Term { k: one, g: 3, h: [2, 3] },
        Term { k: one, g: 3, h: [0, 2] },
        Term { k: one, g: 4, h: [0, 1] },
    ];
    let layer0_terms = vec![
        Term { k: one, g: 0, h: [1, 2] },
        Term { k: one, g: 0, h: [0, 3] },
        Term { k: one, g: 0, h: [0, 4] },
    ];
    Circuit {
        id: [0u8; 32],
        field_id: 5,
        noutput: 1,
        logv: 0,
        npublic_input: 1,
        subfield_boundary: 0,
        ninput: 4,
        layers: vec![
            CircuitLayer { logw: 3, nw: 5, quad: layer0_terms },
            CircuitLayer { logw: 2, nw: 4, quad: layer1_terms },
        ],
    }
}

#[test]
fn record_sgonal_p256() {
    let circuit = sgonal_p256();
    let inputs = vec![p256_val(1), p256_val(45), p256_val(5), p256_val(6)];
    record("p256", "b3_2_sgonal", &circuit, &inputs, "sgonal_test_vector_p256");
}

#[test]
fn record_quadratic_gf2_128() {
    let circuit = sgonal_gf2_128();
    let m = Gf2_128 { v: 5 };
    let s = Gf2_128 { v: 6 };
    let s_plus_1 = s + Gf2_128::one();
    let n = (s_plus_1 * m * m) + (s_plus_1 * m);
    let inputs = vec![Gf2_128::one(), n, m, s];
    record("gf2_128", "b3_3_quadratic", &circuit, &inputs, "sgonal_test_vector_gf2_128");
}
