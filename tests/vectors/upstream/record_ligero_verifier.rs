// Recording of the upstream Ligero verifier for the longfellow-spark
// harness (tier 3 of ADR 0040).
//
// Drop this file into docs/specs/rust/tests/ of google/longfellow-zk at
// commit d5e6be7 and run
//
//     cargo test --test record_ligero_verifier -- --nocapture
//
// It rebuilds the two explicit circuits of draft Appendix B.3 exactly as
// unit_tests.rs does, runs the upstream prover and verifier, then replays
// LigeroVerifier::verify step by step on a transcript built as
// zk/verifier.rs builds it (root, statement, the symbolic sumcheck core,
// then the fixed statement hash), writing the challenges, the chosen
// columns and the two sides of each test, in the line format of ADR 0040,
// to /tmp/ligero_<field>_<circuit>.txt. The steps are the private
// functions of ligero/verifier.rs transcribed over the public API; each
// must agree where the library's verifier accepted. The library is not
// modified.

use std::fs::File;
use std::io::Write;

use reference::{
    algebra::{Field, Gf2_128, P256, Rng, Subfield, axpy, dot, dot1, vaxpy},
    circuit::{Circuit, CircuitLayer, Term},
    ligero::{
        LigeroConfig, LigeroGeometry, LigeroProof, LigeroTerm, LqcTriple, ReedSolomonCode,
        gen_alphal, gen_alphaq, gen_uldt, gen_uquad,
    },
    merkle::{sha256_bytes, verify_merkle_proof},
    transcript::Transcript,
    zk::{
        DEFAULT_STATEMENT_HASH, ZkProver, ZkVerifier, generate_lqc_triples,
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

/// encode_row of the code of dimension k at the queried columns
/// (interpolate_req_columns of ligero/verifier.rs).
fn interpolate_req_columns<F: Field + 'static>(
    geom: &LigeroGeometry,
    k: usize,
    y: &[F],
    idx: &[usize],
    sf: &F::Subfield,
) -> Vec<F> {
    let rs = ReedSolomonCode::new(k, geom.encoded_len, sf);
    let y_ext = rs.encode_row()(y);
    idx.iter().map(|&col| y_ext[geom.dblock_len + col]).collect()
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
    let verifier = ZkVerifier::new(circuit.clone(), config.clone());
    assert!(verifier.verify(pub_inputs, &proof, label).is_ok(), "upstream verification failed");

    // The transcript as zk/verifier.rs builds it, through the core.
    let pad_base = circuit.ninput - circuit.npublic_input;
    let mut ts = Transcript::new(label.as_bytes());
    ts.write_bytes(&proof.root);
    write_sumcheck_statement(&mut ts, circuit, pub_inputs);
    let core = symbolic_sumcheck_verifier_core(
        pad_base,
        pub_inputs,
        circuit,
        &proof.sumcheck_proof,
        &mut ts,
    );
    let a: &[LigeroTerm<F>] = &core.a;
    let b: &[F] = &core.b;
    let lqc: Vec<LqcTriple> = generate_lqc_triples(circuit);
    let mut nw = circuit.ninput - circuit.npublic_input;
    for layer in &circuit.layers {
        nw += 4 * layer.logw + 3;
    }
    let sf = F::Subfield::default();
    let lp: &LigeroProof<F> = &proof.ligero_proof;

    let mut lines: Vec<String> = Vec::new();
    lines.push("# Recorded run of the upstream Ligero verifier,".to_string());
    lines.push(format!(
        "# google/longfellow-zk d5e6be7, docs/specs/rust, circuit {} over {}.",
        name, field
    ));
    lines.push("# Produced by record_ligero_verifier.rs (tests/vectors/upstream/); format: ADR 0040.".to_string());
    lines.push(format!("field {}", field));
    lines.push(format!(
        "ligero {} {} {} {}",
        name, config.rate_inv, config.num_queries, config.encoded_len
    ));

    // LigeroVerifier::verify, step by step.
    ts.write_bytes(&DEFAULT_STATEMENT_HASH);
    let geom = LigeroGeometry::new(&config, nw, lqc.len());
    lines.push(format!(
        "geometry {} {} {} {} {} {} {} {}",
        geom.block_len,
        geom.dblock_len,
        geom.witnesses_per_row,
        nw,
        lqc.len(),
        geom.num_witness_rows,
        geom.num_quad_rows,
        geom.total_rows
    ));
    assert_eq!(lp.queried_columns.len(), geom.total_rows * geom.num_queries);
    assert_eq!(lp.ldt_poly.len(), geom.block_len);
    assert_eq!(lp.linear_poly.len(), geom.dblock_len);
    assert_eq!(lp.quad_poly_low.len(), geom.num_queries);
    assert_eq!(lp.quad_poly_high.len(), geom.dblock_len - geom.block_len);
    assert_eq!(lp.column_nonces.len(), geom.num_queries);
    let nwqrow = geom.total_rows - 3;
    let u_ldt: Vec<F> = gen_uldt(&mut ts, nwqrow);
    let alphal: Vec<F> = gen_alphal(&mut ts, b.len());
    let alphaq: Vec<Vec<F>> = gen_alphaq(&mut ts, lqc.len());
    let u_quad: Vec<F> = gen_uquad(&mut ts, geom.num_quad_rows);
    lines.push(format!("u_ldt {}", join(&u_ldt)));
    lines.push(format!("alphal {}", join(&alphal)));
    for (q, aq) in alphaq.iter().enumerate() {
        lines.push(format!("alphaq {} {}", q, join(aq)));
    }
    lines.push(format!("u_quad {}", join(&u_quad)));
    ts.write_elt_field_slice(&lp.ldt_poly);
    ts.write_elt_field_slice(&lp.linear_poly);
    ts.write_elt_field_slice(&lp.quad_poly_low);
    ts.write_elt_field_slice(&lp.quad_poly_high);
    let idx = ts.choose(geom.encoded_len - geom.dblock_len, geom.num_queries);
    lines.push(format!(
        "idx {}",
        idx.iter().map(|i| i.to_string()).collect::<Vec<_>>().join(" ")
    ));

    // verify_merkle
    let leaf_hash_fn = |col: usize| {
        let mut r_idx = 0;
        for i in 0..idx.len() {
            if idx[i] == col {
                r_idx = i;
                break;
            }
        }
        let mut data = Vec::new();
        data.extend_from_slice(&lp.column_nonces[r_idx]);
        for row in 0..geom.total_rows {
            data.extend_from_slice(&lp.queried_columns[row * geom.num_queries + r_idx].to_bytes());
        }
        sha256_bytes(&data)
    };
    verify_merkle_proof(
        geom.encoded_len - geom.dblock_len,
        &proof.root,
        &idx,
        &lp.merkle_paths,
        leaf_hash_fn,
    )
    .expect("verify_merkle");

    // verify_ldt
    let ildt = geom.ldt_row_idx();
    let iw = geom.witness_row_start();
    let mut yc_ldt = lp.queried_columns[ildt * geom.num_queries..(ildt + 1) * geom.num_queries].to_vec();
    for i in 0..nwqrow {
        let row_req = &lp.queried_columns[(iw + i) * geom.num_queries..(iw + i + 1) * geom.num_queries];
        axpy(&mut yc_ldt, row_req, u_ldt[i]);
    }
    let yp_ldt = interpolate_req_columns(&geom, geom.block_len, &lp.ldt_poly, &idx, &sf);
    lines.push(format!("ldt {} {}", join(&yc_ldt), join(&yp_ldt)));
    assert_eq!(yc_ldt, yp_ldt, "verify_ldt");

    // verify_dot
    let idot = geom.linear_row_idx();
    let mut a_full = vec![F::zero(); nwqrow * geom.witnesses_per_row];
    for term in a {
        a_full[term.witness_idx] += term.coeff * alphal[term.constraint_idx];
    }
    let nqtriples_w = geom.num_quad_rows * geom.witnesses_per_row;
    let ax_offset = (nwqrow - 3 * geom.num_quad_rows) * geom.witnesses_per_row;
    let ay_offset = ax_offset + nqtriples_w;
    let az_offset = ay_offset + nqtriples_w;
    for i in 0..geom.num_quad_rows {
        let mut j = 0;
        while j < geom.witnesses_per_row && j + i * geom.witnesses_per_row < lqc.len() {
            let idx_lqc = j + i * geom.witnesses_per_row;
            let l = lqc[idx_lqc];
            a_full[ax_offset + idx_lqc] += alphaq[idx_lqc][0];
            a_full[l.x] -= alphaq[idx_lqc][0];
            a_full[ay_offset + idx_lqc] += alphaq[idx_lqc][1];
            a_full[l.y] -= alphaq[idx_lqc][1];
            a_full[az_offset + idx_lqc] += alphaq[idx_lqc][2];
            a_full[l.z] -= alphaq[idx_lqc][2];
            j += 1;
        }
    }
    let mut yc_dot = lp.queried_columns[idot * geom.num_queries..(idot + 1) * geom.num_queries].to_vec();
    let a_interp = ReedSolomonCode::new(geom.block_len, geom.encoded_len, &sf);
    for i in 0..nwqrow {
        let mut a_ext = vec![F::zero(); geom.block_len];
        let start = i * geom.witnesses_per_row;
        a_ext[geom.num_queries..geom.block_len]
            .copy_from_slice(&a_full[start..(start + geom.witnesses_per_row)]);
        let a_evals = a_interp.encode_row()(&a_ext);
        let mut a_queried = Vec::with_capacity(geom.num_queries);
        for &col in &idx {
            a_queried.push(a_evals[geom.dblock_len + col]);
        }
        let row_req = &lp.queried_columns[(iw + i) * geom.num_queries..(iw + i + 1) * geom.num_queries];
        vaxpy(&mut yc_dot, row_req, &a_queried);
    }
    let yp_dot = interpolate_req_columns(&geom, geom.dblock_len, &lp.linear_poly, &idx, &sf);
    lines.push(format!("dot {} {}", join(&yc_dot), join(&yp_dot)));
    assert_eq!(yc_dot, yp_dot, "verify_dot");
    let want_dot = dot(b, &alphal);
    let proof_dot = dot1(&lp.linear_poly[geom.num_queries..(geom.num_queries + geom.witnesses_per_row)]);
    lines.push(format!("dot_sum {} {}", hex(&want_dot), hex(&proof_dot)));
    assert_eq!(proof_dot + want_dot, F::zero(), "verify_dot sum");

    // verify_quad
    let iquad = geom.quad_row_idx();
    let iqx = geom.quad_x_row_start();
    let iqy = geom.quad_y_row_start();
    let iqz = geom.quad_z_row_start();
    let mut yc_quad = lp.queried_columns[iquad * geom.num_queries..(iquad + 1) * geom.num_queries].to_vec();
    for i in 0..geom.num_quad_rows {
        let u = u_quad[i];
        let mut tmp = vec![F::zero(); geom.num_queries];
        for j in 0..geom.num_queries {
            let x_val = lp.queried_columns[(iqx + i) * geom.num_queries + j];
            let y_val = lp.queried_columns[(iqy + i) * geom.num_queries + j];
            let z_val = lp.queried_columns[(iqz + i) * geom.num_queries + j];
            tmp[j] = z_val - x_val * y_val;
        }
        axpy(&mut yc_quad, &tmp, u);
    }
    let mut y_quad = lp.quad_poly_low.clone();
    y_quad.resize(geom.block_len, F::zero());
    y_quad.extend_from_slice(&lp.quad_poly_high);
    let yp_quad = interpolate_req_columns(&geom, geom.dblock_len, &y_quad, &idx, &sf);
    lines.push(format!("quad {} {}", join(&yc_quad), join(&yp_quad)));
    assert_eq!(yc_quad, yp_quad, "verify_quad");

    lines.push("verdict ok".to_string());
    lines.push("end".to_string());

    let path = format!("/tmp/ligero_{}_{}.txt", field, name);
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
