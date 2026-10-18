// Cross-verification of a proof file made by longfellow-spark with the
// upstream verifier (ADR 0053).
//
// Drop this file into docs/specs/rust/tests/ of google/longfellow-zk at
// commit d5e6be7 and run, from docs/specs/rust,
//
//     LFS_FIELD=gf2_128 \
//     LFS_CIRCUIT=tests/testdata/sha256_circuit.lfc2 \
//     LFS_INPUTS=tests/testdata/sha256_inputs.json \
//     LFS_PROOF=<longfellow-spark>/cli/out/sha256_seed7.bin \
//     LFS_LABEL=sha256_spec_test LFS_RATE_INV=3 LFS_NREQ=16 LFS_NCOL=256 \
//     cargo test --test verify_proof_file -- --nocapture
//
// and the same with LFS_FIELD=p256 for an ecdsa2 proof (rate 4). The
// test loads the circuit, parses the inputs as test_reference.rs does,
// reads the proof file with read_zk_proof and verifies it with
// ZkVerifier under the label and configuration given; it passes only
// if the upstream verifier accepts. Without LFS_PROOF it is skipped.
// The library is not modified.

use std::{
    env,
    fs::File,
    io::{BufReader, Cursor},
};

use num_bigint::BigInt;
use reference::{
    algebra::{Field, Gf2_128, P256},
    circuit::parse_lfc2_bytes,
    ligero::LigeroConfig,
    zk::{ZkVerifier, read_zk_proof},
};

fn verify_file<F: Field + 'static>(parse_input_fn: impl Fn(&str) -> F) {
    let circuit_path = env::var("LFS_CIRCUIT").expect("LFS_CIRCUIT");
    let inputs_path = env::var("LFS_INPUTS").expect("LFS_INPUTS");
    let proof_path = env::var("LFS_PROOF").expect("LFS_PROOF");
    let label = env::var("LFS_LABEL").expect("LFS_LABEL");
    let config = LigeroConfig {
        rate_inv: env::var("LFS_RATE_INV").expect("LFS_RATE_INV").parse().unwrap(),
        num_queries: env::var("LFS_NREQ").expect("LFS_NREQ").parse().unwrap(),
        encoded_len: env::var("LFS_NCOL").expect("LFS_NCOL").parse().unwrap(),
    };

    let circuit_file = File::open(&circuit_path).expect("circuit file");
    let mut circuit_reader = BufReader::new(circuit_file);
    let circuit_data =
        parse_lfc2_bytes::<F, _>(&mut circuit_reader).expect("LFC2 circuit");

    let inputs_file = File::open(&inputs_path).expect("inputs file");
    let raw_inputs: Vec<String> =
        serde_json::from_reader(inputs_file).expect("inputs JSON");
    let inputs: Vec<F> = raw_inputs.iter().map(|s| parse_input_fn(s)).collect();
    let n_public = circuit_data.npublic_input;

    let bytes = std::fs::read(&proof_path).expect("proof file");
    let sf = F::Subfield::default();
    let mut reader = Cursor::new(&bytes);
    let proof = read_zk_proof(&mut reader, &circuit_data, &sf, &config)
        .expect("the proof file does not parse");

    let verifier = ZkVerifier::new(circuit_data, config);
    verifier
        .verify(&inputs[0..n_public], &proof, &label)
        .expect("the upstream verifier refuses the proof");
    println!(
        "verify_proof_file: {} ({} bytes) accepted by the upstream verifier",
        proof_path,
        bytes.len()
    );
}

#[test]
fn verify_proof_file() {
    if env::var("LFS_PROOF").is_err() {
        println!("verify_proof_file: LFS_PROOF not set, skipped");
        return;
    }
    match env::var("LFS_FIELD").expect("LFS_FIELD").as_str() {
        "gf2_128" => verify_file(|s: &str| {
            let val = BigInt::parse_bytes(s.as_bytes(), 10).unwrap();
            let mut v_bytes = val.to_bytes_le().1;
            v_bytes.resize(16, 0);
            Gf2_128::from_bytes(&v_bytes).unwrap()
        }),
        "p256" => verify_file(|s: &str| {
            let val = BigInt::parse_bytes(s.as_bytes(), 10).unwrap();
            P256::new(val)
        }),
        other => panic!("unknown field {}", other),
    }
}
