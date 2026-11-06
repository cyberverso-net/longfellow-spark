// One v2 proof or one v2 verification of the mDoc v7 flow, for the heap
// profile: `heap_v7 prove FILE` writes the proof, `heap_v7 verify FILE`
// checks it. The setup is that of benches/mdoc_zk_bench_v7.rs at d5e6be7.
use compile_algebra::CompileNat;
use core_algebra::Nat;
use mdoc_zk_circuits::parse_test_data;
use mdoc_zk_runtime::{req_attr, run_mdoc_prover_inner, run_mdoc_verifier_inner, RequestedAttribute};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (mode, file) = (args[1].as_str(), args[2].as_str());
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&mdoc_zk_testcases::vectors::TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .take(1)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();
    let mdoc_bytes = mdoc_zk_testcases::vectors::TEST_DATA.mdoc;
    let transcript = mdoc_zk_testcases::vectors::TEST_DATA.transcript;
    let doc_type = "org.iso.18013.5.1.mDL";
    let pkx = format!("0x{}", num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le()).to_str_radix(16));
    let pky = format!("0x{}", num_bigint::BigUint::from_bytes_le(&issuer_pk.1.to_bytes_le()).to_str_radix(16));
    let provided = mdoc_zk_runtime::provider::materialize(7, req_attrs.len()).unwrap();
    let spec = &provided.spec;
    let circuits_v2 = mdoc_zk_artifacts::load_circuit_v2(&spec.combined_hash_hex());
    if mode == "prove" {
        let mut rng = runtime_random::DeterministicRng::new(42);
        let proof = run_mdoc_prover_inner(spec, &circuits_v2, mdoc_bytes, &pkx, &pky, transcript,
                                          &req_attrs, now, doc_type, &mut rng).unwrap();
        std::fs::write(file, &proof).unwrap();
        println!("proof {} bytes", proof.len());
    } else {
        let proof = std::fs::read(file).unwrap();
        run_mdoc_verifier_inner(spec, &circuits_v2, &pkx, &pky, transcript, &req_attrs, now,
                                doc_type, &proof).unwrap();
        println!("verified");
    }
}
