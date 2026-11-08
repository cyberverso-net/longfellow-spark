// One LFA2 proof or one LFA2 verification of the mDoc v7 flow, for the heap
// profile, on upstream's single crate (after 759b94a, "Refactor the rust
// implementation into 1 crate"): `heap_v7 prove FILE` writes the proof,
// `heap_v7 verify FILE` checks it. The same setup as scripts/measure/heap_v7.rs
// for d5e6be7 (benches/mdoc_zk_bench_v7.rs there, now
// applications/mdoc_zk/runtime/benches/mdoc_zk_bench_v1.rs): TEST_DATA, one
// attribute, the version 7 archive, DeterministicRng seed 42. It prints the
// upstream commit it was built for (MEASURE_UPSTREAM at build time), the
// second label of every series.
// Build from rust/ with the file at rust/examples/heap_v7.rs:
//   MEASURE_UPSTREAM=<commit> RUSTFLAGS="-C target-cpu=x86-64" cargo build \
//     --release --example heap_v7 --features testonly,force-generic-arch
use longfellow_zk::compile::algebra::CompileNat;
use longfellow_zk::core::algebra::Nat;
use longfellow_zk::mdoc::circuits::parse_test_data;
use longfellow_zk::mdoc::v1::{req_attr, run_mdoc_prover_inner, run_mdoc_verifier_inner, RequestedAttribute};

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (mode, file) = (args[1].as_str(), args[2].as_str());
    println!("upstream {}", option_env!("MEASURE_UPSTREAM").unwrap_or("unlabelled"));
    let (issuer_pk, parsed, now) =
        parse_test_data::<4, CompileNat<4>>(&longfellow_zk::mdoc::testcases::vectors::TEST_DATA);
    let req_attrs: Vec<RequestedAttribute> = parsed
        .attrs
        .iter()
        .take(1)
        .map(|a| req_attr("org.iso.18013.5.1", &a.name, &a.cbor_value))
        .collect();
    let mdoc_bytes = longfellow_zk::mdoc::testcases::vectors::TEST_DATA.mdoc;
    let transcript = longfellow_zk::mdoc::testcases::vectors::TEST_DATA.transcript;
    let doc_type = "org.iso.18013.5.1.mDL";
    let pkx = format!("0x{}", num_bigint::BigUint::from_bytes_le(&issuer_pk.0.to_bytes_le()).to_str_radix(16));
    let pky = format!("0x{}", num_bigint::BigUint::from_bytes_le(&issuer_pk.1.to_bytes_le()).to_str_radix(16));
    let provided = longfellow_zk::mdoc::v1::provider::materialize(7, req_attrs.len()).unwrap();
    let spec = &provided.spec;
    let circuits_lfa2 = longfellow_zk::mdoc::artifacts::load_circuit_lfa2(&spec.combined_hash_hex());
    if mode == "prove" {
        let mut rng = longfellow_zk::runtime::random::DeterministicRng::new(42);
        let proof = run_mdoc_prover_inner(spec, &circuits_lfa2, mdoc_bytes, &pkx, &pky, transcript,
                                          &req_attrs, now, doc_type, &mut rng).unwrap();
        std::fs::write(file, &proof).unwrap();
        println!("proof {} bytes", proof.len());
    } else {
        let proof = std::fs::read(file).unwrap();
        run_mdoc_verifier_inner(spec, &circuits_lfa2, &pkx, &pky, transcript, &req_attrs, now,
                                doc_type, &proof).unwrap();
        println!("verified");
    }
}
