// Cross-verification of an mDoc proof made by longfellow-spark with
// upstream's mDoc verifier (ADR 0058, block 5): run_mdoc_verifier_inner
// of rust/applications/mdoc_zk/runtime at d5e6be7 on the proof file,
// under the parameters of the test case the witness files of
// tests/vectors/upstream/mdoc/ come from (FAMILYNAME_MUSTERMANN_MDOC_3
// of testcases/src/vectors.rs: the attribute family_name with the text
// value "Mustermann").
//
// Built as an example of the runtime crate, like scripts/measure/heap_v7.rs:
//
//     git clone https://github.com/longfellow-zk/longfellow-zk upstream
//     git -C upstream checkout d5e6be77336933d50bf7f25a954f8ec273eb51ce
//     mkdir -p upstream/rust/applications/mdoc_zk/runtime/examples
//     cp tests/vectors/upstream/verify_mdoc.rs upstream/rust/applications/mdoc_zk/runtime/examples/
//     cd upstream/rust
//     cargo run --release -p mdoc-zk-runtime --example verify_mdoc -- 7 <longfellow-spark>/cli/out/mdoc_v7_proof.bin
//     cargo run --release -p mdoc-zk-runtime --example verify_mdoc -- 6 <longfellow-spark>/cli/out/mdoc_v6_proof.bin
//
// The first argument is the circuit version of the archive the proof was
// made for (7 or 6, one attribute); the second the proof file. The
// program exits with status 0 and prints "accepted" only if upstream's
// verifier accepts; a refusal is a panic with upstream's error code. The
// library is not modified.
use mdoc_zk_runtime::{req_attr, run_mdoc_verifier_inner, RequestedAttribute, ZK_SPECS};

fn hex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        eprintln!("usage: verify_mdoc <7|6> PROOF_FILE");
        std::process::exit(2);
    }
    let version: usize = args[1].parse().expect("the version is 7 or 6");
    let proof = std::fs::read(&args[2]).expect("the proof file");
    let case = &mdoc_zk_testcases::vectors::FAMILYNAME_MUSTERMANN_MDOC_3;
    let spec = ZK_SPECS
        .iter()
        .find(|s| s.version == version && s.num_attributes == 1)
        .expect("a specification with one attribute at that version");
    let circuits = mdoc_zk_artifacts::load_circuit_lfa2(&spec.combined_hash_hex());
    let attrs: Vec<RequestedAttribute> = vec![req_attr(
        "org.iso.18013.5.1",
        "family_name",
        hex("6a4d75737465726d616e6e"),
    )];
    run_mdoc_verifier_inner(
        spec,
        &circuits,
        case.pkx,
        case.pky,
        case.transcript,
        &attrs,
        case.now,
        case.doc_type,
        &proof,
    )
    .expect("upstream's mDoc verifier refuses the proof");
    println!(
        "verify_mdoc: {} ({} bytes) accepted by upstream's run_mdoc_verifier, version {}",
        args[2],
        proof.len(),
        version
    );
}
