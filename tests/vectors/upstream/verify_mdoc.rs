// Cross-verification of an mDoc proof made by longfellow-spark with
// upstream's mDoc verifier (ADR 0058, block 5; ADR 0086, block 6):
// run_mdoc_verifier_inner of rust/applications/mdoc_zk/runtime at
// d5e6be7 on the proof file, under the parameters of one of upstream's
// test cases (testcases/src/vectors.rs, ALL_TEST_CASES): by default the
// case the witness files of tests/vectors/upstream/mdoc/ come from
// (FAMILYNAME_MUSTERMANN_MDOC_3, "familyname_mustermann-mdoc[3].json":
// the attribute family_name with the text value "Mustermann"), or the
// case named on the command line with its requested attributes.
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
//     cargo run --release -p mdoc-zk-runtime --example verify_mdoc -- 7 <proof> "age_over_18-website-mdoc[5].json" age_over_18:f5
//
// The first argument is the circuit version of the archive the proof was
// made for (7 or 6, one attribute); the second the proof file; the third,
// optional, the name of the test case in ALL_TEST_CASES (the issuer's
// key, the session transcript, the date and the document type are the
// case's), followed by the requested attributes as ID:CBORHEX, at least
// one, under the namespace upstream's own tests use (org.iso.18013.5.1
// for an mDL, the document type otherwise). The program exits with
// status 0 and prints "accepted" only if upstream's verifier accepts; a
// refusal prints upstream's error and exits with status 3; any other
// status (a missing file, an unknown case, a panic) is a failure of the
// program, not a verdict. The library is not modified.
use mdoc_zk_runtime::{req_attr, run_mdoc_verifier_inner, RequestedAttribute, ZK_SPECS};

fn hex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 && args.len() < 5 {
        eprintln!("usage: verify_mdoc <7|6> PROOF_FILE [CASE_NAME ID:CBORHEX...]");
        std::process::exit(2);
    }
    let version: usize = args[1].parse().expect("the version is 7 or 6");
    let proof = std::fs::read(&args[2]).expect("the proof file");
    let case_name = if args.len() > 3 {
        args[3].as_str()
    } else {
        "familyname_mustermann-mdoc[3].json"
    };
    let case = mdoc_zk_testcases::vectors::ALL_TEST_CASES
        .iter()
        .find(|c| c.name == case_name)
        .unwrap_or_else(|| panic!("no test case named {}", case_name))
        .data;
    let ns = if case.doc_type.starts_with("org.iso.18013.5.1") {
        "org.iso.18013.5.1"
    } else {
        case.doc_type
    };
    let attrs: Vec<RequestedAttribute> = if args.len() > 4 {
        args[4..]
            .iter()
            .map(|a| {
                let (id, value) = a.split_once(':').expect("an attribute is ID:CBORHEX");
                req_attr(ns, id, hex(value))
            })
            .collect()
    } else {
        vec![req_attr(ns, "family_name", hex("6a4d75737465726d616e6e"))]
    };
    let spec = ZK_SPECS
        .iter()
        .find(|s| s.version == version && s.num_attributes == attrs.len())
        .expect("a specification with that many attributes at that version");
    let circuits = mdoc_zk_artifacts::load_circuit_lfa2(&spec.combined_hash_hex());
    if let Err(e) = run_mdoc_verifier_inner(
        spec,
        &circuits,
        case.pkx,
        case.pky,
        case.transcript,
        &attrs,
        case.now,
        case.doc_type,
        &proof,
    ) {
        eprintln!(
            "verify_mdoc: {} refused by upstream's run_mdoc_verifier: {:?}",
            args[2], e
        );
        std::process::exit(3);
    }
    println!(
        "verify_mdoc: {} ({} bytes) accepted by upstream's run_mdoc_verifier, version {}",
        args[2],
        proof.len(),
        version
    );
}
