#!/usr/bin/env python3
"""Tests of attribute-steps.py: recorded call stacks, written as `perf
script` prints them, and the step and circuit each must go to.

Run: python3 -I scripts/measure/attribute-steps-test.py
"""

import importlib.util
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
SCRIPT = os.path.join(HERE, "attribute-steps.py")
spec = importlib.util.spec_from_file_location("attribute_steps", SCRIPT)
a = importlib.util.module_from_spec(spec)
spec.loader.exec_module(a)

#  Frame names as perf prints them for upstream at 1c06629, innermost
#  first, with the crate hashes of the v0 scheme.
LZ = "longfellow_zk[e83b98cdbc7b5989]::"
GF = LZ + "runtime::algebra::gf2_128::Gf2_128Field"
FP = (LZ + "runtime::algebra::fp_generic::FpGenericField<4, 4, 9, "
      + LZ + "runtime::algebra::p256::P256Tag>")
MAIN = ["heap_v7[bf9e862fc4aeb1b3]::main", "main"]
PROVER = [LZ + "mdoc::runtime::v1::prover::run_mdoc_prover_inner::<x>"] + MAIN
VERIFIER = [LZ + "mdoc::runtime::v1::verifier::run_mdoc_verifier_inner"] + MAIN

CASES = [
    # (side, program, frames innermost first, step, circuit)
    ("upstream-single", "verify",
     [LZ + "runtime::algebra::arch::generic::clmul64",
      "<" + LZ + "runtime::sumcheck_v1::hquad::HQuad<2, " + GF + ">>::bind_g",
      LZ + "runtime::sumcheck_v1::verifier::derive_verifier_data::<2, " + GF + ">",
      "<" + LZ + "runtime::zk_v1::verifier::ZkVerifier<2, " + GF + ">>::verify"] + VERIFIER,
     "VS5-VS6", "hash"),
    ("upstream-single", "verify",
     [LZ + "runtime::sumcheck_v1::symbolic::verify::<4, " + FP + ">",
      "<" + LZ + "runtime::zk_v1::verifier::ZkVerifier<4, " + FP + ">>::verify"] + VERIFIER,
     "VS5-VS6", "sig"),
    ("upstream-single", "verify",
     [LZ + "runtime::zk_v1::constraint_compiler::compile::<2, " + GF + ">"] + VERIFIER,
     "VS5-VS6", "hash"),
    ("upstream-single", "verify",
     ["<" + LZ + "runtime::zk_v1::verifier::ZkVerifier<2, " + GF + ">>::verify"] + VERIFIER,
     "VS4", "hash"),
    ("upstream-single", "verify",
     ["ZSTD_decompressStream", LZ + "mdoc::runtime::v1::circuits::decompress_circuits"] + VERIFIER,
     "VS1", "both"),
    ("upstream-single", "prove",
     [LZ + "mdoc::artifacts::load_circuit_lfa2"] + MAIN,
     "PS1", "both"),
    ("upstream-single", "prove",
     ["<" + LZ + "mdoc::runtime::v1::proto::MdocProof<" + GF + ">>::write"] + PROVER,
     "PS11", "hash"),
    #  A store through a pointer is not the proof's writing: it takes the
    #  step of the root above it.
    ("upstream-single", "prove",
     ["core::ptr::write::<" + GF + ">",
      "<alloc::vec::Vec<u8>>::push",
      LZ + "runtime::sumcheck_v1::prover::prove_core::<2, " + GF + ">"] + PROVER,
     "PS8", "hash"),
    ("upstream", "prove",
     ["core::ptr::write::<runtime_algebra::gf2_128::Gf2_128Field>",
      "runtime_sumcheck[1a2b3c4d5e6f7a8b]::prover::prove_core::<2, runtime_algebra::gf2_128::Gf2_128Field>",
      "mdoc_zk_runtime[1a2b3c4d5e6f7a8b]::prover::run_mdoc_prover_inner::<x>"] + MAIN,
     "PS8", "hash"),
    ("upstream", "prove",
     ["<mdoc_zk_runtime[1a2b3c4d5e6f7a8b]::proto::MdocProof<runtime_algebra::gf2_128::Gf2_128Field>>::write",
      "mdoc_zk_runtime[1a2b3c4d5e6f7a8b]::prover::run_mdoc_prover_inner::<x>"] + MAIN,
     "PS11", "hash"),
    #  ::write is PS11 only under the prover's run; elsewhere the program.
    ("upstream-single", "prove",
     ["<" + LZ + "mdoc::runtime::v1::proto::MdocProof<" + GF + ">>::write"] + MAIN,
     "program", "both"),
    ("upstream-single", "prove",
     [LZ + "runtime::sumcheck_v1::symbolic::verify::<2, " + GF + ">",
      "<" + LZ + "runtime::zk_v1::prover::ZkProver<2, " + GF + ">>::prove"] + PROVER,
     "PS9", "hash"),
    ("upstream-single", "prove",
     ["<" + LZ + "runtime::zk_v1::prover::ZkProver<4, " + FP + ">>::prove"] + PROVER,
     "PS7", "sig"),
    ("upstream-single", "prove",
     ["memcpy", "[unknown]"],
     "not attributed", "both"),
    #  The crate names of d5e6be7 are not roots of the single crate, and
    #  the reverse.
    ("upstream-single", "verify",
     ["symbolic_sumcheck_verifier_core", "[unknown]"],
     "not attributed", "both"),
    ("upstream", "verify",
     [LZ + "runtime::sumcheck_v1::verifier::derive_verifier_data", "[unknown]"],
     "not attributed", "both"),
    ("upstream", "verify",
     ["runtime_zk[1a2b3c4d5e6f7a8b]::symbolic_sumcheck_verifier::symbolic_sumcheck_verifier_core::<2, runtime_algebra::gf2_128::Gf2_128Field>"]
     + ["mdoc_zk_runtime::verifier::run_mdoc_verifier_inner"] + MAIN,
     "VS5-VS6", "hash"),
]


def perf_text(stacks):
    out = []
    for n, frames in enumerate(stacks):
        out.append("heap_v7 20787 %d.000000: cpu-clock: " % n)
        for i, f in enumerate(frames):
            out.append("\t    %x %s (/bin/heap_v7)" % (0x1000 + i, f))
        out.append("")
    return "\n".join(out) + "\n"


def main():
    failures = 0
    for side, prog, frames, step, circuit in CASES:
        roots, program = a.SIDES[side]
        got = a.attribute(frames, roots[prog], program, side)[:2]
        if got != (step, circuit):
            failures += 1
            print("FAIL %s %s %s: %s, expected %s" % (side, prog, frames[0], got, (step, circuit)))
    #  The same stacks through perf_stacks and the command line.
    with tempfile.TemporaryDirectory() as d:
        path = os.path.join(d, "verify.txt")
        stacks = [c[2] for c in CASES if c[0] == "upstream-single" and c[1] == "verify"]
        with open(path, "w") as f:
            f.write(perf_text(stacks))
        r = subprocess.run([sys.executable, "-I", SCRIPT, "upstream-single", "verify", "time", path],
                           capture_output=True, text=True)
        lines = r.stdout.splitlines()
        for want in ("VS5-VS6\thash\t2\t", "VS5-VS6\tsig\t1\t", "VS4\thash\t1\t", "VS1\tboth\t1\t",
                     "not attributed\tboth\t1\t", "total\t\t6\t"):
            if r.returncode != 0 or not any(l.startswith(want) for l in lines):
                failures += 1
                print("FAIL command line: no line %r in\n%s%s" % (want, r.stdout, r.stderr))
        r = subprocess.run([sys.executable, "-I", SCRIPT, "upstream-v3", "verify", "time", path],
                           capture_output=True, text=True)
        if r.returncode != 2:
            failures += 1
            print("FAIL an unknown side gives exit %d, expected 2" % r.returncode)
    print("attribute-steps: %d cases, %d failures" % (len(CASES) + 7, failures))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
