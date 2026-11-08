# The peak heap, measured the same way on both sides

The memory milestone (ADR 0080) compares the peak heap of this project's prover and verifier with upstream's, by one measure: the bytes allocated at the peak of each process, counted by the same interposer on both sides. The two files here are that tooling. The numbers in `docs/guide/performance.md`, "Memory", come from them.

## `heapshim.c`: the counter

A shared object loaded with `LD_PRELOAD` on Linux (glibc). It wraps `malloc`, `calloc`, `realloc`, `free` and the aligned allocators, adds the usable size of every block alive, and at exit appends one line to the file `HEAPSHIM_OUT` names (or to standard error): the program's name, the peak and the bytes still allocated. Single-threaded programs; both sides are.

```
gcc -O2 -shared -fPIC -o heapshim.so scripts/measure/heapshim.c
```

The counter measures what the program asked for, not what the operating system keeps resident: the maximum resident set that `scripts/measure-mdoc.sh` prints beside the times is a different quantity, larger by the allocator's own pages and the binary.

## Our side

The release build, then the four runs of `measure-mdoc.sh` under the counter; one line per process in the peaks file, the prover and the verifier of each circuit.

```
LONGFELLOW_CLI_BUILD=proved make cli
HEAPSHIM_OUT=peaks.txt LD_PRELOAD=$PWD/heapshim.so scripts/measure-mdoc.sh v7
```

## `heap_v7.rs`: upstream's side

A driver of forty lines for upstream's mDoc runtime at the pinned commit: `heap_v7 prove FILE` writes one proof of the version 7 flow (both circuits, one attribute, the test data of the repository), `heap_v7 verify FILE` checks it. The setup is that of upstream's `benches/mdoc_zk_bench_v7.rs`. It is built as an example of the runtime crate, with the generic field arithmetic and the baseline processor target, so that the comparison is of the algorithms and not of the vector units:

```
git clone https://github.com/longfellow-zk/longfellow-zk upstream
git -C upstream checkout d5e6be77336933d50bf7f25a954f8ec273eb51ce
mkdir -p upstream/rust/applications/mdoc_zk/runtime/examples
cp scripts/measure/heap_v7.rs upstream/rust/applications/mdoc_zk/runtime/examples/
cd upstream/rust
RUSTFLAGS="-C target-cpu=x86-64" cargo build --release -p mdoc-zk-runtime --example heap_v7 \
   --features runtime-algebra/force-generic-arch
HEAPSHIM_OUT=up-peaks.txt LD_PRELOAD=/path/to/heapshim.so target/release/examples/heap_v7 prove up-proof.bin
HEAPSHIM_OUT=up-peaks.txt LD_PRELOAD=/path/to/heapshim.so target/release/examples/heap_v7 verify up-proof.bin
```

Upstream's one process proves, or verifies, both circuits; ours is one process per circuit. The comparison in the performance page puts our hash circuit alone against upstream's pair, which is the conservative side.

## How the series were run

One session of the proving machine (`c4-standard-24`, ADR 0060), the toolchain of `alire.toml`, rustc 1.99.1 for upstream; three runs per commit, the peaks identical from run to run, the times the median of the three (ADR 0067). The proofs are compared byte for byte before and after each change.

## `heap_v7_single_crate.rs`: upstream's side at a commit newer than the pin

Upstream's commit 759b94a (October 2026) refactored its Rust implementation into one crate, `longfellow-zk`, and split the mDoc runtime into `v1`, the Longfellow this project implements, and `v2`. The driver above no longer compiles there. This file is the same forty lines for the single crate: the same test data, the same archive, the same seed, the same LFA2 format, so that a proof it makes compares byte for byte with the pinned driver's. It is built as an example of the crate, with its `testonly` feature for the test data and the deterministic randomness, and the generic arithmetic:

```
git -C upstream checkout <commit>
mkdir -p upstream/rust/examples
cp scripts/measure/heap_v7_single_crate.rs upstream/rust/examples/heap_v7.rs
cd upstream/rust
MEASURE_UPSTREAM=<commit> RUSTFLAGS="-C target-cpu=x86-64" cargo build --release --example heap_v7 \
   --features testonly,force-generic-arch
```

The runs are as above. The first use is the series of #128 on the performance page, "Upstream at a newer commit".
