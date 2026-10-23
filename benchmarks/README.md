# Benchmarks

Where Oris stands against the allocators in use today — on the workloads it was built for,
and on the standard external suite. The protocol is in [`methodology.md`](methodology.md);
the numbers are in [`results/`](results/).

| | |
|---|---|
| [`methodology.md`](methodology.md) | what is measured, how, and how to read it |
| [`results/v0.3.0/`](results/v0.3.0/README.md) | the v0.3.0 results — [what they say](results/v0.3.0/README.md), and [the tables](results/v0.3.0/SUMMARY.md): trace replay on Windows and Linux (WSL2), mimalloc-bench on Linux |
| [`traces.toml`](traces.toml), [`trace-checksums.txt`](trace-checksums.txt) | the trace corpus: every trace's generator and seed, and the bench traces' SHA-256s |
| [`scripts/tracegen/`](scripts/tracegen/) | generates and verifies the traces |
| [`scripts/bench-rust/`](scripts/bench-rust/), [`scripts/bench-zig/`](scripts/bench-zig/) | replay a trace through one allocator, one measurement pass per process |
| [`scripts/run.sh`](scripts/run.sh), [`scripts/run.ps1`](scripts/run.ps1), [`scripts/env.*`](scripts/) | run every cell and record the environment |
| [`scripts/aggregate/`](scripts/aggregate/) | turns the raw records into `SUMMARY.md` |
| [`scripts/purge-ablation.py`](scripts/purge-ablation.py) | diagnosis: every bench trace with and without its `purge` operations, per-category timings, OS-mapping counts ([results](results/v0.3.0/README.md#without-purge-the-ablation)) |
| [`mimalloc-bench/`](mimalloc-bench/) | Oris's two `LD_PRELOAD` shims and the pinned mimalloc-bench integration |

The trace corpus also drives the cross-port invariant check (the CI tier of
`traces.toml`, under [`examples/traces/`](../examples/traces/)); see
[`docs/traces.md`](../docs/traces.md).
