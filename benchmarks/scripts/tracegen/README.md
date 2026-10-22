# tracegen

Seeded, reproducible allocation traces for Oris — the generated half of the trace corpus
(`../../../examples/traces/`) and the inputs of the benchmarks (`../../`). The format is
specified in [`examples/traces/GRAMMAR.md`](../../../examples/traces/GRAMMAR.md).

A standalone crate (not part of `orisnik`'s package), modelled on the priority-queue
project's `graphgen`.

## Determinism

Every trace is a pure function of its `[[trace]]` table in
[`benchmarks/traces.toml`](../../traces.toml) and of this crate's exactly-pinned
`rand`/`rand_chacha`: one `ChaCha8Rng::seed_from_u64(seed)` drives every choice. No
floating-point math library is involved (log-uniform sizes are drawn with integer
arithmetic), so the output is the same on every OS — CI's `tracegen verify` runs on
Linux, Windows and macOS against files generated on one machine.

Every trace is valid by construction: workloads write through a builder that only emits
operations satisfying GRAMMAR.md's semantic constraints, and each finished trace is
replayed through `orisnik` before it is written.

## Commands

Run from this directory (the default paths are relative to it):

```sh
cargo run --release -- generate              # both tiers + bench checksums
cargo run --release -- generate --tier ci    # just the committed corpus
cargo run --release -- verify                # nothing drifted
```

| Tier | Written to | Committed |
|---|---|---|
| `ci` (a few thousand operations) | `examples/traces/generated/<name>.trace` | yes, with its `.record` (from the C++ oracle) |
| `bench` (a million operations) | `benchmarks/traces/<name>.trace` | no — only `benchmarks/trace-checksums.txt` |

`verify` regenerates every trace in memory: a CI trace must equal its committed file byte
for byte, a bench trace must hash to its committed SHA-256.

## Workloads

| `workload` | What it models |
|---|---|
| `planner` | A GOAP-style best-first search: bursts of small plan nodes, state copies and preconditions; a doubling open list; pruned dead ends; occasional scratch buffers; everything released at the end of a plan; `purge` every four plans. The brief's canonical workload. |
| `parser` | A source buffer per file, a doubling token buffer, short-lived token strings, a tree of small nodes with growable child lists, a symbol table; torn down in reverse; `purge` every two files. |
| `synthetic` + `profile` | A steady-state live set churned at random: `small` (1–256 B), `large` (257 B–256 KiB), `mixed` (both, with reallocs and resizes), `aligned` (alignments 16–65536), `realloc` (mostly reallocs). |

## Adding a trace

1. Add a `[[trace]]` table to `benchmarks/traces.toml` (unique `name`, a new `seed`).
2. `cargo run --release -- generate`.
3. For a CI trace, generate its record with the C++ oracle (see
   [`Cpp/oracle/README.md`](../../../Cpp/oracle/README.md)) and check that both ports
   reproduce it (`docs/traces.md`).
4. Commit the trace, its record, and `benchmarks/trace-checksums.txt`.

Changing a generator changes its traces: `verify` fails until they are regenerated (and,
for the CI tier, their records too).
