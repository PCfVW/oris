# v0.3.0 results — what they say

The tables are in [`SUMMARY.md`](SUMMARY.md), generated from the raw records in this
directory; the protocol is in [`../../methodology.md`](../../methodology.md). This page is the
reading of them, measured 2026-10-22 on one machine (AMD Ryzen 9 5950X): Windows 11 natively
(32 logical cores), and Linux as Ubuntu 24.04 under WSL2 (4 logical cores and 8 GB given to the
VM). These are first results: one machine, defaults everywhere. Expect the ranking to hold
better than any single number.

## The two ports perform alike

On every trace and both platforms, `orisnik` and `orisnitsa` are within about 15% of each
other in time (typically under 10%), and their memory figures agree to the megabyte — as they
should, since the trace gate proves they perform the same transitions; the time gap is the
compiled code around the shared algorithm, not the algorithm. In mimalloc-bench the Zig shim
is slower on several rows (`alloc-test1`, `cfrac`, and the threaded `alloc-testN`,
`sh6bench`, `sh8bench`); that difference lies in the shim or the code around it, and is noted
here as unexplained rather than guessed at.

## Speed: mid-pack, and slow where Oris goes back to the OS

- **The modern allocators win on raw speed.** mimalloc is faster than Oris on every trace, by
  1.1× (`small`, Windows) to about 15× (`large`, Linux); snmalloc and jemalloc are faster on most,
  though on the `mixed` trace both come within 1.15–1.6× of Oris and behind glibc. (Both are
  measured on Linux only; see the methodology.)
- **Against the platform allocator it depends.** On Windows, Oris replays the `mixed` trace 4×
  faster than the system heap (165 ms vs 698 ms) and the `small` one 2× faster; on Linux, Oris
  is slightly faster than glibc on `small` (15.0 ms vs 16.5 ms) and slower on every other
  trace.
- **The cost is concentrated in `purge`.** The `planner` and `parser` workloads purge every few
  plans or files, as the brief's planner is meant to; each purge returns idle 64 KiB pages,
  which the next plan maps again. That OS round trip is where Oris's p99.9 latency on those
  traces goes (15–36 µs, where every other allocator stays under 0.5 µs on Linux and 3 µs on
  Windows), and much of its wall time — and it costs about
  twice as much under WSL2 as on native Windows. HPHA's lazy return is a design choice (`BRIEF.md`:
  "memory returned only on explicit `purge()`"); a planner that purged less often would pay
  less. The comparison is lopsided in Oris's disfavour here: for the other allocators `purge`
  is a no-op, so they neither pay for returning memory nor show its effect on their resident
  set. The next section measures how lopsided.

## Without purge: the ablation

Measured 2026-10-23 by [`../../scripts/purge-ablation.py`](../../scripts/purge-ablation.py):
the same protocol, once as published above and once with every `purge` of the trace skipped
(`bench-rust --no-purge`), for `orisnik`, the system allocator and mimalloc. The tables and
raw records are in [`purge-ablation/`](purge-ablation/) ([Windows](purge-ablation/windows-x86_64/summary.md),
[Linux](purge-ablation/linux-wsl2-x86_64/summary.md)).

**Wall time, ms (median of 10), with purge → without.** The other allocators do not change,
since for them `purge` was already a no-op:

| Trace | `orisnik` Windows | `orisnik` Linux | glibc Linux | mimalloc Linux |
|---|---|---|---|---|
| `planner` | 40.8 → **9.0** | 87.0 → **9.8** | 20.0 | 9.6 |
| `parser` | 36.4 → **9.2** | 72.3 → **10.1** | 17.3 | 10.6 |
| `small` | 13.3 → 12.3 | 15.3 → 12.5 | 17.4 | 12.6 |
| `mixed` | 153.5 → **55.5** | 540.1 → **59.5** | 225.9 | 51.8 |
| `large` | 248.5 → **91.3** | 604.7 → **90.8** | 368.8 | 42.9 |

- **Purge is most of Oris's time on these traces.** Without it, Oris beats glibc on every
  trace, matches mimalloc on `planner`, `parser` and `small` and comes within 1.15× of it on
  `mixed`. The p99.9 of its small allocations on `planner` falls from 38 µs to 61 ns (Linux).
- **The cost is not in `purge` itself, but in what follows it.** On `planner` the 47 purges
  take 5.7 ms (Windows); the small allocations after them take 23 ms more than without purge,
  because each one that finds its page gone maps a fresh one and builds it. The transition
  records count the round trips: `planner` maps and unmaps 1,505 pages with purge and maps 32
  without; `large` maps 2,682 tree arenas instead of 76.
- **Linux pays about 2.4× what Windows pays per round trip** (`planner`: 77 ms against 32 ms
  for the same 1,505 pages), which is why Oris looked so much slower on Linux. The
  virtualization in WSL2 is part of that; a native Linux run will say how much.
- **What purge buys is small on these traces:** peak resident growth falls by at most 9%
  (`large` 18.2 MiB against 19.9 MiB without), and fragmentation from 1.43 to 1.32. Purge
  pays off where a program's peak and steady state differ a lot, which these traces' cadence
  does not let it show: every 4 plans in `planner`, every 2 files in `parser`, about every
  2,000 operations in the synthetic traces.

The ablation does not change the published comparison, which measures what the traces ask
for. It says where the gap comes from, and that a caller who purges between levels rather
than between plans will not see most of it.

## Where the remaining time goes

Sampled with `samply` 0.13.1 at 10 kHz under WSL2, over 22 replays per run, symbolized
through the inline chains (`addr2line -i`):

- **The small-block path is not the problem.** `small`, and `planner` and `parser` without
  purge, replay as fast as mimalloc.
- **With purge, the cost is the OS.** On `planner`, 44% of the samples are on one line
  ([`bucket.rs`](../../../Rust/src/bucket.rs), the loop that threads a fresh bucket page's
  free list through all of its slots, taking every 4 KiB page's first-touch fault), 25% in
  `munmap` and 4% in `mmap`.
- **On large blocks, the best-fit tree.** On `large` without purge, Oris spends 2.7× mimalloc's
  samples inside the allocator. Of Oris's: the red-black tree 39% (descents, fixups,
  comparisons), block-header reads 31% (cache misses on headers scattered over a 20 MiB heap,
  read while coalescing and comparing), the tree glue 9%, pointer tags 6%. The tree itself is
  small (about 100 nodes, 125 at most); the cost is about 1.7 tree operations per free, since
  the freed block almost always merges with a neighbour, which leaves the tree, and the block it
  displaces from the most-recently-freed cache enters it. That is what best-fit with
  immediate coalescing costs, and what buys the fragmentation of 1.31 above.

What can be made faster without changing a single transition, and what would take departing
from HPHA, is planned in [`ROADMAP.md`](../../../ROADMAP.md) (v0.5.0, and beyond v1.0).

## Memory: lean on large blocks

- **Large and mixed workloads:** Oris's best-fit tree keeps fragmentation at 1.31–1.32
  (resident growth over peak live bytes), close to glibc and jemalloc (1.15–1.4) and well below
  mimalloc (2.4–4.2) — the coalescing best-fit allocator doing what the brief says it does.
- **Small allocations:** each size class takes its own 64 KiB page, so a heap of a few hundred
  KiB spread over many classes holds a few MiB (fragmentation 5–8 on `small` and `planner`). That
  is the page granularity, not waste that grows: it stays flat as the workload runs.
- **Aligned allocations:** Oris (10.3–10.5) and the system allocators (8–14) are comparable.
  jemalloc's fragmentation on this trace (about 300), and Zig's `smp_allocator`'s times on the
  large-block traces (seconds: its large path goes to the OS for every block), are outliers worth
  knowing about, not Oris findings.

## mimalloc-bench: fine single-threaded, serialized when threaded

- **Single-threaded programs** (cfrac, espresso, barnes, alloc-test1, glibc-simple, mleak):
  `orisnik` runs at 0.91–1.15× glibc's time and 0.96–1.45× its peak memory; `orisnitsa` at
  0.93–1.30×, except on `alloc-test1` (1.91×), unexplained so far.
- **Threaded programs** (marked † in the tables) run behind the shims' global lock, and pay for
  it: typically 5–20× glibc's time, up to 39× for `orisnik` (`larson`, where the figure is
  inverse throughput) and 67× for `orisnitsa` (`sh6bench`). These rows measure serialization, as the methodology warns; Oris is a
  single-threaded allocator until v2.x. (A few threaded tests show Oris using *less* memory —
  `xmalloc-test`, `larson` — because they run for a fixed time and a serialized allocator simply
  does less work in it.)
- **`malloc-large`:** Oris holds 2.7× glibc's peak RSS, because the shim never purges and Oris
  never returns memory on its own — the same lazy-return design, seen from the other side.

## Provenance notes

- Windows: commit `f35d79c`, clean. Linux and mimalloc-bench: commit `426a005`, recorded as
  "dirty" because WSL's git, reading the Windows checkout, sees CRLF line endings in files git
  stores as LF (`Cpp/hpha.*`, the licence files); no source file differs from the commit.
- The Linux trace-replay records were taken after fixing the Rust harness's resident-set
  sampling on Linux (commit `426a005`, which removed an 8 MiB per-measurement artifact); the
  Windows records were not affected by that bug.
- WSL2 is a virtual machine: its timings include virtualization, and its memory figures are
  the guest's view. A native Linux run is the obvious next measurement.
- The purge ablation: Windows at commit `e1913fc`, clean; Linux at `db3876e`, "dirty" for the
  same CRLF reason. Linux built `bench-rust` with its default features, Windows with
  `--no-default-features --features mimalloc`, as for the main results. The profiles were taken
  with the same harness built with `CARGO_PROFILE_RELEASE_DEBUG=line-tables-only`, and are not
  committed.
