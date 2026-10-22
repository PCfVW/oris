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
  set.

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
