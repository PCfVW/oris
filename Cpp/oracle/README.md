# The C++ oracle harness

Three tools that put the 2007 HPHA source itself next to the ports:

| Tool | What it checks | Where it runs |
|---|---|---|
| [`oracle_trace.cpp`](oracle_trace.cpp) (below) | the red-black tree alone, against both ports' trees | manually |
| [`main_c_abi.cpp`](main_c_abi.cpp) (below) | Lazarov's own benchmark, over either port's `oris_*` C ABI | manually |
| [`trace_replay.cpp`](trace_replay.cpp) (last section) | the whole allocator: HPHA's transition record for every trace of the corpus | CI (`trace-ci.yml`, Windows) |

`oracle_trace.cpp` is the C++ side of the three-way RB-tree cross-validation this
project's `CHANGELOG.md` and `Rust/src/rbtree.rs`/`Zig/src/rbtree.zig` refer to: it
links against the real, unmodified `../hpha.h`/`../hpha.cpp` and drives HPHA's own
`intrusive_multi_rbtree<T>` through the identical 3000-step PRNG-seeded
insert/erase sequence, printing the identical in-order trace format, as:

- Rust: `Rust/src/rbtree.rs`'s `#[ignore]`d
  `rbtree::tests::print_oracle_cross_validation_trace`
- Zig: `Zig/src/rbtree.zig`'s skipped-by-default
  `"oracle cross-validation trace (manual tool, not an assertion)"`

All three must produce byte-identical stdout across the full run for the cross-port
invariant's RB-tree slice (`ROADMAP.md`) to hold. This is a **manual verification
tool**, not part of this repo's CI: HPHA is Windows-only by `../hpha.h`'s own hard
`#error` outside `WIN32`, so it can only build where the other two ports' CI can't
meaningfully run it either.

## Build (Windows, MSVC)

From a Developer Command Prompt (or after running `vcvars64.bat`), from this
directory:

```sh
cl /EHsc /DWIN32 /I.. oracle_trace.cpp ..\hpha.cpp /Fe:oracle_trace.exe
```

`/DWIN32` is required explicitly — `cl` does not define bare `WIN32` on its own, and
`hpha.h` hard-errors without it.

This build **must not** define `_DEBUG` (e.g. via `/MTd`/`/MDd`, or an explicit
`/D_DEBUG`) — `../hpha.h:26-29`'s `#ifdef _DEBUG` / `#define DEBUG_ALLOCATOR` turns
`MEMORY_GUARD_SIZE` from 0 to 16 the moment it is, which shifts every size class and
every split relative to the non-debug allocator both ports compare against. The
command above builds clean of it by construction (plain `cl /EHsc`, no debug-CRT
switch); any other invocation of `oracle_trace.cpp`, and any harness added under
v0.2.0, must say the same explicitly rather than rely on the same accident.

## Run and cross-validate

```sh
.\oracle_trace.exe > cpp_trace.txt
```

Compare against a fresh run of each port's own oracle test:

```sh
# Rust, from Rust/ — extract the printed lines between "running 1 test" and the
# trailing "test ... ok" / "test result" summary:
cargo test --lib --release -- --ignored --nocapture rbtree::tests::print_oracle_cross_validation_trace

# Zig, from Zig/ — temporarily flip `run_oracle_trace` to `true` in
# rbtree.zig's oracle test, then:
zig test src/root.zig --test-filter "oracle cross"
# flip it back to `false` before committing; strip the "N/N ...)..." progress-line
# prefix Zig's test runner prepends to the very first trace line.
```

`cpp_trace.txt`'s lines end `\r\n` (MSVC's default text-mode stdio); the Rust/Zig
captures are `\n`-only — `diff --strip-trailing-cr` (or equivalent) before comparing,
same convention difference, not a real divergence.

## Verified

Re-run during this repo's v0.1.0 pre-release audit follow-up (2026-08-17): all 3000
steps matched byte-for-byte across all three pairings (C++↔Rust, C++↔Zig,
Rust↔Zig) — confirming the `CHANGELOG.md` claim live, not just by inspection of a
prior, unreproduced run.

---

## `main_c_abi.cpp`: Lazarov's own benchmark, ported to the oris\_\* C ABI

A different kind of tool from `oracle_trace.cpp` above: not a cross-language
comparison, but Lazarov's own `hpha-errata/main.cpp` benchmark (archived outside
this repo, referenced by the
[pre-v0.2.0 audit](../../docs/audits/2026-08-29-pre-v0.2.0-audit.md#on-running-lazarovs-maincpp))
mechanically ported onto `oris_*` — a real workload someone else designed, run
through an explicit `OrisAllocator*` handle instead of HPHA's global `gAllocator`.
`main.cpp` carries no assertions of its own; its only correctness signal is "did
not crash," which is exactly the confidence this buys: 512 Ki live allocations at
its `r^8`-skewed size distribution, freed in its randomized order, through every
`oris_alloc`/`oris_alloc_aligned`/`oris_realloc`/`oris_realloc_aligned`/
`oris_free*` entry point — plus one assertion beyond the original, that `oris_purge`
reclaims everything afterward.

Because `oris.h` is deliberately port-agnostic ("this header does not care which"),
the same `.cpp` file links against either port's real, released library — the same
pattern `tests/c-abi/smoke.c` uses in CI, just not CI itself: this needs MSVC, same
Win32-only reasoning as `oracle_trace.cpp` above (see also the audit's Option A,
which also drops `benchmark2()` — an operator-`new`/`delete` exposition that
exercises no allocator surface — and keeps the CRT/`_aligned_malloc` comparison arms
unmodified, since this is an MSVC-only tool already).

### Build and run (Windows, MSVC)

Build each port's real linkable library first:

```sh
# from Rust/
cargo build --release
# from Zig/
zig build
```

Then, from a Developer Command Prompt (or after `vcvars64.bat`), from the repo root
— link against whichever port's import library, and copy its DLL alongside the
resulting `.exe` before running (Windows resolves a DLL from the executable's own
directory first):

```sh
cl /EHsc /O2 /Fe:main_orisnik.exe Cpp\oracle\main_c_abi.cpp Rust\target\release\orisnik.dll.lib
copy Rust\target\release\orisnik.dll .
main_orisnik.exe

cl /EHsc /O2 /Fe:main_orisnitsa.exe Cpp\oracle\main_c_abi.cpp Zig\zig-out\lib\import\orisnitsa.lib
copy Zig\zig-out\bin\orisnitsa.dll .
main_orisnitsa.exe
```

Same `_DEBUG` caveat as `oracle_trace.cpp` above applies here in spirit, though this
tool never links `hpha.h`/`hpha.cpp` at all — it only exercises `oris_*`, and
neither port's v0.1.x non-debug allocator has a `MEMORY_GUARD_SIZE`-equivalent knob
yet. Once v0.2.0's debug allocator lands behind its own feature flag/`comptime`
bool, a build of this tool with that layer enabled is a different, separate
comparison from the one verified below, and should say so explicitly rather than
silently mix the two.

### Verified

Run 2026-09-28: both completed all six `benchmark1()` cases (2 Mi allocator calls
each) with exit code 0 and `allocated after purge: 0` — including the
aligned-realloc case's final loop, `realloc(ptr, 0, 0)`, which is the exact call
audit finding F5 blocked before v0.1.1.

Note on the build commands above: `cargo build --release` is optimized, but bare
`zig build` (no `-Doptimize=`) defaults to `Debug` — matching `c-abi-ci.yml`'s own
smoke-test build, so the commands above are reproducible as written, but it means
the two runs are **not** a fair speed comparison against each other (a `Debug`
Zig binary is expected to trail an optimized Rust one on every case; that is not a
finding about either allocator's design). Timings are incidental either way —
wall-clock comparison against `mimalloc-bench` is a v0.3.0 deliverable
(`ROADMAP.md`), not this tool's job. Pass `-Doptimize=ReleaseFast` to `zig build`
for a same-optimization-level run if that comparison matters to you — confirmed:
re-run against a `-Doptimize=ReleaseFast` `orisnitsa.dll`, still exit 0 and
`allocated after purge: 0`, and the per-case timings close to in line with the
`Debug`-vs-`--release` gap above, consistent with that gap being a build-mode
artifact rather than a real difference between the two allocators.

---

## `trace_replay.cpp`: the HPHA leg of the trace gate

The third kind of tool here, and the one CI runs: HPHA itself replaying an allocation
trace (`../../examples/traces/GRAMMAR.md`) and printing its **transition record**, the
same record `orisnik` (`cargo run --example replay --features trace`) and `orisnitsa`
(`zig build replay`) print. The committed `*.record` files next to every trace in
`../../examples/traces/` are this tool's output; `.github/workflows/trace-ci.yml` checks
that all three implementations still produce them, byte for byte. That is the cross-port
invariant (`../../ROADMAP.md`) verified against the specification, not only between the
two ports.

HPHA has no notion of a transition record, so the events have to come from inside it.
They do, without touching `../hpha.h`/`../hpha.cpp`:

- **`letopis.patch`** adds one `#include "letopis_hooks.h"` and, at each hook site, a
  statement that records an event, a tree branch or a rotation (40 added lines, nothing
  removed or changed), at exactly the places
  `../../examples/traces/EVENTS.md` lists. Every hook only *reports*: it reads a
  pointer or a size the surrounding code already has, so the patched allocator makes
  the same decisions as the original.
- **`letopis_hooks.h`** declares what those calls need; **`trace_replay.cpp`** defines
  it, and holds the trace parser, the semantic constraints, the address normalization
  and the record writer — ports of `Rust/src/letopis/` and `Zig/src/letopis_*.zig`,
  with the same error messages.
- **`build_trace_oracle.ps1`** copies the two reference files to a scratch directory
  outside the repository (normalizing their line endings to the committed LF), applies
  the patch there with `git apply --check` first, and builds. If HPHA's sources ever
  changed, the patch would stop applying and the build would say so.

### Build and run (Windows, MSVC)

From a Developer PowerShell (or after `vcvars64.bat`), from the repository root:

```powershell
$oracle = & Cpp/oracle/build_trace_oracle.ps1     # prints the executable's path
& $oracle examples/traces/handwritten/realloc-branches.trace
```

The build is the non-debug allocator by construction (no `_DEBUG`, no debug CRT — see the
`_DEBUG` caveat above), with HPHA's asserts left on: a trace that trips one is a finding.
Output is written in binary mode, so records end lines with LF like the ports' do.

### Regenerating the records

A record changes only when the allocator's behaviour or the record format does — a
change under the cross-port invariant, which lands in Rust, Zig and `letopis.patch`
together. After such a change, and after adding a trace, regenerate every record from
the oracle (never from a port) and check both ports against them:

```sh
for t in examples/traces/handwritten/*.trace examples/traces/generated/*.trace; do
  "$ORACLE" "$t" > "${t%.trace}.record"
done
```

### Verified

The traces under `rejected/` have no record: each must be refused, and its `.expected` file
holds the message all three replayers print (after the `replay: <path>: ` prefix).

Run 2026-10-22: the 12 hand-written traces and the 7 generated ones
(`../../benchmarks/traces.toml`, CI tier) — 54,710 record lines in all, every event
kind, 3,344 rotations — replay byte-identically on HPHA, `orisnik` and `orisnitsa`.
