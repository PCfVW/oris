# The C++ oracle harness

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
