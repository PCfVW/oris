# Changelog

All notable changes to Oris are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Both ports ship in lockstep: one version number covers `orisnik` (crates.io) and
`orisnitsa` (GitHub Release), carrying the same feature set and the same internal
state transitions (see [`ROADMAP.md`](ROADMAP.md)).

## [Unreleased]

## [0.1.1] - 2026-08-29

A fidelity-and-soundness patch. Every change below either restores agreement with
`Cpp/hpha.h`/`hpha.cpp` or removes undefined behaviour, so all of it ships as a patch
under the *Fidelity fixes are patches* rule now recorded in
[`ROADMAP.md`](ROADMAP.md#fidelity-fixes-are-patches). No input that previously
behaved correctly changes. Both ports carry every fix, as the cross-port invariant
requires; findings are numbered as in
[`docs/audits/2026-08-29-pre-v0.2.0-audit.md`](docs/audits/2026-08-29-pre-v0.2.0-audit.md).

### Fixed

- **F1 — unchecked size arithmetic silently under-allocated on very large requests.**
  Every tree-path request passed through `round_up(size, 16)`, a bare mask with no
  overflow check, so `alloc(usize::MAX)` wrapped to a *zero-byte* block in a release
  build and panicked in `align.rs`/`std.mem.alignForward` in a checked one. Both ports
  now decline any request above a new `tree::MAX_ALLOCATION` / `tree.MAX_ALLOCATION`
  (roughly `usize::MAX - 64 KiB`, derived from the headroom each rounding step on the
  path to a mapped arena needs) before that arithmetic runs. HPHA performs the same
  arithmetic unchecked; the bound is above any allocation a real machine could serve,
  so it only refuses requests upstream would have corrupted the heap over.
- **F1, `calloc` half — an overflowing `count * size` was fatal, not merely wrong.**
  `calloc` passed HPHA's unchecked product to both the allocation *and* the zero-fill,
  so `calloc(2, usize::MAX)` acquired a few bytes and then memset exabytes over them —
  a segfault in release, reproduced during the audit. Now `checked_mul` /
  `@mulWithOverflow`, returning null on overflow.
- **F3 — `purge()` under-reclaimed bucket pages relative to HPHA.** Both ports broke
  out of the page-list walk at the first *partially-used* page; HPHA's `bucket_purge`
  breaks only at the first *full* one and keeps walking. Because a bucket's page list
  is re-sorted only on the full↔not-full transition, an empty page can sit behind a
  partially-used one, and those pages were never returned to the OS. The walk now
  mirrors HPHA exactly, latching each node's successor before unlinking it.
- **F5 — a zero `alignment` aborted where HPHA accepts it.** HPHA's own precondition is
  `assert((alignment & (alignment-1)) == 0)`, which *passes* for zero, so upstream
  routes `alloc(size, 0)` and `realloc(ptr, size, 0)` to the unaligned path — and
  Lazarov's own `main.cpp` benchmark calls `realloc(ptr, 0, 0)`. v0.1.0 checked
  `is_power_of_two`/`isPowerOfTwo` instead, which rejects zero and aborted every
  debug/`ReleaseSafe` build on that call. Both ports now port the original expression
  verbatim, as `is_hpha_alignment` / `isHphaAlignment`. `free_with_size_aligned` /
  `freeWithSizeAligned` maps a zero alignment to `DEFAULT_ALIGNMENT` so it names the
  same bucket the allocation came from — pinned by a test over the whole
  `1..=MAX_SMALL_ALLOCATION` range.
- **F6 — a zero-length `realloc`/`remap` freed the block and then reported failure.**
  `GlobalAlloc::realloc(ptr, layout, 0)` and the `std.mem.Allocator` vtable's
  `remap(_, 0)`/`resize(_, 0)` forwarded to a `realloc` that frees, then surfaced the
  resulting null — which both interfaces define as "failed, your pointer is still
  live", inviting a double free from a caller that respects the contract. All three
  now decline without touching the block. (Both interfaces forbid a zero length, so
  this is a caller bug either way; the guard makes it a harmless one.)
- **F10 — a zero `orig_size` underflowed the size-class index.** `free_with_size(ptr, 0)`
  and both zero-size forms of `free_with_size_aligned` reached
  `bucket_spacing_function(0)` — `((0 + 7) >> 3) - 1` — which underflows to
  `usize::MAX` and indexes a 32-element array. No allocation can have an original size
  of 0 (`alloc(0)` returns null), so this is a caller bug; but the consequence was not
  uniform. `orisnik` was contained to a bounds-check panic by Rust's always-on slice
  check, while **`orisnitsa`'s `ReleaseFast` build has no bounds check and wrote out of
  bounds silently** — in the build users ship. All three entry points in both ports now
  recover through `free`'s pointer-based dispatch, which re-derives bucket-vs-tree
  ownership from the pointer and so releases the block correctly regardless of the bad
  size. Deliberately not an assert: the recovery is correct rather than a guess, and
  asserting would reproduce the F5 failure shape (aborts in checked builds, works in
  release). HPHA has the identical underflow and no bounds check at all.

### Changed

- **F4 — `Orisnik`/`Orisnitsa` document their address-stability contract, and debug
  builds enforce it.** Both types bind three pieces of state to the instance's own
  address on first use (two lazily self-linked sentinels plus every bucket page
  marker), so moving one after its first allocation silently breaks bucket/tree
  dispatch. That constraint was documented only inside the private `list`/`rbtree`
  modules; it is now an `# Address stability` section on each public type. Debug and
  `ReleaseSafe` builds latch the instance address on first use and trip a named
  assertion on the first operation after a move, instead of corrupting quietly;
  `ReleaseFast`/release pay one word of storage and no instructions. A `Pin`-based API
  that would enforce this at compile time is deferred to v0.2.0. HPHA's C++
  `allocator` carries the same implicit constraint (it defines no move constructor).
- `Buckets::ptr_in_bucket`'s debug cross-check now distinguishes its two possible
  causes: a false *positive* is the known HPHA-inherited marker collision, while a
  false *negative* means the owning allocator was moved (F4).
- `SECURITY.md`'s CWE-190/CWE-131 row described checked size arithmetic that did not
  exist in v0.1.0 (**F2**). F1 implements it; the row now matches the code, and the
  CWE-476 row records the one documented exception to "OOM is a value, never a panic".
- `ROADMAP.md` gains an explicit *Fidelity fixes are patches* rule under the versioning
  policy, with the two conditions a change must meet to qualify.
- **F7 — `Zig/CONVENTIONS.md` and `Zig/CLAUDE.md` named the wrong verification tool.**
  Both listed `std.testing.checkAllAllocationFailures` as covering allocation-failure
  paths. It cannot: that helper wraps a `FailingAllocator` around a *backing*
  `std.mem.Allocator` and passes it **to** the code under test, so it exercises
  allocator *consumers*. `Orisnitsa` consumes no allocator — it calls `os.map` directly
  — so there is nothing to wrap. It was correspondingly never used anywhere in `src/`.
  Both documents now describe the injection seam that actually fits, and say why.
- **F8 — `Cpp/NOTICE.md` claimed "Modifications: None".** The reference `hpha.h` in fact
  differs from the archived original on one line (`#define MULTITHREADED` commented out —
  a build-configuration choice matching both ports' single-threaded scope, not an
  algorithm edit). `hpha.cpp` is byte-identical. The NOTICE now records this in a table,
  declares which revision of the reference governs, and points at the new errata
  register.

### Added

- **[`Cpp/ERRATA.md`](Cpp/ERRATA.md)** — a register of defects found in the HPHA
  reference, split by what the ports actually do about each: fixed (E1–E5), deliberately
  preserved (E6–E7), unreachable through the ports' surface (E8), and already fixed by
  the author in a later revision (E9). Every entry carries a **Trace-visible** verdict —
  whether the v0.3.0 trace-corpus gate should expect the C++ oracle and the ports to
  disagree — so that gate has a list to work from instead of firing on each deviation.
  The register also records the evidence each fix met the *Fidelity fixes are patches*
  conditions.
- **E9, found while writing that register and open for v0.2.0:** the 2007 reference in
  `Cpp/` loses a live allocation's debug record when a `realloc` fails. Two of
  `realloc`'s three debug call sites pass a possibly-`NULL` `newPtr` into
  `debug_replace`, whose unconditional `*record = debug_record(newPtr, ...)` then
  overwrites the record of the still-live original block. The author fixed this himself
  in a 2012 revision (splitting `replace` into `replace_begin`/`replace_end`, guarded by
  `if (ptr)`), which is *not* the source this directory carries. Nothing to fix in
  v0.1.1 — no debug subsystem is ported yet — but v0.2.0 should port the 2012 form.
- **F7 — an out-of-memory injection seam, and coverage for every OOM path.** `os::map`
  had no failure seam, so every `?` / `orelse return null` on a `system_alloc` result in
  `Buckets` and `Tree` was unexecuted by any test — the OOM early-outs existed only on
  paper. `os::test_vm::fail_map_after` / `os.test_vm.failMapAfter` supplies one, and both
  ports now cover: OOM on all four alloc paths plus `calloc`, recovery once the OS stops
  refusing, and — the one with teeth — that a `realloc` which cannot grow reports failure
  **and leaves the original allocation live and intact**.
- **F9 — the entire public surface now runs under Miri (`orisnik`).** Miri cannot
  interpret `VirtualAlloc`/`mmap`, so before v0.1.1 every test that actually allocated
  was `#[cfg_attr(miri, ignore)]`: 22 allocator-path tests, including all of `Orisnik`,
  the `oris_*` C-ABI, `GlobalAlloc` and the `Allocator` trait, sat outside the soundness
  gate. `os::test_vm` now serves `map`/`unmap` from a `PAGE_SIZE`-aligned heap
  allocation **under Miri only** — a native `cargo test` still exercises the real
  syscalls, so this adds coverage rather than replacing it. Miri goes from **60 passed /
  32 ignored to 92 passed / 5 ignored**; the remaining five are `os.rs`'s own
  real-syscall tests and the manual oracle tool.
  - Nine tests gained a `purge()` they had been missing: with the stand-in backing
    `map`, pages the allocator holds until asked (matching HPHA) show up to Miri as
    still-live memory. That is the documented embedder contract, so calling `purge()`
    is both what a well-behaved caller does and a stronger assertion. `capi.rs`'s test
    now demonstrates the `oris_purge`-before-`oris_destroy` pattern `oris_destroy`'s own
    doc prescribes.
- **F9 — a randomized stress workload in both ports**, modelled on the shape of
  Lazarov's own `main.cpp` benchmark: 20 000 allocations at its `r^8`-skewed size
  distribution, freed in its randomized `i + rand() % (N - i)` order, with and without
  alignment — plus the assertions `main.cpp` never had. Every block is stamped with a
  fingerprint derived from its index and verified on free, so a block handed out twice
  or overlapping another fails loudly; `purge()` must then reclaim everything. Path
  coverage (~71% bucket, ~29% tree) is asserted so the workload cannot silently
  degenerate into a single-path test. This is the coverage class the suites had none of:
  the only randomized test in either port previously exercised the `RB-tree`, not the
  allocator. `orisnik` scales the workload down under Miri rather than skipping it
  there — Miri's cost is near-linear in the block count (measured at 22.9 s / 45.7 s /
  83.7 s / 149.9 s for 100 / 250 / 500 / 1000, i.e. `t ~= 8.8 + 0.141*N` s), so the
  full run would cost ~47 min while `N = 150` costs ~30 s and still puts a randomized
  alloc/free interleaving across both size paths under the soundness gate.
  - The generator is the **Microsoft C runtime's `rand()` LCG**, from Eric Jacopin's
    "Vintage RNGs" chapter (*Game AI Pro 3*) — verified bit-identical to the real CRT
    over 200 000 draws across five seeds before being relied on, and pinned in both
    ports by a golden vector from that chapter's own `srand(0)` corpus plus the
    `srand(1234)` seed `main.cpp` uses. Both ports therefore drive **one identical
    stream**, and a future three-way C++/Rust/Zig comparison (`ROADMAP.md`'s v0.3.0
    trace corpus) can generate Lazarov's exact sequence independently in each language
    rather than shipping recorded traces. The size distribution uses an integer
    analogue of `powf(r, 8.0f)` — deliberately, since float `pow` is not
    bit-reproducible across language runtimes.
- Regression tests for every finding above, in both ports: oversized and
  overflowing-product requests, the F3 page-list state (an empty page behind a
  partially-used one), zero-alignment accept/alloc/free round trips, the
  bucket-index agreement the zero-alignment free relies on, the
  raw-vtable/`GlobalAlloc` zero-length realloc guard, and the zero-`orig_size`
  recovery across all three entry points on both the bucket and tree paths.
  93 Rust tests (from 79) and 95 Zig tests (from 81).

## [0.1.0] - 2026-08-17

### Added

- The Rust port (`orisnik`) of HPHA's non-debug, single-threaded allocator
  (`DEBUG_ALLOCATOR`/`MULTITHREADED` remain out of scope, see `ROADMAP.md`):
  - Cross-platform VM layer, alignment helpers, and a tagged-pointer helper
    (`os.rs`, `align.rs`, `tag.rs`).
  - An intrusive doubly-linked list and red-black tree, both faithful ports of
    HPHA's `intrusive_list`/`intrusive_multi_rbtree` (`list.rs`, `rbtree.rs`),
    cross-validated against the reference C++ via a standalone oracle harness.
  - The block header and the bucket (small-allocation) and tree (large-allocation,
    best-fit + coalescing) sub-allocators (`block.rs`, `bucket.rs`, `tree.rs`).
  - The top-level `Orisnik` dispatcher plus its three public surfaces: the
    `oris_*` C-ABI, `unsafe impl GlobalAlloc` (opt-in `#[global_allocator]`), and
    an optional `unsafe impl core::alloc::Allocator` behind the nightly-only
    `nightly` Cargo feature (`orisnik.rs`, `capi.rs`, `global_alloc.rs`,
    `allocator_trait.rs`).
  - 80+ tests (60+ Miri-covered under `-Zmiri-strict-provenance
    -Zmiri-tree-borrows`), including a debug-only exhaustive-scan verification of
    `ptr_in_bucket`'s marker-based dispatch (mirroring HPHA's own `#ifndef
    NDEBUG` check) added after integration testing reproduced the false-positive
    HPHA's own comment already anticipates.
- The Zig port (`orisnitsa`) of the same HPHA slice, module-for-module mirroring
  `orisnik`:
  - Cross-platform VM layer, alignment helpers, and a tagged-pointer helper
    (`os.zig`, `align.zig`, `tag.zig`).
  - An intrusive doubly-linked list and red-black tree, both faithful ports of
    HPHA's `intrusive_list`/`intrusive_multi_rbtree` (`list.zig`, `rbtree.zig`),
    cross-validated against `orisnik`'s own already-C++-oracle-validated trace via
    a matching 3000-step operation trace (byte-for-byte identical).
  - The block header and the bucket (small-allocation) and tree (large-allocation,
    best-fit + coalescing) sub-allocators (`block.zig`, `bucket.zig`, `tree.zig`),
    including `ptr_in_bucket`'s debug-only exhaustive-scan verification from the
    start (ported ahead of the false-positive `orisnik` only added after
    integration testing).
  - The top-level `Orisnitsa` dispatcher plus its three public surfaces:
    `Orisnitsa`'s own methods, a `std.mem.Allocator` vtable (`resize` never
    moves, `remap` may — matching the vtable's own contract), and the `oris_*`
    C-ABI (`orisnitsa.zig`, `allocator.zig`, `capi.zig`).
  - 80+ tests, verified in `Debug`/`ReleaseSafe` (`std.testing.allocator` leak
    detection, runtime safety checks on) and `ReleaseFast`, on all three CI OSes —
    Zig's analog of the Rust port's Miri gate.
- A shared C header, [`include/oris.h`](include/oris.h), declaring the `oris_*` prototypes
  behind an opaque `OrisAllocator*` handle, identical for both ports, plus the build
  changes that make the `oris_*` C-ABI actually linkable by a real C/C++ caller instead
  of only compiled into each port's own test binary:
  - `orisnik`: `crate-type = ["lib", "cdylib", "staticlib"]` in `Cargo.toml` — `cargo build
    --release` now also emits `liborisnik.so`/`.dylib`/`orisnik.dll` and
    `liborisnik.a`/`orisnik.lib`.
  - `orisnitsa`: `build.zig` now builds static and shared library artifacts
    (`liborisnitsa.so`/`.dylib`/`.a`, or `orisnitsa.dll`/`.lib` on Windows) from a module
    rooted directly at `capi.zig` — Zig only auto-exports `export fn`s that live in a
    module's own root file, so rooting the library artifacts at `root.zig` (as initially
    tried) silently produced a library with no `oris_*` symbols at all; verified with
    `dumpbin /exports` and a real C smoke test linked against both the static and shared
    artifacts before landing.
- Project scaffolding ahead of the v0.1.0 allocator implementation:
  - Initial Rust (`orisnik`, edition 2024 / MSRV 1.85) and Zig (`orisnitsa`,
    0.16.0) package skeletons — `Cargo.toml`/`build.zig.zon` manifests, a green
    `cargo test`/`zig build test` baseline — ahead of either allocator core.
  - `Grit-ORIS` coding conventions and AI-assist wiring (`CLAUDE.md`) for both ports.
  - CI for both ports (3-OS matrix; Rust adds a Miri soundness lane) with aggregator
    gate checks, crates.io **Trusted Publishing**, and a re-rooted Zig release asset
    with a recorded `zig fetch` hash.
  - `INSTALL.md`, `SECURITY.md`, README badges, Dependabot, and the Rust lint floor.
- Release engineering ahead of the tag:
  - `RELEASING.md`, the release-ceremony checklist, plus tag↔manifest version
    consistency gates in both `rust-publish.yml` and `zig-release.yml`.
  - A cross-platform C-ABI smoke-test workflow (`c-abi-ci.yml`) that builds both
    ports' real linkable libraries and links a real C caller against each via
    `zig cc`; `oris.h` vendored into both packages with a CI drift check.
  - CI coverage for the `nightly` `Allocator`-trait feature (test + clippy),
    previously verified only locally; both release workflows' own gauntlets
    extended to match (Miri re-run on the exact tagged commit, `ReleaseFast`
    tests, a packaged-tarball build-test for the Zig release asset).
  - `Orisnik`'s single-threaded/UB-if-multithreaded contract published on its
    public type doc (previously only in a private module's comment).
  - The C++ oracle harness (`Cpp/oracle/`) behind the three-way RB-tree
    cross-validation, reconstructed and re-verified live: all 3000 steps match
    byte-for-byte across every C++/Rust/Zig pairing.

[Unreleased]: https://github.com/PCfVW/oris/compare/v0.1.1...HEAD
[0.1.1]: https://github.com/PCfVW/oris/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/PCfVW/oris/releases/tag/v0.1.0
