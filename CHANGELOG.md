# Changelog

All notable changes to Oris are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Both ports ship in lockstep: one version number covers `orisnik` (crates.io) and
`orisnitsa` (GitHub Release), carrying the same feature set and the same internal
state transitions (see [`ROADMAP.md`](ROADMAP.md)).

## [Unreleased]

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

[Unreleased]: https://github.com/PCfVW/oris/compare/v0.1.0...HEAD
[0.1.0]: https://github.com/PCfVW/oris/releases/tag/v0.1.0
