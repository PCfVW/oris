# Changelog

All notable changes to Oris are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Both ports ship in lockstep: one version number covers `orisnik` (crates.io) and
`orisnitsa` (GitHub Release), carrying the same feature set and the same internal
state transitions (see [`ROADMAP.md`](ROADMAP.md)).

## [Unreleased]

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
- Project scaffolding ahead of the v0.1.0 allocator implementation:
  - Rust (`orisnik`, edition 2024 / MSRV 1.85) and Zig (`orisnitsa`, 0.16.0) stub
    packages that build and test green.
  - `Grit-ORIS` coding conventions and AI-assist wiring (`CLAUDE.md`) for both ports.
  - CI for both ports (3-OS matrix; Rust adds a Miri soundness lane) with aggregator
    gate checks, crates.io **Trusted Publishing**, and a re-rooted Zig release asset
    with a recorded `zig fetch` hash.
  - `INSTALL.md`, `SECURITY.md`, README badges, Dependabot, and the Rust lint floor.

<!-- On cutting v0.1.0, add a dated section and move the shipped items here:
## [0.1.0] - YYYY-MM-DD
-->
