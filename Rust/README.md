# orisnik

A Rust port of [Oris](https://github.com/PCfVW/oris) — a Rust and Zig port of Dimitar Lazarov's **HPHA** (2007): a single-threaded heap allocator combining a size-class bucket allocator for small allocations with a red-black-tree best-fit allocator for large ones.

[![crates.io](https://img.shields.io/crates/v/orisnik?logo=rust)](https://crates.io/crates/orisnik)
[![docs.rs](https://img.shields.io/docsrs/orisnik?logo=docsdotrs)](https://docs.rs/orisnik)
[![Rust CI](https://github.com/PCfVW/oris/actions/workflows/rust-ci.yml/badge.svg)](https://github.com/PCfVW/oris/actions/workflows/rust-ci.yml)
[![MSRV](https://img.shields.io/badge/MSRV-1.85-blue?logo=rust)](https://github.com/PCfVW/oris/blob/main/Rust/Cargo.toml)
[![License](https://img.shields.io/crates/l/orisnik)](https://github.com/PCfVW/oris/blob/main/LICENSE-MIT)
[![Zig sibling: orisnitsa](https://img.shields.io/badge/zig%20sibling-orisnitsa-f7a41d?logo=zig)](https://github.com/PCfVW/oris/releases)

**The v0.1.0 implementation is complete in this repository and not yet published to crates.io** — the `0.0.0` release currently live on crates.io only reserves the name. Track the v0.1.0 release at <https://github.com/PCfVW/oris>.

## What's here

- A size-class **bucket allocator** for small allocations (up to 256 bytes), backed by fixed-size 64&nbsp;KiB OS pages.
- A red-black-tree **best-fit allocator** for everything larger, with physical-neighbour coalescing.
- Three public surfaces over one shared core:
  - **`oris_*`** — a C-shaped API (`oris_new`, `oris_alloc`, `oris_free`, `oris_realloc`, ...), instance-scoped via an explicit handle — never a hidden global.
  - **`unsafe impl GlobalAlloc`** — opt in as a `#[global_allocator]`.
  - **`unsafe impl core::alloc::Allocator`** — optional, behind the `nightly` Cargo feature, for `Box::new_in`/`Vec::new_in`.
- 80+ tests, most Miri-covered under `-Zmiri-strict-provenance -Zmiri-tree-borrows`.

## Quick start

```rust
use orisnik::Orisnik;

#[global_allocator]
static ALLOCATOR: Orisnik = Orisnik::new();
```

`Orisnik::new()` is a `const fn`, so the `static` above const-evaluates at compile time — no `OnceLock`/`LazyLock` indirection needed. See [INSTALL.md](https://github.com/PCfVW/oris/blob/main/INSTALL.md) for build instructions and toolchain requirements.

The Zig sibling is `orisnitsa`. See the [project brief](https://github.com/PCfVW/oris/blob/main/BRIEF.md) for design rationale and the [roadmap](https://github.com/PCfVW/oris/blob/main/ROADMAP.md) for what ships in each version.

## License

Dual-licensed under [MIT](https://github.com/PCfVW/oris/blob/main/LICENSE-MIT) OR [Apache-2.0](https://github.com/PCfVW/oris/blob/main/LICENSE-APACHE), at your option.

## Development

- Exclusively developed with [Claude Code](https://claude.com/product/claude-code)
- `unsafe` soundness gated on [Miri](https://github.com/rust-lang/miri) (`-Zmiri-strict-provenance -Zmiri-tree-borrows`) as a required CI lane, not just a local dev-time check
- Coding discipline: [Grit-ORIS](https://github.com/PCfVW/oris/blob/main/Rust/CONVENTIONS.md), the allocator-specific extension of the [Amphigraphic](https://github.com/PCfVW/Amphigraphic-Strict) `Grit` conventions
