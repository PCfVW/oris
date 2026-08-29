# Oris

*A high-performance heap allocator, after the folk-allotters of fate.*

A Rust and Zig port of Dimitar Lazarov's **HPHA** (2007).

[![Rust CI](https://github.com/PCfVW/oris/actions/workflows/rust-ci.yml/badge.svg)](https://github.com/PCfVW/oris/actions/workflows/rust-ci.yml)
[![Zig CI](https://github.com/PCfVW/oris/actions/workflows/zig-ci.yml/badge.svg)](https://github.com/PCfVW/oris/actions/workflows/zig-ci.yml)
[![crates.io](https://img.shields.io/crates/v/orisnik?logo=rust&label=orisnik)](https://crates.io/crates/orisnik)
[![Zig release](https://img.shields.io/github/v/release/PCfVW/oris?logo=zig&label=orisnitsa&color=f7a41d)](https://github.com/PCfVW/oris/releases)
[![docs.rs](https://img.shields.io/docsrs/orisnik?logo=docsdotrs)](https://docs.rs/orisnik)
[![MSRV](https://img.shields.io/badge/MSRV-1.85-blue?logo=rust)](Rust/Cargo.toml)
[![Zig](https://img.shields.io/badge/Zig-0.16.0-f7a41d?logo=zig)](https://ziglang.org/)
[![License](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue)](#license)

**Document revision 0.4. v0.1.1 has shipped: both the `orisnik` (Rust) and `orisnitsa` (Zig) allocator cores are released, in lockstep.**

## Status

- **`orisnik` (Rust)** — v0.1.1 is released: the bucket (small-allocation) and red-black-tree best-fit (large-allocation) sub-allocators, plus the three public surfaces (`oris_*` C-ABI, `GlobalAlloc`, an optional `Allocator` trait). 94 tests, the entire public surface Miri-covered. See [Rust/README.md](Rust/README.md) for details and [CHANGELOG.md](CHANGELOG.md) for what shipped.
- **`orisnitsa` (Zig)** — v0.1.1 is released: the same bucket and red-black-tree best-fit sub-allocators, plus the three public surfaces (`Orisnitsa`'s own methods, a `std.mem.Allocator` vtable, the `oris_*` C-ABI). 96 tests, verified in Debug/ReleaseSafe/ReleaseFast across all three OSes — Zig's analog of the Rust port's Miri gate. See [Zig/README.md](Zig/README.md) for details and [CHANGELOG.md](CHANGELOG.md) for what shipped.
- Both ports **ship in lockstep** (see [Versioning policy](ROADMAP.md#versioning-policy)): one version number means the same feature set and the same internal state transitions on both sides. See [RELEASING.md](RELEASING.md) for the checklist that cuts each release.

The two foundational documents:

- **[BRIEF.md](BRIEF.md)** — design rationale, etymological grounding, target workloads, prior-art positioning
- **[ROADMAP.md](ROADMAP.md)** — milestones, versioning policy, the cross-language invariant

## Structure

- **[Cpp/](Cpp/)** — the canonical HPHA reference source from 2007, included for diff and reference purposes. See [Cpp/NOTICE.md](Cpp/NOTICE.md) for the license trail.
- **[Rust/](Rust/)** — the `orisnik` crate (targets Rust 1.85 / edition 2024), released at v0.1.1 on crates.io.
- **[Zig/](Zig/)** — the `orisnitsa` module (targets Zig 0.16.0), released at v0.1.1 as a GitHub Release asset.
- **[.github/workflows/](.github/workflows/)** — CI for both ports (3-OS matrix; Rust adds a Miri soundness lane) plus tag-driven publishing: crates.io via Trusted Publishing, and a re-rooted Zig release asset — both fire off the same `vX.Y.Z` tag.

## Coding conventions

Both ports follow the [Amphigraphic](https://github.com/PCfVW/Amphigraphic-Strict) `Grit`
discipline, extended for a high-performance heap allocator (`Grit-ORIS`):

- **[Rust/CONVENTIONS.md](Rust/CONVENTIONS.md)** — `orisnik`
- **[Zig/CONVENTIONS.md](Zig/CONVENTIONS.md)** — `orisnitsa`

The two share the cross-port-invariant discipline (see [ROADMAP.md](ROADMAP.md)): an identical
public alloc/free sequence must produce identical internal state transitions across both ports.
The `CLAUDE.md` files (repo root and one per port) wire these conventions into AI-assisted edits.

## License

Dual-licensed under [MIT](LICENSE-MIT) OR [Apache-2.0](LICENSE-APACHE), at your option — see [LICENSE](LICENSE).

The HPHA reference source under `Cpp/` retains its original 2007 copyright header verbatim and is included under the same dual license, consistent with the public license trail established by the [Open 3D Engine](https://github.com/o3de/o3de) project. See [Cpp/NOTICE.md](Cpp/NOTICE.md) for full provenance.
