# orisnitsa

The Zig port of [Oris](https://github.com/PCfVW/oris) — a Rust and Zig port of Dimitar Lazarov's **HPHA** (2007).

[![Zig CI](https://github.com/PCfVW/oris/actions/workflows/zig-ci.yml/badge.svg)](https://github.com/PCfVW/oris/actions/workflows/zig-ci.yml)
[![Zig release](https://img.shields.io/github/v/release/PCfVW/oris?logo=zig&color=f7a41d)](https://github.com/PCfVW/oris/releases)
[![Zig](https://img.shields.io/badge/Zig-0.16.0-f7a41d?logo=zig)](https://ziglang.org/)
[![License](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue)](https://github.com/PCfVW/oris/blob/main/LICENSE-MIT)
[![Rust sibling: orisnik](https://img.shields.io/crates/v/orisnik?logo=rust&label=rust%20sibling)](https://crates.io/crates/orisnik)

**No implementation yet.** This stub establishes the `build.zig.zon` manifest and a green `zig build test` baseline while the design settles. The allocator core — the bucket and tree sub-allocators, the *orisnitsi* — lands in v0.1.0, in lockstep with the `orisnik` Rust crate (same version, same internal state transitions).

The Rust sibling is `orisnik`. See the [project brief](https://github.com/PCfVW/oris/blob/main/BRIEF.md) and [roadmap](https://github.com/PCfVW/oris/blob/main/ROADMAP.md).

## Requirements

Targets **Zig 0.16.0**, pinned in [`build.zig.zon`](build.zig.zon). The `std.mem.Allocator` vtable shape is version-sensitive while Zig is pre-1.0, so the pin is load-bearing.

## Conventions

This port follows [`CONVENTIONS.md`](CONVENTIONS.md) — the Zig dialect of the [Amphigraphic](https://github.com/PCfVW/Amphigraphic-Strict) `Grit-ORIS` discipline, sharing the cross-port-invariant rules with the Rust port (see the [roadmap](https://github.com/PCfVW/oris/blob/main/ROADMAP.md)).

## License

Dual-licensed under [MIT](https://github.com/PCfVW/oris/blob/main/LICENSE-MIT) OR [Apache-2.0](https://github.com/PCfVW/oris/blob/main/LICENSE-APACHE), at your option.
