# orisnitsa

The Zig port of [Oris](https://github.com/PCfVW/oris) — a Rust and Zig port of Dimitar Lazarov's **HPHA** (2007): a single-threaded heap allocator combining a size-class bucket allocator for small allocations with a red-black-tree best-fit allocator for large ones.

[![Zig CI](https://github.com/PCfVW/oris/actions/workflows/zig-ci.yml/badge.svg)](https://github.com/PCfVW/oris/actions/workflows/zig-ci.yml)
[![Zig release](https://img.shields.io/github/v/release/PCfVW/oris?logo=zig&color=f7a41d)](https://github.com/PCfVW/oris/releases)
[![Zig](https://img.shields.io/badge/Zig-0.16.0-f7a41d?logo=zig)](https://ziglang.org/)
[![License](https://img.shields.io/badge/license-MIT%20OR%20Apache--2.0-blue)](https://github.com/PCfVW/oris/blob/main/LICENSE-MIT)
[![Rust sibling: orisnik](https://img.shields.io/crates/v/orisnik?logo=rust&label=rust%20sibling)](https://crates.io/crates/orisnik)

**The v0.1.0 implementation is complete in this repository and not yet tagged as a release.** Track the v0.1.0 release at <https://github.com/PCfVW/oris>.

## What's here

- A size-class **bucket allocator** for small allocations (up to 256 bytes), backed by fixed-size 64&nbsp;KiB OS pages.
- A red-black-tree **best-fit allocator** for everything larger, with physical-neighbour coalescing.
- Three public surfaces over one shared core:
  - **`Orisnitsa`**'s own methods (`alloc`, `free`, `realloc`, `resize`, `purge`, ...) — the idiomatic Zig entry point.
  - **`allocator()`** — hands out a `std.mem.Allocator` backed by an instance, for `std.ArrayList`/`std.HashMap`/etc.
  - **`oris_*`** — a C-shaped API (`oris_new`, `oris_alloc`, `oris_free`, `oris_realloc`, ...), instance-scoped via an explicit handle — never a hidden global.
- 80+ tests, verified in Debug and ReleaseSafe (runtime safety checks on) and ReleaseFast (hot path with checks off), on Windows, Linux, and macOS in CI.

## Quick start

```zig
const std = @import("std");
const orisnitsa = @import("orisnitsa");

var backing: orisnitsa.Orisnitsa = .init();
const gpa = orisnitsa.allocator(&backing);

var list: std.ArrayList(u8) = .empty;
defer list.deinit(gpa);
```

`Orisnitsa.init()` is a pure, `comptime`-constructible value, so a
`var ALLOCATOR: orisnitsa.Orisnitsa = .init();`-style global needs no
`OnceLock`/`LazyLock`-equivalent indirection. See [INSTALL.md](https://github.com/PCfVW/oris/blob/main/INSTALL.md) for build instructions and toolchain requirements — the **Zig 0.16.0** pin in [`build.zig.zon`](build.zig.zon) is load-bearing while Zig is pre-1.0: the `std.mem.Allocator` vtable shape is version-sensitive across releases.

The Rust sibling is `orisnik`. See the [project brief](https://github.com/PCfVW/oris/blob/main/BRIEF.md) for design rationale and the [roadmap](https://github.com/PCfVW/oris/blob/main/ROADMAP.md) for what ships in each version.

## License

Dual-licensed under [MIT](https://github.com/PCfVW/oris/blob/main/LICENSE-MIT) OR [Apache-2.0](https://github.com/PCfVW/oris/blob/main/LICENSE-APACHE), at your option.

## Development

- Exclusively developed with [Claude Code](https://claude.com/product/claude-code)
- Verified in Debug and ReleaseSafe (`std.testing.allocator` leak detection, runtime safety checks on) as a required CI lane on all three OSes, not just a local dev-time check — Zig's analog of the Rust port's Miri gate
- Coding discipline: [Grit-ORIS](CONVENTIONS.md), the Zig dialect of the [Amphigraphic](https://github.com/PCfVW/Amphigraphic-Strict) `Grit` conventions (initially named Gizmo), sharing the [cross-port-invariant](https://github.com/PCfVW/oris/blob/main/ROADMAP.md) rules with the Rust port
