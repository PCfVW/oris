# Claude Code Instructions — orisnitsa (Zig port)

## Coding conventions

Always apply the rules in `CONVENTIONS.md` (this directory). The annotation grammar, the
`extern`/`packed` layout-lock, the raw-memory (`unsafe`-by-nature) discipline, and the
cross-port-invariant section are mandatory. The repo-root `CLAUDE.md` holds the shared
**cross-port invariant** — read it before changing size-class math, tree rotation, coalescing
order, or block-header layout.

Every `.zig` file begins with `// SPDX-License-Identifier: MIT OR Apache-2.0` as its first line.
`zig fmt` is canonical; CI rejects unformatted code.

## Pre-commit checks (once code lands)

1. `zig fmt .`
2. `zig build test` in `Debug` **and** `ReleaseSafe` (runtime safety checks on), wrapping the
   allocator-under-test with `std.testing.allocator` (leak detection) and exercising
   `std.testing.checkAllAllocationFailures`. See `CONVENTIONS.md` § *Verification gate*. A new
   raw-memory path is *pending* until a safe-build test exercises it.
3. Build `ReleaseFast` to confirm the hot path compiles with safety checks off.
4. Update `CHANGELOG.md` — a bullet under `[Unreleased]` for any user-visible change.

## Zig version

Target **Zig 0.16.0** (current stable; 0.15.x is one series behind, 0.17.0 imminent) and pin it
in `build.zig.zon`. The `std.mem.Allocator` vtable signature (alignment representation, the
`remap` entry) shifted around the 0.15 → 0.16 boundary, and the cross-port invariant is defined
against a specific interface shape — so the pin matters while Zig is pre-1.0.
