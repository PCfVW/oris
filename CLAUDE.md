# Claude Code Instructions — Oris

Oris is a two-port monorepo: `Rust/` (the `orisnik` crate) and `Zig/` (the `orisnitsa`
module), both faithful ports of Dimitar Lazarov's HPHA (2007). See `BRIEF.md` for design
rationale and the Bulgarian naming family, `ROADMAP.md` for milestones and the cross-port
invariant.

## Coding conventions

- When editing under `Rust/`, apply **`Rust/CONVENTIONS.md`** in full — every annotation,
  doc-comment, and `unsafe`/provenance rule is mandatory.
- When editing under `Zig/`, apply **`Zig/CONVENTIONS.md`** in full.
- Each port has its own `CLAUDE.md` (next to its `CONVENTIONS.md`) with language-specific
  build and test gates.

## The cross-port invariant (both ports)

The project's defining property (see `ROADMAP.md`): an identical public alloc/free sequence
must produce **identical internal state transitions** across both ports — same bucket-page
spawns, same tree-rotation count, same coalescing operations, same final RSS.

Any change to size-class math, tree rotation, coalescing order, or on-heap metadata layout in
one port must be mirrored in the other. From v0.3.0 a CI trace-corpus parity check enforces
this. Treat such changes as touching that gate.

## License header

Every source file begins with `// SPDX-License-Identifier: MIT OR Apache-2.0` (both `.rs` and
`.zig`). The reference C++ under `Cpp/` keeps its original 2007 copyright header verbatim — do
not modify it.

## Shell environment

The user runs PowerShell on Windows. Use `$env:VAR="value";` for environment variables and
semicolons to chain commands (not `&&`); use forward slashes in paths passed to cargo/zig.
