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
one port must be mirrored in the other. The trace gate enforces this (`trace-ci.yml`;
`docs/traces.md`): every trace under `examples/traces/` must replay to its committed
`.record` — written by the HPHA oracle — on both ports. Treat such changes as touching that
gate:

- A state transition added, removed or moved emits its `letopis` event at the same point in
  Rust (`chronicle!`), Zig (`if (config.trace) self.tap.emit(...)`) **and**
  `Cpp/oracle/letopis.patch`, and `examples/traces/EVENTS.md` is updated in the same commit.
- Records are regenerated from the oracle (`Cpp/oracle/build_trace_oracle.ps1`, Windows +
  MSVC), never from a port; both ports must then reproduce them byte for byte.
- `benchmarks/scripts/tracegen` changes regenerate the corpus (`tracegen generate`), and
  `tracegen verify` must pass.

The invariant covers the allocator's own state. Debug-only diagnostic storage (the record-book
pages, callstack contents) is outside it: record size and page capacity differ between the
ports, and a Rust instance used through `GlobalAlloc` records no callstack. Rotation counts across
`Drop`/`deinit` are not comparable either (`orisnik` releases memory by read-only walks, `orisnitsa`
calls `purge`): compare state before teardown. See `ROADMAP.md`'s scope note.

## License header

Every source file begins with `// SPDX-License-Identifier: MIT OR Apache-2.0` (both `.rs` and
`.zig`). The reference C++ under `Cpp/` keeps its original 2007 copyright header verbatim — do
not modify it.

## Shell environment

The user runs PowerShell on Windows. Use `$env:VAR="value";` for environment variables and
semicolons to chain commands (not `&&`); use forward slashes in paths passed to cargo/zig.
