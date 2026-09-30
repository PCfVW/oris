// SPDX-License-Identifier: MIT OR Apache-2.0
//! `spomen` (спомен, "remembrance") — the instrumentation cousin of the allocator
//! family: guard bytes, allocation-record tracking, callstack capture, leak
//! detection, and the `check()`/`report()` diagnostics (see
//! `Zig/CONVENTIONS.md`'s "The `spomen` Debug Subsystem" section). This module
//! itself defines only `Config`, the `comptime` toggle `Orisnitsa`/`Buckets`/
//! `Tree` are generic over. The instrumentation lives in sibling files: guard bytes (`guard.zig`, `spomen_guard.zig`) and
//! payload poisoning (`spomen_poison.zig`) are implemented, as is allocation-record
//! storage (`spomen_record.zig`, `spomen_book.zig`, `spomen_store.zig`, including
//! raw callstack capture), wired into `Orisnitsa`'s dispatch through the
//! `debug*` hooks (`orisnitsa.zig`), with corruption reported by
//! `spomen_failure.zig`. `Orisnitsa.check()`, `report()` and leak detection at
//! `deinit()` are implemented too. Not implemented: resolving callstack addresses to
//! symbols (`report()` prints raw return addresses; feed them to `addr2line`).

/// The `comptime` configuration `Orisnitsa`/`Buckets`/`Tree` are generic type
/// constructors over — `Orisnitsa(config)`, not a plain `Orisnitsa` value with a
/// `config` field. Passing `config` through a generic type constructor, rather
/// than reading a runtime `bool` field on `self`, is what makes the debug
/// subsystem's zero-cost-when-disabled property a *compiler guarantee* instead of
/// an optimizer hope: every `spomen`-only branch lives inside
/// an `if (config.debug)` whose condition is `comptime`-known at the call site, so
/// it is eliminated from `Orisnitsa(.{})`'s code entirely, not merely folded when
/// the optimizer happens to see through it. Matches Zig's own
/// `std.heap.DebugAllocator(comptime config: Config) type` and `orisnik`'s
/// `debug-allocator` Cargo feature.
pub const Config = struct {
    /// Enables the `spomen` debug subsystem (guard bytes, allocation-record
    /// tracking, callstack capture, leak detection, check()/report()) — guard
    /// bytes, poisoning, allocation records, the hooks that use them, check()/report()
    /// and leak detection at `deinit()` are implemented (see this module's own doc).
    /// `comptime` so the relevant branches are
    /// eliminated entirely when `false`, matching
    /// `orisnik`'s `debug-allocator` Cargo feature and Zig's own
    /// `std.heap.DebugAllocator(comptime config: Config)`.
    debug: bool = false,
};
