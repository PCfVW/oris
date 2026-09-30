// SPDX-License-Identifier: MIT OR Apache-2.0
//! # orisnitsa
//!
//! The Zig port of Dimitar Lazarov's HPHA (2007) — a single-threaded heap
//! allocator combining a size-class bucket allocator for small allocations with a
//! red-black-tree best-fit allocator for large ones. See
//! [the brief](https://github.com/PCfVW/oris/blob/main/BRIEF.md) for the design
//! rationale and [the roadmap](https://github.com/PCfVW/oris/blob/main/ROADMAP.md)
//! for what ships in each version. Mirrors `orisnik` (the Rust port) module for
//! module; both ports release in lockstep — same version, same internal state
//! transitions.
//!
//! Two surfaces share one core: `Orisnitsa`'s own methods (`alloc`, `free`,
//! `realloc`, ...) and `allocator`, which hands out a `std.mem.Allocator` backed
//! by an instance for use with `std.ArrayList`/`std.HashMap`/etc. A third, the
//! `oris_*` C-ABI (`oris_alloc`, `oris_free`, ...), is available to C callers by
//! symbol name once this module is built into a library — see `capi.zig`'s own
//! module doc for why those functions aren't additionally re-exported here by
//! name (unlike `orisnik`'s `lib.rs`, which needs `pub use capi::{...}` for
//! Rust-level visibility of items that would otherwise be private to that
//! module; Zig's `export fn` already gives them global C linkage independent of
//! any `pub`/import visibility within this package).
//!
//! ```zig
//! const std = @import("std");
//! const orisnitsa = @import("orisnitsa");
//!
//! var backing: orisnitsa.Orisnitsa = .init();
//! defer backing.deinit(); // must be called: returns the idle OS pages/arenas (every build)
//! const gpa = orisnitsa.allocator(&backing);
//!
//! var list: std.ArrayList(u8) = .empty;
//! defer list.deinit(gpa);
//! ```
//!
//! `Orisnitsa.init()` is a pure, `comptime`-constructible value — no
//! `OnceLock`/`LazyLock`-equivalent indirection needed for a
//! `var ALLOCATOR: orisnitsa.Orisnitsa = .init();`-style global. Unlike
//! `orisnik`'s doctest, this one is deliberately *not* wired as a real
//! process-wide global allocator here: doing so would make every allocation in
//! this very documentation build route through `Orisnitsa`, for the same reason
//! `orisnik`'s own doctest is `no_run` and its `global_alloc.rs` tests call the
//! vtable directly rather than installing it — see that file's module doc.

const std = @import("std");

const orisnitsa_mod = @import("orisnitsa.zig");
const allocator_mod = @import("allocator.zig");

/// The top-level allocator type — dispatches every request between the bucket
/// and tree paths. The default, non-debug instantiation of the generic
/// `orisnitsa_mod.Orisnitsa(comptime config: Config) type` — keeps this public
/// surface source-compatible with every pre-v0.2.0 consumer. See `orisnitsa.zig`
/// and `spomen.zig`'s `Config`.
pub const Orisnitsa = orisnitsa_mod.Orisnitsa(.{});
/// The generic behind `Orisnitsa`: `OrisnitsaWith(.{ .debug = true })` is the debug allocator
/// (guard bytes, allocation records, `check()`/`report()`, leak detection in `deinit()`);
/// `OrisnitsaWith(.{})` is exactly `Orisnitsa`. Every instantiation works with `allocator()`.
pub const OrisnitsaWith = orisnitsa_mod.Orisnitsa;
/// The `comptime` configuration `OrisnitsaWith` takes. See `spomen.zig`.
pub const Config = @import("spomen.zig").Config;
/// Hands out a `std.mem.Allocator` backed by an `Orisnitsa` instance. See
/// `allocator.zig`.
pub const allocator = allocator_mod.allocator;
/// The error set of the debug subsystem's off-hot-path diagnostics (`Orisnitsa.check`). See
/// `spomen_failure.zig`.
pub const OrisError = @import("spomen_failure.zig").OrisError;
/// The out-parameter `Orisnitsa.check` fills with a human-readable description of the first
/// problem it finds. See `spomen_failure.zig`.
pub const Diagnostic = @import("spomen_failure.zig").Diagnostic;

// Imported only so their `test` blocks are reachable from this root module via
// this file's own `test { refAllDecls(...) }` block below — not re-exported as
// part of the public surface above. `capi.zig`'s `export fn`s (the `oris_*`
// C-ABI) are *not* linked into an artifact by this import alone: Zig only
// auto-exports `export fn`s that live in a module's own root file, so
// `build.zig` builds the C-linkable library artifacts from a module rooted
// directly at `capi.zig`, not this file — see `build.zig`'s own comment on
// that. This import exists solely so `zig build test` also exercises
// `capi.zig`'s tests via the `refAllDecls` call below.
const align_helpers = @import("align.zig");
const tag = @import("tag.zig");
const os = @import("os.zig");
const list = @import("list.zig");
const rbtree = @import("rbtree.zig");
const block = @import("block.zig");
const bucket = @import("bucket.zig");
const tree = @import("tree.zig");
const spomen = @import("spomen.zig");
const guard = @import("guard.zig");
const spomen_guard = @import("spomen_guard.zig");
const spomen_poison = @import("spomen_poison.zig");
const spomen_record = @import("spomen_record.zig");
const spomen_book = @import("spomen_book.zig");
const spomen_store = @import("spomen_store.zig");
const spomen_failure = @import("spomen_failure.zig");
const rand = @import("rand.zig");
const capi = @import("capi.zig");

test "a consumer can instantiate the debug allocator and hand it out as a std.mem.Allocator" {
    // Only what this file exports: the way an importing package reaches the debug allocator.
    const Debug = OrisnitsaWith(.{ .debug = true });
    var backing: Debug = .init();
    const gpa = allocator(&backing);
    const memory = try gpa.alloc(u8, 40);
    try backing.check(null);
    gpa.free(memory);
    backing.deinit();
    // The default instantiation is the very type `Orisnitsa` names.
    try std.testing.expect(OrisnitsaWith(.{}) == Orisnitsa);
}

test {
    // `refAllDecls` must be called with each *imported module* as its own argument,
    // not `@This()` — `refAllDecls(@This())` only forces reference of this file's own
    // top-level decls (which includes the `align_helpers` name itself, but not
    // anything *inside* it), so it does not surface `align.zig`'s own `test` blocks.
    // Calling it once per imported module is what actually forces each module's
    // declarations — and therefore its `test` blocks — into this test binary.
    // Confirmed empirically against Zig 0.16.0, not assumed: `zig test` does not
    // auto-discover tests across the whole `@import` graph on its own.
    std.testing.refAllDecls(align_helpers);
    std.testing.refAllDecls(tag);
    std.testing.refAllDecls(os);
    std.testing.refAllDecls(list);
    std.testing.refAllDecls(rbtree);
    std.testing.refAllDecls(block);
    std.testing.refAllDecls(bucket);
    std.testing.refAllDecls(tree);
    std.testing.refAllDecls(spomen);
    std.testing.refAllDecls(guard);
    std.testing.refAllDecls(spomen_guard);
    std.testing.refAllDecls(spomen_poison);
    std.testing.refAllDecls(spomen_record);
    std.testing.refAllDecls(spomen_book);
    std.testing.refAllDecls(spomen_store);
    std.testing.refAllDecls(spomen_failure);
    std.testing.refAllDecls(rand);
    std.testing.refAllDecls(orisnitsa_mod);
    std.testing.refAllDecls(allocator_mod);
    std.testing.refAllDecls(capi);
}
