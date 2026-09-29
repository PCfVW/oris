// SPDX-License-Identifier: MIT OR Apache-2.0
//! One allocation's debug record. Ports `Cpp/hpha.h`'s `allocator::debug_record` and
//! `debug_source`, mirroring `orisnik`'s `Rust/src/spomen/record.rs`.
//!
//! A `Record` remembers everything the debug subsystem needs to know about one live
//! allocation: where it is, how big the *caller* asked for, which sub-allocator served
//! it, the seed of its trailing guard ramp, and where it was allocated from. Records are
//! kept in a `spomen_book.zig` `RecordBook` and indexed by address in an
//! `IntrusiveMultiRbTree` via the embedded `NodeBase`, exactly as HPHA's
//! `debug_record_map` does.
//!
//! # Callstack capture
//! HPHA's `record_stack` is a stub ("usually very system specific so here we just clear
//! all"). This port captures a real callstack instead — the equivalent `ROADMAP.md`
//! allows ("contents must be equivalent, structure need not match"): the capture is
//! diagnostic content, never part of the cross-port state-transition invariant.
//!
//! Zig has no drop glue, so — unlike `orisnik`, whose `Backtrace` owns heap memory —
//! the callstack is plain data: a fixed `[MAX_CALLSTACK_DEPTH]usize` of return
//! addresses (HPHA's own `MAX_CALLSTACK_DEPTH` is 8), captured with
//! `std.debug.captureCurrentStackTrace(.{ .first_address = @returnAddress() }, &buf)`
//! and zero-filling the unused tail — exactly what `std/heap/debug_allocator.zig`'s
//! `collectStackTrace` does (Zig 0.16). A `Record` is therefore trivially copyable, and
//! the book and store move it by value with no ownership bookkeeping.
//!
//! Symbol resolution (turning the addresses into names and source locations) is
//! deferred to `report()`, a later phase; nothing here formats or resolves anything.

const std = @import("std");
const rbtree = @import("rbtree.zig");
const spomen = @import("spomen.zig");
const spomen_guard = @import("spomen_guard.zig");

const Config = spomen.Config;

/// The number of return addresses a `Record` keeps. HPHA's own
/// `MAX_CALLSTACK_DEPTH`.
pub const MAX_CALLSTACK_DEPTH: usize = 8;

/// Which sub-allocator served an allocation. Ports `debug_source`
/// (`DEBUG_SOURCE_BUCKETS = 0`, `DEBUG_SOURCE_TREE = 1`).
pub const Source = enum(u8) {
    /// The small-allocation path (`bucket.zig`).
    buckets = 0,
    /// The large-allocation path (`tree.zig`).
    tree = 1,
};

/// Everything the debug subsystem remembers about one live allocation. Ports
/// `debug_record`.
///
/// # Invariants
/// - `node` is the first field of an `extern struct`, so a `*Record` and its
///   `*NodeBase` are the same address (`IntrusiveMultiRbTree`'s contract).
/// - `ptr` is only ever compared and (by `checkGuard`) read through; the record does
///   not own the allocation it describes.
/// - Records are ordered by `ptr`'s address, and every live allocation's address is
///   unique, so the tree never actually chains two records.
pub const Record = extern struct {
    /// This record's tree linkage. Byte offset 0 (required by `IntrusiveMultiRbTree`).
    node: rbtree.NodeBase = rbtree.NodeBase.UNLINKED,
    /// The payload pointer the allocator handed to the caller. 8-byte aligned in this
    /// struct.
    ptr: [*]u8,
    /// The size the *caller* requested, in bytes — not the (larger) usable size the
    /// block really has. The guard ramp trails at `ptr + size`.
    size: usize,
    /// Which sub-allocator served this allocation.
    source: Source,
    /// The first byte of this allocation's guard ramp — the seed
    /// `spomen_guard.writeGuard` was given.
    guard_byte: u8,
    /// Where this allocation was made from: up to `MAX_CALLSTACK_DEPTH` return
    /// addresses, innermost first, with unused trailing entries zero. Addresses only —
    /// symbols are resolved later, by `report()`.
    callstack: [MAX_CALLSTACK_DEPTH]usize,

    /// A query key is a bare address: records are looked up by the pointer a caller
    /// hands back to `free`, never by a whole record. `IntrusiveMultiRbTree`'s
    /// required `Key`.
    pub const Key = usize;

    /// A fresh, unlinked record for the allocation at `ptr`, capturing the current
    /// callstack. Ports `debug_record(ptr, size, source)`'s `record_stack()` half; the
    /// `write_guard()` half stays with the caller, which owns the guard-seed stream
    /// (see `spomen_guard.writeGuard`) and passes the seed it used as `guard_byte`.
    pub fn init(ptr: [*]u8, size: usize, source: Source, guard_byte: u8) Record {
        return .{
            .node = rbtree.NodeBase.UNLINKED,
            .ptr = ptr,
            .size = size,
            .source = source,
            .guard_byte = guard_byte,
            .callstack = captureCallstack(@returnAddress()),
        };
    }

    /// Captures the current callstack, skipping frames up to `first_address` (pass
    /// `@returnAddress()` from the function whose *caller* should be the first frame).
    /// The unused tail is zero-filled. The same call `std/heap/debug_allocator.zig`'s
    /// `collectStackTrace` makes.
    pub fn captureCallstack(first_address: usize) [MAX_CALLSTACK_DEPTH]usize {
        var buf: [MAX_CALLSTACK_DEPTH]usize = undefined;
        const st = std.debug.captureCurrentStackTrace(.{ .first_address = first_address }, &buf);
        // INDEX: `@min(.., buf.len)` keeps the slice start within `buf`.
        @memset(buf[@min(st.return_addresses.len, buf.len)..], 0);
        return buf;
    }

    /// Whether this allocation's trailing guard ramp is still exactly the one written
    /// for it. Ports `debug_record::check_guard`.
    ///
    /// The allocation this record describes must still be live and valid for
    /// `size + memoryGuardSize(config)` bytes, readable for at least the trailing
    /// `memoryGuardSize(config)` of them. (`config` is a `comptime` parameter here
    /// because Zig's guard size is per-instantiation, where `orisnik` has one global
    /// `MEMORY_GUARD_SIZE` constant.)
    pub fn checkGuard(self: *const Record, comptime config: Config) bool {
        return spomen_guard.checkGuardSeeded(config, self.ptr, self.size, self.guard_byte);
    }

    /// Orders by payload address. `IntrusiveMultiRbTree`'s required `cmp`.
    pub fn cmp(this: *const Record, other: *const Record) std.math.Order {
        // PROVENANCE: address read for its bit pattern only, never turned back into a
        // pointer.
        return std.math.order(@intFromPtr(this.ptr), @intFromPtr(other.ptr));
    }

    /// `IntrusiveMultiRbTree`'s required `cmpKey`.
    pub fn cmpKey(this: *const Record, key: usize) std.math.Order {
        // PROVENANCE: address read for its bit pattern only, never turned back into a
        // pointer.
        return std.math.order(@intFromPtr(this.ptr), key);
    }
};

comptime {
    // Layout lock — `node` must sit at offset 0 for `@fieldParentPtr("node", ...)` to
    // be an identity and to match `orisnik`'s `#[repr(C)]` `Record`, whose leading
    // fields are identical (only the trailing `callstack` differs, see the module doc).
    std.debug.assert(@offsetOf(Record, "node") == 0);
    std.debug.assert(@alignOf(Record) == @alignOf(usize));
    std.debug.assert(@sizeOf(Record) % @alignOf(Record) == 0);
}

const testing = std.testing;
const debug_config: Config = .{ .debug = true };

test "ordering is by address" {
    var bytes = [_]u8{0} ** 4;
    const lo = Record.init(@ptrCast(&bytes[0]), 1, .buckets, 0);
    const hi = Record.init(@ptrCast(&bytes[3]), 1, .buckets, 0);
    try testing.expectEqual(std.math.Order.lt, lo.cmp(&hi));
    try testing.expectEqual(std.math.Order.gt, hi.cmpKey(@intFromPtr(lo.ptr)));
}

test "checkGuard uses the recorded seed" {
    const requested = 10;
    const buf = try testing.allocator.alloc(u8, requested + @import("guard.zig").memoryGuardSize(debug_config));
    defer testing.allocator.free(buf);
    spomen_guard.writeGuard(debug_config, buf.ptr, requested, 77);
    const good = Record.init(buf.ptr, requested, .tree, 77);
    try testing.expect(good.checkGuard(debug_config));
    // Same (self-consistent) ramp, wrong remembered seed: must be rejected.
    const stale = Record.init(buf.ptr, requested, .tree, 78);
    try testing.expect(!stale.checkGuard(debug_config));
}

test "init captures a callstack and zero-fills the unused tail" {
    var byte: u8 = 0;
    const rec = Record.init(@ptrCast(&byte), 1, .buckets, 0);
    // Zig cannot cheaply resolve symbols inside a unit test (that is `report()`'s
    // later job, and needs debug info the test binary may not carry), so this only
    // asserts that a real frame was captured: the innermost address is non-zero.
    try testing.expect(rec.callstack[0] != 0);
    // Zero-fill invariant: once a zero appears, everything after it is zero too.
    var seen_zero = false;
    for (rec.callstack) |addr| {
        if (addr == 0) seen_zero = true else try testing.expect(!seen_zero);
    }
}
