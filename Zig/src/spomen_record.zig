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
//! left to the reader: `report()` prints the raw addresses, and nothing here formats or
//! resolves anything.

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
/// - 64-bit layout (locked by the `comptime` block below): `node` 0, `ptr` 40, `size`
///   48, `source` 56, `guard_byte` 57, `callstack` 64, total 128 bytes. The leading
///   fields match `orisnik`'s `#[repr(C)]` `Record`; the trailing `callstack` differs
///   (inline addresses here, an owning `Backtrace` there), so `@sizeOf` — and hence
///   how many records fit a book page — differs between the ports. That is
///   debug-only diagnostic storage, outside the cross-port state-transition invariant.
pub const Record = extern struct {
    /// This record's tree linkage. Byte offset 0, 8-byte aligned (required by
    /// `IntrusiveMultiRbTree`).
    node: rbtree.NodeBase = rbtree.NodeBase.UNLINKED,
    /// The payload pointer the allocator handed to the caller; a non-zero address.
    /// Byte offset 40, 8-byte aligned. This is the tree key.
    ptr: [*]u8,
    /// The size the *caller* requested, in bytes (any `usize`) — not the (larger)
    /// usable size the block really has. The guard ramp trails at `ptr + size`. Byte
    /// offset 48, 8-byte aligned.
    size: usize,
    /// Which sub-allocator served this allocation. Byte offset 56, 1-byte aligned.
    source: Source,
    /// The first byte of this allocation's guard ramp — the seed
    /// `spomen_guard.writeGuard` was given (any `u8`, the ramp wraps). Byte offset 57.
    guard_byte: u8,
    /// Where this allocation was made from: an array of up to `MAX_CALLSTACK_DEPTH`
    /// raw return addresses (not a `Backtrace`), innermost first, the unused tail
    /// filled with zero. Addresses only — symbols are resolved later, by `report()`.
    /// Byte offset 64, 8-byte aligned.
    callstack: [MAX_CALLSTACK_DEPTH]usize,

    /// A query key is a bare address: records are looked up by the pointer a caller
    /// hands back to `free`, never by a whole record. `IntrusiveMultiRbTree`'s
    /// required `Key`.
    pub const Key = usize;

    /// A fresh, unlinked record for the allocation at `ptr`, capturing the current
    /// callstack with `init`'s own caller as the first frame (`@returnAddress()` here
    /// is a call site inside that caller). Ports `debug_record(ptr, size, source)`'s
    /// `record_stack()` half; the `write_guard()` half stays with the caller, which
    /// owns the guard-seed stream (see `spomen_guard.writeGuard`) and passes the seed
    /// it used as `guard_byte`.
    ///
    /// A layer that wants the trace to start further out (as `RecordStore` does, so
    /// it starts at the store method's caller) uses `initAt` instead.
    pub fn init(ptr: [*]u8, size: usize, source: Source, guard_byte: u8) Record {
        return initAt(@returnAddress(), ptr, size, source, guard_byte);
    }

    /// Like `init`, but the callstack starts at `first_address` — a return address
    /// (typically the `@returnAddress()` of the function whose caller should appear
    /// first). See `captureCallstack`.
    pub fn initAt(first_address: usize, ptr: [*]u8, size: usize, source: Source, guard_byte: u8) Record {
        return withCallstack(ptr, size, source, guard_byte, captureCallstack(first_address));
    }

    /// A fresh, unlinked record with an explicitly supplied `callstack`, capturing
    /// nothing. The seam that makes record bookkeeping testable with a deterministic
    /// callstack. Mirrors `orisnik`'s `Record::with_callstack`.
    pub fn withCallstack(
        ptr: [*]u8,
        size: usize,
        source: Source,
        guard_byte: u8,
        callstack: [MAX_CALLSTACK_DEPTH]usize,
    ) Record {
        return .{
            .node = rbtree.NodeBase.UNLINKED,
            .ptr = ptr,
            .size = size,
            .source = source,
            .guard_byte = guard_byte,
            .callstack = callstack,
        };
    }

    /// Captures the current callstack. The first recorded frame is the one whose
    /// return address equals `first_address` — i.e. a call site in the caller of the
    /// function that took `@returnAddress()` — and that frame is *included*; frames
    /// before it (the capture machinery, that function) are skipped. The unused tail
    /// is zero-filled. The same call `std/heap/debug_allocator.zig`'s
    /// `collectStackTrace` makes. Yields all-zero when stack tracing is unavailable
    /// (`std.options.allow_stack_tracing == false`, e.g. ReleaseSmall).
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
    /// `memoryGuardSize(config)` of them. Only instantiate with `config.debug = true`
    /// (`.{}` is a compile error, see `spomen_guard.checkGuardSeeded`). `config` is a
    /// `comptime` parameter because Zig's guard size is per-instantiation, where
    /// `orisnik` has one global `MEMORY_GUARD_SIZE` constant.
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
    // be an identity, and the leading fields match `orisnik`'s `#[repr(C)]` `Record`
    // (see `Record`'s doc for why the trailing `callstack` and total size differ).
    std.debug.assert(@offsetOf(Record, "node") == 0);
    std.debug.assert(@alignOf(Record) == @alignOf(usize));
    std.debug.assert(@sizeOf(Record) % @alignOf(Record) == 0);
    if (@sizeOf(usize) == 8) { // 64-bit only, like `block.zig`
        std.debug.assert(@offsetOf(Record, "ptr") == 40);
        std.debug.assert(@offsetOf(Record, "size") == 48);
        std.debug.assert(@offsetOf(Record, "source") == 56);
        std.debug.assert(@offsetOf(Record, "guard_byte") == 57);
        std.debug.assert(@offsetOf(Record, "callstack") == 64);
        std.debug.assert(@sizeOf(Record) == 128);
    }
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

test "withCallstack stores exactly the supplied callstack" {
    var byte: u8 = 0;
    const cs = [_]usize{ 1, 2, 3, 4, 5, 6, 7, 8 };
    const rec = Record.withCallstack(@ptrCast(&byte), 3, .tree, 9, cs);
    try testing.expectEqual(cs, rec.callstack);
    try testing.expectEqual(@as(usize, 3), rec.size);
    try testing.expectEqual(Source.tree, rec.source);
    try testing.expectEqual(@as(u8, 9), rec.guard_byte);
}

test "init captures a callstack and zero-fills the unused tail" {
    // With stack tracing disabled (`strip_debug_info`, the default for ReleaseSmall)
    // `captureCurrentStackTrace` legitimately returns nothing, so there is no frame to
    // assert on; the record is still valid (an all-zero callstack).
    if (!std.options.allow_stack_tracing) return error.SkipZigTest;
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
