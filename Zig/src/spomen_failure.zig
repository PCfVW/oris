// SPDX-License-Identifier: MIT OR Apache-2.0
//! What the debug hooks do when they detect corruption. Ports the `assert()`s in
//! `Cpp/hpha.cpp`'s `debug_record_map::remove`/`check` ("if this asserts most likely the
//! pointer was already deleted", "if this asserts then the memory was corrupted past the
//! end of the block", "make sure the free size matches the allocation size"), mirroring
//! `orisnik`'s `Rust/src/spomen/failure.rs`.
//!
//! Detection is a plain value (`Corruption`, derived from the `VerifyError` that the
//! hooks' pure `verify` step returns, so it is directly testable); the *reaction* is the
//! single `fail` function: it panics with a message that names the block, what is
//! wrong, and where the block was allocated. This is `spomen`'s one deliberate exception
//! to "the hot path never panics" (`Zig/CONVENTIONS.md`): fail-fast is the whole point
//! of a debug allocator, and it is compiled only into `config.debug` instantiations.
//!
//! # Testing limitation
//! A Zig test cannot catch a panic, so `fail` itself is never exercised by a unit test.
//! The tests cover `verify` (which returns the error for each corruption kind) and
//! `describe` (the message text) directly; there is deliberately no test-only seam that
//! lets dispatch continue after a detected corruption.
//!
//! # No global-allocator caveat
//! `orisnik` must be built `panic = "abort"` when it is the process's global allocator,
//! because unwinding out of a Rust global allocator is undefined behaviour. Zig panics do
//! not unwind, so there is nothing to configure.
//!
//! # Callstacks
//! A record's callstack is raw return addresses, so the message lists them in hex.
//! Resolving them to symbols is left to the reader (`report()` prints the same raw
//! addresses; feed them to `addr2line` or `std.debug`).

const std = @import("std");
const spomen_record = @import("spomen_record.zig");

const Record = spomen_record.Record;

/// Bytes of stack the panic path reserves for its message. Generous for the fixed
/// wording, three addresses/sizes and `MAX_CALLSTACK_DEPTH` hex return addresses;
/// `describe` truncates rather than fail if it is ever too small.
pub const MESSAGE_CAPACITY: usize = 2048;

/// The ways `verify` can reject a pointer handed to `free`/`realloc`/`resize`.
pub const VerifyError = error{
    /// No record exists for the pointer: it was never allocated by this allocator, or it
    /// was already freed (a double free).
    UnknownPointer,
    /// A sized free named a size other than the one recorded for the allocation.
    SizeMismatch,
    /// The trailing guard ramp no longer matches the seed recorded for the allocation:
    /// something wrote past the end of the block.
    GuardOverrun,
};

/// What a debug hook found wrong with a pointer, with the data the message needs.
pub const Corruption = union(enum) {
    /// See `VerifyError.UnknownPointer`.
    unknown_pointer,
    /// See `VerifyError.SizeMismatch`. The payload is the size the caller supplied, as
    /// compared (after the minimum-size clamp), in bytes.
    size_mismatch: usize,
    /// See `VerifyError.GuardOverrun`.
    guard_overrun,
    /// A live record claims more bytes than the block it describes can hold. Only
    /// `check()` and the leak audit look for this (HPHA's
    /// `assert(it->size() <= size(it->ptr()))`). The payload is the block's real usable
    /// size, in bytes.
    oversized: usize,
};

/// Why a debug diagnostic (`Orisnitsa.check`) failed. Zig's first `error{...}` set, per
/// `Zig/CONVENTIONS.md`'s "Allocation outcomes are values" (error sets are reserved for the
/// off-hot-path `spomen` surface). The human-readable description is obtained through a
/// `Diagnostic` out-parameter. Mirrors `orisnik`'s `OrisError`.
pub const OrisError = error{
    /// The operating system refused something. Reserved: no diagnostic here asks the OS for
    /// anything that can fail as a *result* yet (out of memory is a value, `null`, on the
    /// allocation paths), but the member is part of the documented shape so adding such a
    /// diagnostic later is not a breaking change.
    Os,
    /// The heap was found corrupted: a guard overrun, or a record that disagrees with the
    /// block it describes.
    Corruption,
};

/// A fixed buffer that receives `check()`'s description of the first problem it found. No
/// allocation; pass `null` to `check` if only the error matters.
pub const Diagnostic = struct {
    /// Backing storage for the message.
    buf: [MESSAGE_CAPACITY]u8 = undefined,
    /// How many bytes of `buf` hold the message (`0` until `check` fills it).
    len: usize = 0,

    /// The description `check` wrote, or an empty slice if it found no problem.
    pub fn message(self: *const Diagnostic) []const u8 {
        return self.buf[0..self.len];
    }

    /// Fills this diagnostic with the description of `what` (see `describe`).
    pub fn set(self: *Diagnostic, what: Corruption, ptr: [*]const u8, record: ?*const Record) void {
        self.len = describe(&self.buf, what, ptr, record).len;
    }
};

/// The diagnostic for `what`, formatted into `buf` and returned as a slice of it,
/// following the house wording (lowercase, no trailing period, the offending value
/// included; the head line is identical to `orisnik`'s, the callstack section differs —
/// raw hex addresses here, a rendered `Backtrace` there). `record`, when the pointer had one, adds the
/// recorded sizes and where the block was allocated (raw addresses, see the module doc).
/// Truncates if `buf` is too small.
///
/// `record`, if non-null, must point to a live `Record`.
pub fn describe(buf: []u8, what: Corruption, ptr: [*]const u8, record: ?*const Record) []const u8 {
    var w: std.Io.Writer = .fixed(buf);
    write(&w, what, ptr, record) catch {}; // only `error.WriteFailed`: buffer full, keep what fit
    return w.buffered();
}

fn write(w: *std.Io.Writer, what: Corruption, ptr: [*]const u8, record: ?*const Record) std.Io.Writer.Error!void {
    // PROVENANCE: address read for its bit pattern only, to print it.
    const addr = @intFromPtr(ptr);
    switch (what) {
        .unknown_pointer => try w.print(
            "pointer was not allocated by this allocator or was already freed (block 0x{x})",
            .{addr},
        ),
        .size_mismatch => |given| {
            const recorded = if (record) |r| r.size else 0;
            try w.print(
                "free size does not match allocation size (block 0x{x}, allocated as {d} bytes, freed as {d})",
                .{ addr, recorded, given },
            );
        },
        .oversized => |usable| {
            const size = if (record) |r| r.size else 0;
            try w.print(
                "recorded size exceeds the block's size (block 0x{x}, recorded {d} bytes, block holds {d})",
                .{ addr, size, usable },
            );
        },
        .guard_overrun => {
            const size = if (record) |r| r.size else 0;
            try w.print(
                "guard bytes overwritten, memory was written past the end of the block (block 0x{x}, requested {d} bytes)",
                .{ addr, size },
            );
        },
    }
    const r = record orelse return;
    try w.writeAll("\nallocated at (return addresses, symbols not resolved):");
    var any = false;
    for (r.callstack) |frame| {
        if (frame == 0) break; // the unused tail is zero-filled
        any = true;
        try w.print("\n  0x{x}", .{frame});
    }
    if (!any) try w.writeAll("\n  (no callstack captured)");
}

/// Reacts to detected corruption: panics with `message`. Never returns. Cold, so the
/// checks around it stay on the fast path's side of the code layout.
pub fn fail(message: []const u8) noreturn {
    @branchHint(.cold);
    std.debug.panic("{s}", .{message});
}

/// The panic that ends `Orisnitsa.deinit` when `leaked` allocations were still live (HPHA's
/// destructor assert). Zig panics do not unwind, so there is no "already panicking" case to
/// skip.
pub fn failOnLeak(leaked: usize) noreturn {
    @branchHint(.cold);
    var buf: [LEAK_MESSAGE_CAPACITY]u8 = undefined;
    fail(leakMessage(&buf, leaked));
}

/// Bytes `leakMessage` needs for any `usize` count.
pub const LEAK_MESSAGE_CAPACITY: usize = 160;

/// The text of `failOnLeak`'s panic, formatted into `buf` (pure, so it is testable
/// without panicking). Same wording as `orisnik`'s.
pub fn leakMessage(buf: []u8, leaked: usize) []const u8 {
    return std.fmt.bufPrint(
        buf,
        "memory leaked: {d} allocation(s) still live when the allocator was dropped (see the report above)",
        .{leaked},
    ) catch buf; // unreachable for `LEAK_MESSAGE_CAPACITY`
}

const testing = std.testing;

// `fail` is not tested: a Zig test cannot catch a panic (see the module doc).

fn ptrAt(addr: usize) [*]u8 {
    // SAFETY: never dereferenced; only its address is printed.
    // PROVENANCE: no allocation behind it.
    return @ptrFromInt(addr);
}

test "unknown pointer names the block and the cause" {
    var buf: [MESSAGE_CAPACITY]u8 = undefined;
    const msg = describe(&buf, .unknown_pointer, ptrAt(0x1230), null);
    try testing.expect(std.mem.indexOf(u8, msg, "already freed") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "0x1230") != null);
}

test "record-backed messages carry sizes and the allocation site" {
    const cs = [_]usize{ 0xAAA1, 0xBBB2, 0, 0, 0, 0, 0, 0 };
    const record = Record.withCallstack(ptrAt(0x4000), 40, .tree, 7, cs);
    var buf: [MESSAGE_CAPACITY]u8 = undefined;

    const overrun = describe(&buf, .guard_overrun, ptrAt(0x4000), &record);
    try testing.expect(std.mem.indexOf(u8, overrun, "guard bytes overwritten") != null);
    try testing.expect(std.mem.indexOf(u8, overrun, "requested 40 bytes") != null);
    try testing.expect(std.mem.indexOf(u8, overrun, "allocated at") != null);
    try testing.expect(std.mem.indexOf(u8, overrun, "0xaaa1") != null);
    try testing.expect(std.mem.indexOf(u8, overrun, "0xbbb2") != null);

    const mismatch = describe(&buf, .{ .size_mismatch = 64 }, ptrAt(0x4000), &record);
    try testing.expect(std.mem.indexOf(u8, mismatch, "allocated as 40 bytes, freed as 64") != null);
}

test "an empty callstack is reported as such" {
    const record = Record.withCallstack(ptrAt(0x4000), 8, .buckets, 0, [_]usize{0} ** spomen_record.MAX_CALLSTACK_DEPTH);
    var buf: [MESSAGE_CAPACITY]u8 = undefined;
    const msg = describe(&buf, .guard_overrun, ptrAt(0x4000), &record);
    try testing.expect(std.mem.indexOf(u8, msg, "no callstack captured") != null);
}

test "describe truncates instead of failing on a tiny buffer" {
    var buf: [16]u8 = undefined;
    const msg = describe(&buf, .unknown_pointer, ptrAt(0x1230), null);
    try testing.expectEqual(@as(usize, 16), msg.len);
}

test "an oversized record names both sizes" {
    const record = Record.withCallstack(ptrAt(0x4000), 10_000, .buckets, 0, [_]usize{0} ** spomen_record.MAX_CALLSTACK_DEPTH);
    var buf: [MESSAGE_CAPACITY]u8 = undefined;
    const msg = describe(&buf, .{ .oversized = 24 }, ptrAt(0x4000), &record);
    try testing.expect(std.mem.indexOf(u8, msg, "recorded size exceeds the block's size") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "recorded 10000 bytes") != null);
    try testing.expect(std.mem.indexOf(u8, msg, "block holds 24") != null);
}

test "a Diagnostic keeps the description it was given" {
    var diagnostic: Diagnostic = .{};
    try testing.expectEqual(@as(usize, 0), diagnostic.message().len);
    diagnostic.set(.unknown_pointer, ptrAt(0x1230), null);
    try testing.expect(std.mem.indexOf(u8, diagnostic.message(), "0x1230") != null);
}

test "an oversized record's whole message, exactly" {
    // The record's callstack is empty, so the message is the head line plus the empty
    // callstack section: address, both sizes, no trailing period on the head.
    const record = Record.withCallstack(ptrAt(0x4000), 10_000, .buckets, 0, [_]usize{0} ** spomen_record.MAX_CALLSTACK_DEPTH);
    var buf: [MESSAGE_CAPACITY]u8 = undefined;
    try testing.expectEqualStrings(
        "recorded size exceeds the block's size (block 0x4000, recorded 10000 bytes, block holds 24)\n" ++
            "allocated at (return addresses, symbols not resolved):\n  (no callstack captured)",
        describe(&buf, .{ .oversized = 24 }, ptrAt(0x4000), &record),
    );
    // Without a record there is no callstack section and no recorded size (`0`).
    try testing.expectEqualStrings(
        "recorded size exceeds the block's size (block 0x4000, recorded 0 bytes, block holds 24)",
        describe(&buf, .{ .oversized = 24 }, ptrAt(0x4000), null),
    );
}

test "the leak panic message, exactly" {
    var buf: [LEAK_MESSAGE_CAPACITY]u8 = undefined;
    try testing.expectEqualStrings(
        "memory leaked: 3 allocation(s) still live when the allocator was dropped (see the report above)",
        leakMessage(&buf, 3),
    );
    // Fits even for the largest count.
    try testing.expect(std.mem.startsWith(u8, leakMessage(&buf, std.math.maxInt(usize)), "memory leaked: 18446744073709551615 "));
}
