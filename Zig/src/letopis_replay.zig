// SPDX-License-Identifier: MIT OR Apache-2.0
//! Replaying a trace on a fresh allocator and writing its transition record. Ports
//! `orisnik`'s `letopis/replay.rs`.

const std = @import("std");
const orisnitsa = @import("orisnitsa.zig");
const letopis_event = @import("letopis_event.zig");
const letopis_record = @import("letopis_record.zig");
const letopis_trace = @import("letopis_trace.zig");

const Error = letopis_trace.Error;
const Diagnostic = letopis_trace.Diagnostic;
const Op = letopis_trace.Op;

/// The instantiation every replay runs: the default allocator, plus the `letopis` hooks.
pub const Traced = orisnitsa.Orisnitsa(.{ .trace = true });

/// Bound handles only: `null` is a handle bound to null.
const Handles = std.AutoHashMapUnmanaged(u64, ?[*]u8);

/// What one operation returned, as the record writes it.
const Outcome = union(enum) {
    pointer: ?[*]u8,
    size: usize,
    nothing,
};

/// Replays `trace` on a fresh `Orisnitsa(.{ .trace = true })` and writes its transition
/// record to `out`.
///
/// The trace is parsed and checked in full first (`examples/traces/GRAMMAR.md` §1.3), so
/// nothing is executed unless every operation is defined. The record — one entry per
/// operation, its events, and the closing summary — is byte-identical to what `orisnik`
/// and the HPHA reference write for the same trace; that is the cross-port invariant,
/// checked in CI over the committed corpus. `gpa` backs the parser, the event log and the
/// record's bookkeeping — never the traced allocator, which maps its own pages. On
/// `error.Syntax`/`error.Semantic`, `diagnostic` (if given) receives the line and why.
pub fn replay(gpa: std.mem.Allocator, trace: []const u8, out: *std.Io.Writer, diagnostic: ?*Diagnostic) Error!void {
    const lines = try letopis_trace.parse(gpa, trace, diagnostic);
    defer gpa.free(lines);
    var allocator: Traced = .init();
    var log = letopis_event.EventLog.init(gpa);
    defer log.deinit();
    var handles: Handles = .empty;
    defer handles.deinit(gpa);

    allocator.setLetopis(&log);
    const result = run(gpa, &allocator, &log, lines, &handles, out, diagnostic);
    allocator.setLetopis(null);

    // Teardown is outside the record: free what the trace left live, then `deinit`.
    var live = handles.valueIterator();
    while (live.next()) |ptr| allocator.free(ptr.*);
    allocator.deinit();
    return result;
}

fn run(
    gpa: std.mem.Allocator,
    allocator: *Traced,
    log: *letopis_event.EventLog,
    lines: []const letopis_trace.Line,
    handles: *Handles,
    out: *std.Io.Writer,
    diagnostic: ?*Diagnostic,
) Error!void {
    try out.writeAll("oris-record 1\n");
    var norm: letopis_record.Normalizer = .{};
    defer norm.deinit(gpa);
    // An operation's events are normalized *before* its result (a mapping the operation
    // made must be known to name the pointer it returned), but written after it.
    var events: std.Io.Writer.Allocating = .init(gpa);
    defer events.deinit();
    for (lines, 0..) |line, index| {
        const outcome = try execute(gpa, allocator, line.op, handles);
        if (log.failed) return error.OutOfMemory;
        events.clearRetainingCapacity();
        for (log.events.items) |event| {
            try events.writer.writeAll("  ");
            norm.writeEvent(gpa, &events.writer, event) catch |err| return unmapped(err, diagnostic, line.number);
            try events.writer.writeByte('\n');
        }
        log.events.clearRetainingCapacity();
        try out.print("#{d} ", .{index});
        try line.op.render(out);
        try out.writeAll(" -> ");
        switch (outcome) {
            .pointer => |maybe| if (maybe) |ptr| {
                // PROVENANCE: address read for its value only, to name the result.
                norm.writeLocation(out, @intFromPtr(ptr)) catch |err| return unmapped(err, diagnostic, line.number);
            } else try out.writeAll("null"),
            .size => |size| try out.print("{d}", .{size}),
            .nothing => try out.writeAll("-"),
        }
        try out.print(" a={d}\n", .{allocator.allocated()});
        try out.writeAll(events.written());
    }
    try out.print("end ops={d} maps={d} unmaps={d} rotations={d} allocated={d}\n", .{
        lines.len, norm.maps, norm.unmaps, norm.rotations, allocator.allocated(),
    });
}

fn unmapped(err: Error, diagnostic: ?*Diagnostic, line: usize) Error {
    if (err == error.Unmapped) {
        if (diagnostic) |d| d.set(line, "an event named an address outside every live mapping (a hook bug, not a trace error)", .{});
    }
    return err;
}

/// Runs one operation, updating the handle bindings exactly as `GRAMMAR.md` §1.2 says.
/// Every handle `op` reads is bound to a live allocation of `allocator`, or to null, or
/// (for `realloc`/`reallocAligned` only) unbound — what a trace that passed
/// `letopis_trace.parse` guarantees.
fn execute(gpa: std.mem.Allocator, allocator: *Traced, op: Op, handles: *Handles) Error!Outcome {
    // CAST: u64 -> usize; the package is 64-bit only, so every `@intCast` below is lossless
    // (sizes and alignments are moreover bounded by constraints C3/C4; a calloc's count is not).
    switch (op) {
        .alloc => |o| return bind(gpa, handles, o.h, allocator.alloc(@intCast(o.size))),
        .alloc_aligned => |o| return bind(gpa, handles, o.h, allocator.allocAligned(@intCast(o.size), @intCast(o.alignment))),
        .calloc => |o| return bind(gpa, handles, o.h, allocator.calloc(@intCast(o.count), @intCast(o.size))),
        .realloc => |o| {
            const old = pointer(handles, o.h);
            return rebind(gpa, handles, o.h, o.size, allocator.realloc(old, @intCast(o.size)));
        },
        .realloc_aligned => |o| {
            const old = pointer(handles, o.h);
            return rebind(gpa, handles, o.h, o.size, allocator.reallocAligned(old, @intCast(o.size), @intCast(o.alignment)));
        },
        .resize => |o| return .{ .size = allocator.resize(pointer(handles, o.h), @intCast(o.size)) },
        .size => |o| return .{ .size = allocator.querySize(pointer(handles, o.h)) },
        .free => |o| {
            allocator.free(take(handles, o.h));
            return .nothing;
        },
        .free_sized => |o| {
            allocator.freeWithSize(take(handles, o.h), @intCast(o.size));
            return .nothing;
        },
        .free_sized_aligned => |o| {
            allocator.freeWithSizeAligned(take(handles, o.h), @intCast(o.size), @intCast(o.alignment));
            return .nothing;
        },
        .purge => {
            allocator.purge();
            return .nothing;
        },
    }
}

fn pointer(handles: *const Handles, h: u64) ?[*]u8 {
    return handles.get(h) orelse null;
}

fn take(handles: *Handles, h: u64) ?[*]u8 {
    const entry = handles.fetchRemove(h) orelse return null;
    return entry.value;
}

fn bind(gpa: std.mem.Allocator, handles: *Handles, h: u64, ptr: ?[*]u8) Error!Outcome {
    try handles.put(gpa, h, ptr);
    return .{ .pointer = ptr };
}

/// A realloc rebinds its handle to the result — except a failed one (null for a nonzero
/// size), which leaves the original block, and so the binding, in place.
fn rebind(gpa: std.mem.Allocator, handles: *Handles, h: u64, size: u64, new: ?[*]u8) Error!Outcome {
    if (new != null or size == 0) {
        try handles.put(gpa, h, new);
    } else if (!handles.contains(h)) {
        try handles.put(gpa, h, null);
    }
    return .{ .pointer = new };
}
