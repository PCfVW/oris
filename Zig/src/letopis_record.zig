// SPDX-License-Identifier: MIT OR Apache-2.0
//! Writing the transition record (`examples/traces/GRAMMAR.md` §2): normalizing every raw
//! address an `Event` carries into `m<id>+0x<offset>`, and rendering each event line.
//! Ports `orisnik`'s `letopis/record.rs`.
//!
//! The normalizer replays the `map`/`unmap` events in order to know, at each moment,
//! which mappings are live and which id each one got — the same bookkeeping, in the same
//! order, as `orisnik` and the C++ oracle's `trace_replay.cpp`.

const std = @import("std");
const letopis_event = @import("letopis_event.zig");
const letopis_trace = @import("letopis_trace.zig");

const Event = letopis_event.Event;
const Error = letopis_trace.Error;

/// A live mapping: its base, its length and the id it was given.
const Mapping = struct { base: usize, bytes: usize, id: u64 };

/// The live mappings of one replay, and the run's totals.
pub const Normalizer = struct {
    /// Live mappings, in no particular order (a replay has few at a time).
    live: std.ArrayList(Mapping) = .empty,
    /// The id the next mapping gets.
    next_id: u64 = 0,
    /// Mappings made so far.
    maps: u64 = 0,
    /// Mappings returned so far.
    unmaps: u64 = 0,
    /// Rotations reported by `tree+`/`tree-` events so far.
    rotations: u64 = 0,

    /// Releases the live-mapping table.
    pub fn deinit(self: *Normalizer, gpa: std.mem.Allocator) void {
        self.live.deinit(gpa);
    }

    /// The index in `live` of the mapping containing `addr`.
    fn find(self: *const Normalizer, addr: usize) Error!usize {
        for (self.live.items, 0..) |m, i| {
            if (addr >= m.base and addr - m.base < m.bytes) return i;
        }
        return error.Unmapped;
    }

    /// Writes `addr` as `m<id>+0x<offset>`.
    pub fn writeLocation(self: *const Normalizer, w: *std.Io.Writer, addr: usize) Error!void {
        // INDEX: `find` only returns indices of `live.items`.
        const m = self.live.items[try self.find(addr)];
        try w.print("m{d}+0x{x}", .{ m.id, addr - m.base });
    }

    fn mappingId(self: *const Normalizer, addr: usize) Error!u64 {
        // INDEX: as in `writeLocation`.
        return self.live.items[try self.find(addr)].id;
    }

    /// Writes one event line (without indentation or newline), updating the live-mapping
    /// table and the totals as it goes.
    pub fn writeEvent(self: *Normalizer, gpa: std.mem.Allocator, w: *std.Io.Writer, event: Event) Error!void {
        switch (event) {
            .map => |e| {
                const id = self.next_id;
                self.next_id += 1;
                self.maps += 1;
                try self.live.append(gpa, .{ .base = e.base, .bytes = e.bytes, .id = id });
                const kind: u8 = switch (e.kind) {
                    .bucket => 'b',
                    .tree => 't',
                };
                try w.print("map {c} m{d} {d}", .{ kind, id, e.bytes });
            },
            .unmap => |e| {
                // An unmap names a whole mapping, by its base exactly.
                const index = for (self.live.items, 0..) |m, i| {
                    if (m.base == e.base) break i;
                } else return error.Unmapped;
                const id = self.live.swapRemove(index).id;
                self.unmaps += 1;
                try w.print("unmap m{d} {d}", .{ id, e.bytes });
            },
            .page_spawn => |e| try w.print("page+ b{d} m{d}", .{ e.bucket, try self.mappingId(e.page) }),
            .page_release => |e| try w.print("page- b{d} m{d}", .{ e.bucket, try self.mappingId(e.page) }),
            .page_full => |e| try w.print("page-full b{d} m{d}", .{ e.bucket, try self.mappingId(e.page) }),
            .page_refill => |e| try w.print("page-refill b{d} m{d}", .{ e.bucket, try self.mappingId(e.page) }),
            .split => |e| {
                try w.writeAll("split ");
                try self.writeLocation(w, e.block);
                try w.print(" {d}", .{e.size});
            },
            .shift => |e| {
                try w.writeAll("shift ");
                try self.writeLocation(w, e.block);
                try w.print(" {d}", .{e.offset});
            },
            .merge => |block| {
                try w.writeAll("merge ");
                try self.writeLocation(w, block);
            },
            .tree_insert => |e| {
                self.rotations += e.rotations;
                try w.writeAll("tree+ ");
                try self.writeLocation(w, e.block);
                try w.print(" {d} {s} rot={d}", .{ e.size, @tagName(e.kind), e.rotations });
            },
            .tree_erase => |e| {
                self.rotations += e.rotations;
                try w.writeAll("tree- ");
                try self.writeLocation(w, e.block);
                try w.print(" {d} {s} rot={d}", .{ e.size, @tagName(e.kind), e.rotations });
            },
            .list_push => |e| {
                try w.writeAll("list+ ");
                try self.writeLocation(w, e.block);
                try w.print(" {d}", .{e.size});
            },
            .list_erase => |e| {
                try w.writeAll("list- ");
                try self.writeLocation(w, e.block);
                try w.print(" {d}", .{e.size});
            },
            .mr => |maybe| if (maybe) |block| {
                try w.writeAll("mr ");
                try self.writeLocation(w, block);
            } else {
                try w.writeAll("mr -");
            },
        }
    }
};

const testing = std.testing;

fn expectLine(norm: *Normalizer, event: Event, expected: []const u8) !void {
    var buf: [128]u8 = undefined;
    var w: std.Io.Writer = .fixed(&buf);
    try norm.writeEvent(testing.allocator, &w, event);
    try testing.expectEqualStrings(expected, w.buffered());
}

test "ids follow map order and are never reused" {
    var norm: Normalizer = .{};
    defer norm.deinit(testing.allocator);
    try expectLine(&norm, .{ .map = .{ .kind = .bucket, .base = 0x30_0000, .bytes = 0x1_0000 } }, "map b m0 65536");
    try expectLine(&norm, .{ .map = .{ .kind = .tree, .base = 0x10_0000, .bytes = 0x1_0000 } }, "map t m1 65536");
    var buf: [64]u8 = undefined;
    var w: std.Io.Writer = .fixed(&buf);
    try norm.writeLocation(&w, 0x30_0018);
    try norm.writeLocation(&w, 0x10_0000);
    try testing.expectEqualStrings("m0+0x18m1+0x0", w.buffered());
    try expectLine(&norm, .{ .unmap = .{ .base = 0x30_0000, .bytes = 0x1_0000 } }, "unmap m0 65536");
    try testing.expectError(error.Unmapped, norm.writeLocation(&w, 0x30_0018));
    try expectLine(&norm, .{ .map = .{ .kind = .bucket, .base = 0x30_0000, .bytes = 0x1_0000 } }, "map b m2 65536");
    try testing.expectError(error.Unmapped, norm.writeLocation(&w, 0x11_0000));
    try testing.expectEqual(@as(u64, 3), norm.maps);
    try testing.expectEqual(@as(u64, 1), norm.unmaps);
}

test "renders every event kind" {
    var norm: Normalizer = .{};
    defer norm.deinit(testing.allocator);
    const base: usize = 0x7f00_0000;
    try expectLine(&norm, .{ .map = .{ .kind = .tree, .base = base, .bytes = 0x2_0000 } }, "map t m0 131072");
    try expectLine(&norm, .{ .page_spawn = .{ .bucket = 2, .page = base + 0xffe0 } }, "page+ b2 m0");
    try expectLine(&norm, .{ .page_release = .{ .bucket = 31, .page = base } }, "page- b31 m0");
    try expectLine(&norm, .{ .page_full = .{ .bucket = 0, .page = base } }, "page-full b0 m0");
    try expectLine(&norm, .{ .page_refill = .{ .bucket = 1, .page = base } }, "page-refill b1 m0");
    try expectLine(&norm, .{ .split = .{ .block = base + 0x20, .size = 1008 } }, "split m0+0x20 1008");
    try expectLine(&norm, .{ .shift = .{ .block = base + 0x40, .offset = 16 } }, "shift m0+0x40 16");
    try expectLine(&norm, .{ .merge = base + 0x1_0000 }, "merge m0+0x10000");
    try expectLine(&norm, .{ .tree_insert = .{ .block = base + 0x20, .size = 300, .kind = .chain, .rotations = 0 } }, "tree+ m0+0x20 300 chain rot=0");
    try expectLine(&norm, .{ .tree_erase = .{ .block = base + 0x20, .size = 300, .kind = .promote, .rotations = 2 } }, "tree- m0+0x20 300 promote rot=2");
    try expectLine(&norm, .{ .list_push = .{ .block = base + 0x30, .size = 48 } }, "list+ m0+0x30 48");
    try expectLine(&norm, .{ .list_erase = .{ .block = base + 0x30, .size = 48 } }, "list- m0+0x30 48");
    try expectLine(&norm, .{ .mr = base + 0x30 }, "mr m0+0x30");
    try expectLine(&norm, .{ .mr = null }, "mr -");
    try testing.expectEqual(@as(u64, 2), norm.rotations);
}
